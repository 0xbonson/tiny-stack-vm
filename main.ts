import { readdirSync, readFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Machine boundaries
const STACK_MAX = 256;
const CALL_MAX = 64;
const MEM_MAX = 256;
const STEP_LIMIT = 1_000_000;
const OUTPUT_LIMIT = 65_536;

// [opcode, imm_bytes, pop_count, push_count]
const OP_SPECS: [number, number, number, number][] = [
  [0x00,0,0,0],[0x01,1,0,1],[0x02,4,0,1],[0x03,0,1,0],[0x04,0,1,2],[0x05,0,2,2],
  [0x06,0,2,3],[0x07,0,3,3],[0x10,0,2,1],[0x11,0,2,1],[0x12,0,2,1],[0x13,0,2,1],
  [0x14,0,2,1],[0x15,0,2,1],[0x16,0,2,1],[0x17,0,1,1],[0x18,0,2,1],[0x19,0,2,1],
  [0x1a,0,2,1],[0x1b,0,1,1],[0x1c,0,2,1],[0x1d,0,2,1],[0x1e,0,2,1],[0x20,0,2,1],
  [0x21,0,2,1],[0x22,0,2,1],[0x30,2,0,0],[0x31,2,1,0],[0x32,2,1,0],[0x33,2,0,0],
  [0x34,0,0,0],[0x40,0,1,1],[0x41,0,2,0],[0x50,0,1,0],[0x51,0,1,0],[0x52,0,0,1],
  [0x53,0,1,0]
];

// Encoded opcode metadata: (imm << 8) | (pop << 4) | push; -1 = invalid opcode
const OP_TABLE = new Int16Array(256).fill(-1);
for (const [op, imm, pop, push] of OP_SPECS) {
  OP_TABLE[op] = (imm << 8) | (pop << 4) | push;
}

export function executeVM(program: Uint8Array, input: Uint8Array): { stdout: Uint8Array; exit: number } {
  const codeLen = program.length;
  const dstack = new Int32Array(STACK_MAX);
  let sp = 0;
  const cstack = new Int32Array(CALL_MAX);
  let csp = 0;
  const memory = new Int32Array(MEM_MAX);
  const outBuf = new Uint8Array(OUTPUT_LIMIT);
  let outLen = 0;

  let pc = 0;
  let steps = 0;
  let inPos = 0;

  const finish = (code: number) => ({ stdout: outBuf.subarray(0, outLen), exit: code });

  while (true) {
    if (steps === STEP_LIMIT) return finish(10);
    if (pc < 0 || pc >= codeLen) return finish(9);

    const op = program[pc];
    const spec = OP_TABLE[op];
    if (spec < 0) return finish(5);

    const imm = (spec >> 8) & 0xf;
    const pop = (spec >> 4) & 0xf;
    const push = spec & 0xf;

    if (pc + imm >= codeLen) return finish(9);

    steps++;
    const nextPc = pc + 1 + imm;

    if (sp < pop) return finish(2);
    if (sp - pop + push > STACK_MAX) return finish(3);

    pc = nextPc;

    switch (op) {
      case 0x00: return finish(0);
      case 0x01: dstack[sp++] = (program[nextPc - 1] << 24) >> 24; break;
      case 0x02:
        dstack[sp++] = program[nextPc - 4] | (program[nextPc - 3] << 8) | (program[nextPc - 2] << 16) | (program[nextPc - 1] << 24);
        break;
      case 0x03: sp--; break;
      case 0x04: dstack[sp] = dstack[sp - 1]; sp++; break;
      case 0x05: {
        const tmp = dstack[sp - 1];
        dstack[sp - 1] = dstack[sp - 2];
        dstack[sp - 2] = tmp;
        break;
      }
      case 0x06: dstack[sp] = dstack[sp - 2]; sp++; break;
      case 0x07: {
        const a = dstack[sp - 3];
        dstack[sp - 3] = dstack[sp - 2];
        dstack[sp - 2] = dstack[sp - 1];
        dstack[sp - 1] = a;
        break;
      }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        const b = dstack[--sp], a = dstack[sp - 1];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b);
        else if (op === 0x13) { if (b === 0) return finish(4); r = (a === -2147483648 && b === -1) ? a : ((a / b) | 0); }
        else if (op === 0x14) { if (b === 0) return finish(4); r = b === -1 ? 0 : ((a % b) | 0); }
        else if (op === 0x15) { if (b === 0) return finish(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
        else if (op === 0x16) { if (b === 0) return finish(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31);
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0;
        else if (op === 0x22) r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        dstack[sp - 1] = r;
        break;
      }
      case 0x17: dstack[sp - 1] = (-dstack[sp - 1]) | 0; break;
      case 0x1b: dstack[sp - 1] = ~dstack[sp - 1]; break;
      case 0x30:
      case 0x31:
      case 0x32: {
        const offset = ((program[nextPc - 2] | (program[nextPc - 1] << 8)) << 16) >> 16;
        let take = op === 0x30;
        if (op === 0x31) take = dstack[--sp] === 0;
        else if (op === 0x32) take = dstack[--sp] !== 0;
        if (take) pc = nextPc + offset;
        break;
      }
      case 0x33: {
        if (csp === CALL_MAX) return finish(7);
        cstack[csp++] = nextPc;
        pc = program[nextPc - 2] | (program[nextPc - 1] << 8);
        break;
      }
      case 0x34: {
        if (csp === 0) return finish(8);
        pc = cstack[--csp];
        break;
      }
      case 0x40: {
        const addr = dstack[sp - 1];
        if (addr < 0 || addr >= MEM_MAX) return finish(6);
        dstack[sp - 1] = memory[addr];
        break;
      }
      case 0x41: {
        const addr = dstack[sp - 1], val = dstack[sp - 2];
        if (addr < 0 || addr >= MEM_MAX) return finish(6);
        sp -= 2;
        memory[addr] = val;
        break;
      }
      case 0x50: {
        const str = String(dstack[--sp]), len = str.length;
        if (outLen + len > OUTPUT_LIMIT) return finish(11);
        for (let i = 0; i < len; i++) outBuf[outLen++] = str.charCodeAt(i);
        break;
      }
      case 0x51: {
        if (outLen + 1 > OUTPUT_LIMIT) return finish(11);
        outBuf[outLen++] = dstack[--sp] & 255;
        break;
      }
      case 0x52: dstack[sp++] = inPos < input.length ? input[inPos++] : -1; break;
      case 0x53: return finish(dstack[--sp] & 255);
    }
  }
}

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

for (const id of readdirSync(inDir).sort()) {
  const pPath = join(inDir, id, 'program.bin');
  const iPath = join(inDir, id, 'input.bin');
  const prog = readFileSync(pPath);
  const inp = readFileSync(iPath);
  const result = executeVM(prog, inp);

  const destDir = join(outDir, id);
  mkdirSync(destDir, { recursive: true });
  writeFileSync(join(destDir, 'stdout.bin'), result.stdout);
  writeFileSync(join(destDir, 'exit.txt'), `${result.exit}\n`);
}
