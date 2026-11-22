// tinyvm: an implementation of make.fun's tiny stack ISA v1 (kit: generator/subject/ISA.md).
// Reads <in>/<id>/{program.bin,input.bin}; writes <out>/<id>/{stdout.bin,exit.txt} per instance.
import { mkdirSync, readdirSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK_MAX = 256, CALLS_MAX = 64, MEM = 256, STEP_LIMIT = 1e6, OUT_MAX = 65536;
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// Per opcode byte: immediate byte count, pops, pushes (the static stack shape).
const SH = new Uint8Array(768);
for (const [op, im, p, u] of [
  [0x00,0,0,0],[0x01,1,0,1],[0x02,4,0,1],[0x03,0,1,0],[0x04,0,1,2],[0x05,0,2,2],
  [0x06,0,2,3],[0x07,0,3,3],[0x10,0,2,1],[0x11,0,2,1],[0x12,0,2,1],[0x13,0,2,1],
  [0x14,0,2,1],[0x15,0,2,1],[0x16,0,2,1],[0x17,0,1,1],[0x18,0,2,1],[0x19,0,2,1],
  [0x1a,0,2,1],[0x1b,0,1,1],[0x1c,0,2,1],[0x1d,0,2,1],[0x1e,0,2,1],[0x20,0,2,1],
  [0x21,0,2,1],[0x22,0,2,1],[0x30,2,0,0],[0x31,2,1,0],[0x32,2,1,0],[0x33,2,0,0],
  [0x34,0,0,0],[0x40,0,1,1],[0x41,0,2,0],[0x50,0,1,0],[0x51,0,1,0],[0x52,0,0,1],
  [0x53,0,1,0]]) {
  SH[op * 3] = im; SH[op * 3 + 1] = p; SH[op * 3 + 2] = u;
}

// Run one program on one input. Trap order per ISA.md "One step": step limit, pc
// bounds, known opcode, immediate fits, stack shape, then the op's own traps. A
// trapping instruction writes nothing; output written before a trap is kept.
function run(P, input) {
  const n = P.length, D = new Int32Array(STACK_MAX), C = new Int32Array(CALLS_MAX),
    M = new Int32Array(MEM), out = new Uint8Array(OUT_MAX);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const end = (e) => ({ o: out.subarray(0, ol), e });
  // PRINT as decimal ASCII; over the output limit it writes nothing (trap 11).
  const emit = (v) => {
    const s = String(v);
    if (ol + s.length > OUT_MAX) return false;
    for (let k = 0; k < s.length; k++) out[ol++] = s.charCodeAt(k);
    return true;
  };
  for (;;) {
    if (steps === STEP_LIMIT) return end(10);
    if (pc < 0 || pc >= n) return end(9);          // falling off the end is trap 9 too
    const op = P[pc], im = SH[op * 3], p = SH[op * 3 + 1], u = SH[op * 3 + 2];
    if (!im && !p && !u && op !== 0 && op !== 0x34) return end(5); // unknown opcode
    if (pc + im >= n) return end(9);               // immediate cut off by program's end
    steps++;
    const nx = pc + 1 + im;
    if (sp < p) return end(2);                     // stack underflow
    if (sp - p + u > STACK_MAX) return end(3);     // stack overflow
    pc = nx;
    let a, b, v;
    switch (op) {
      case 0x00: return end(0);                    // HALT
      case 0x01: D[sp++] = P[nx - 1] << 24 >> 24; break;            // PUSH8 sign-extends
      case 0x02: D[sp++] = P[nx - 4] | P[nx - 3] << 8 | P[nx - 2] << 16 | P[nx - 1] << 24; break;
      case 0x03: sp--; break;                      // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break;   // DUP: write before sp grows
      case 0x05: v = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = v; break; // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break;   // OVER, same care as DUP
      case 0x07: v = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = v; break; // ROT
      case 0x10: D[sp - 2] = D[sp - 2] + D[sp - 1] | 0; sp--; break; // ADD wraps
      case 0x11: D[sp - 2] = D[sp - 2] - D[sp - 1] | 0; sp--; break; // SUB wraps
      case 0x12: D[sp - 2] = Math.imul(D[sp - 2], D[sp - 1]); sp--; break; // MUL: low 32 bits
      case 0x13: b = D[sp - 1]; a = D[sp - 2]; sp -= 2;              // DIV signed, trunc to 0
        if (!b) return end(4);
        D[sp++] = a === -2147483648 && b === -1 ? a : a / b | 0; break;
      case 0x14: b = D[sp - 1]; a = D[sp - 2]; sp -= 2;              // MOD: sign of a; x%-1=0
        if (!b) return end(4);
        D[sp++] = b === -1 ? 0 : a % b | 0; break;
      case 0x15: b = D[sp - 1]; a = D[sp - 2]; sp -= 2;              // DIVU: operands unsigned
        if (!b) return end(4);
        D[sp++] = (a >>> 0) / (b >>> 0) | 0; break;
      case 0x16: b = D[sp - 1]; a = D[sp - 2]; sp -= 2;              // MODU: unsigned remainder
        if (!b) return end(4);
        D[sp++] = (a >>> 0) % (b >>> 0) | 0; break;
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG wraps
      case 0x18: D[sp - 2] &= D[sp - 1]; sp--; break; // AND
      case 0x19: D[sp - 2] |= D[sp - 1]; sp--; break; // OR
      case 0x1a: D[sp - 2] ^= D[sp - 1]; sp--; break; // XOR
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;     // NOT
      case 0x1c: D[sp - 2] <<= D[sp - 1] & 31; sp--; break; // SHL, count b&31
      case 0x1d: D[sp - 2] >>= D[sp - 1] & 31; sp--; break; // SHR arithmetic
      case 0x1e: D[sp - 2] = D[sp - 2] >>> (D[sp - 1] & 31); sp--; break; // SHRU logical
      case 0x20: D[sp - 2] = D[sp - 2] === D[sp - 1] ? 1 : 0; sp--; break; // EQ
      case 0x21: D[sp - 2] = D[sp - 2] < D[sp - 1] ? 1 : 0; sp--; break;   // LT signed
      case 0x22: D[sp - 2] = (D[sp - 2] >>> 0) < (D[sp - 1] >>> 0) ? 1 : 0; sp--; break; // LTU
      case 0x30: pc = nx + (((P[nx - 2] | P[nx - 1] << 8) << 16) >> 16); break; // JMP rel16
      case 0x31: case 0x32: v = D[--sp];            // JZ / JNZ: pop, then maybe jump
        if (op === 0x31 ? v === 0 : v !== 0) pc = nx + (((P[nx - 2] | P[nx - 1] << 8) << 16) >> 16);
        break;
      case 0x33: if (cp === CALLS_MAX) return end(7); // CALL: unsigned 16-bit target
        C[cp++] = nx; pc = P[nx - 2] | P[nx - 1] << 8; break;
      case 0x34: if (cp === 0) return end(8); pc = C[--cp]; break; // RET
      case 0x40: if (D[sp - 1] < 0 || D[sp - 1] >= MEM) return end(6); // LOAD
        D[sp - 1] = M[D[sp - 1]]; break;
      case 0x41: if (D[sp - 1] < 0 || D[sp - 1] >= MEM) return end(6); // STORE
        M[D[sp - 1]] = D[sp - 2]; sp -= 2; break;
      case 0x50: if (!emit(D[sp - 1])) return end(11); sp--; break;  // PRINT
      case 0x51: if (ol + 1 > OUT_MAX) return end(11);               // PUTC
        out[ol++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < input.length ? input[ip++] : -1; break; // IN, -1 once used up
      case 0x53: return end(D[--sp] & 255);        // EXIT: low byte only
    }
  }
}

for (const id of readdirSync(I).sort()) {
  const src = join(I, id);
  if (!statSync(src).isDirectory()) continue;
  const r = run(readFileSync(join(src, 'program.bin')), readFileSync(join(src, 'input.bin')));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), r.e + '\n');
}
