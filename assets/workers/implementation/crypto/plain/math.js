"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
exports.powMod = exports.invert = exports.addMod = exports.mod = void 0;
const secp256k1_1 = __importDefault(require("./secp256k1"));
const mod = (a, b = secp256k1_1.default.P) => {
    const result = a % b;
    return result >= 0 ? result : b + result;
};
exports.mod = mod;
const addMod = (hash1, hash2) => {
    const a = BigInt(`0x${hash1}`);
    const b = BigInt(`0x${hash2}`);
    return (0, exports.mod)(a + b).toString(16);
};
exports.addMod = addMod;
// Inverses number over modulo
const invert = (number, modulo = secp256k1_1.default.P) => {
    if (number === 0n || modulo <= 0n) {
        throw new Error(`invert: expected positive integers, got n=${number} mod=${modulo}`);
    }
    // Eucledian GCD https://brilliant.org/wiki/extended-euclidean-algorithm/
    let a = (0, exports.mod)(number, modulo);
    let b = modulo;
    let [x, y, u, v] = [0n, 1n, 1n, 0n];
    while (a !== 0n) {
        const q = b / a;
        const r = b % a;
        const m = x - u * q;
        const n = y - v * q;
        [b, a] = [a, r];
        [x, y] = [u, v];
        [u, v] = [m, n];
    }
    const gcd = b;
    if (gcd !== 1n)
        throw new Error('invert: does not exist');
    return (0, exports.mod)(x, modulo);
};
exports.invert = invert;
const powMod = (x, n, p = secp256k1_1.default.P) => {
    if (n === 0n) {
        return 1n;
    }
    // eslint-disable-next-line no-bitwise
    if (n & 1n) {
        return ((0, exports.powMod)(x, n - 1n, p) * x) % p;
    }
    // eslint-disable-next-line no-param-reassign
    x = (0, exports.powMod)(x, n / 2n, p);
    return (x * x) % p;
};
exports.powMod = powMod;
//# sourceMappingURL=math.js.map