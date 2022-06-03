"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
// https://en.bitcoin.it/wiki/Secp256k1
const params = {
    a: 0n,
    b: BigInt(7),
    P: 2n ** 256n - 2n ** 32n - 977n,
    n: 2n ** 256n - 432420386565659656852420866394968145599n,
    Gx: 55066263022277343669578718895168534326250603453777594175500187360389116729240n,
    Gy: 32670510020758816978083085130507043184471273380659243275938904335757337482424n
};
exports.default = params;
//# sourceMappingURL=secp256k1.js.map