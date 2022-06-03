"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const crypto_1 = require("crypto");
const Point_1 = __importDefault(require("./Point"));
const secp256k1_1 = __importDefault(require("./secp256k1"));
const math_1 = require("./math");
const JacobianPoint_1 = __importDefault(require("./JacobianPoint"));
class CryptoMath {
    addMod(hash1, hash2) {
        return (0, math_1.addMod)(hash1, hash2);
    }
    ;
}
class Crypto {
    constructor() {
        this.G = JacobianPoint_1.default.fromAffine(new Point_1.default(secp256k1_1.default.Gx, secp256k1_1.default.Gy));
        this.math = new CryptoMath();
    }
    async generatePrivateKey() {
        const privateKey = BigInt(`0x${(0, crypto_1.randomBytes)(64).toString('hex')}`) % secp256k1_1.default.P;
        const publicKey = this.G.multiplyPrecomputes(privateKey).toAffine();
        const publicKeyRestored = this.pubKeyToPoint(this.pointToPublicKey(publicKey));
        if (publicKey.x !== publicKeyRestored.x || publicKey.y !== publicKeyRestored.y) {
            return this.generatePrivateKey();
        }
        return privateKey.toString(16);
    }
    async getPublicKey(privateKeyHex) {
        const privKey = BigInt(`0x${privateKeyHex}`);
        const publicKey = this.G.multiplyPrecomputes(privKey).toAffine();
        return this.pointToPublicKey(publicKey);
    }
    /* X = X1 * a1 + X2 * a2 + ..Xn * an */
    async buildSharedPublicKeyX(publicKeys, hash) {
        let X = null;
        for (const publicKey of publicKeys) {
            const XI = JacobianPoint_1.default.fromAffine(this.pubKeyToPoint(publicKey));
            X = X === null ? XI : X.add(XI);
        }
        X = X.multiply(BigInt(`0x${hash}`)).toAffine();
        return this.pointToPublicKey(X);
    }
    /* let s1 = (R1 + k1 * a1 * e) mod n, where n - is a curve param
    * the "n" has been introduced to reduce the signature size
    * */
    async buildPartialSignature(privateKeyK, dataHash) {
        const hash = BigInt(`0x${dataHash}`);
        const privateKey = BigInt(`0x${privateKeyK}`);
        const signature = (privateKey * hash) % secp256k1_1.default.n;
        return signature.toString(16);
    }
    /* s = s1 + s2 + ...sn */
    async buildSharedSignature(partialSignatures) {
        let signature = 0n;
        for (const sig of partialSignatures) {
            signature = (signature + BigInt(`0x${sig}`)) % secp256k1_1.default.n;
        }
        return signature.toString(16);
    }
    /* let s1 * G = k1 * a1 * e * G = k1 * a1 * G * e = X1 * a1 * e */
    async partialSignatureVerify(partialSignature, publicKeyHex, hash) {
        const signature = BigInt(`0x${partialSignature}`);
        const publicKey = JacobianPoint_1.default.fromAffine(this.pubKeyToPoint(publicKeyHex));
        const m = BigInt(`0x${hash}`);
        const spg = this.G.multiplyPrecomputes(signature).toAffine();
        const check = publicKey.multiply(m).toAffine();
        return spg.x === check.x && spg.y === check.y;
    }
    /* sG = X * e */
    async verify(signature, sharedPublicKeyX) {
        const sg = this.G.multiplyPrecomputes(BigInt(`0x${signature}`)).toAffine();
        const check = this.pubKeyToPoint(sharedPublicKeyX);
        return sg.x === check.x;
    }
    hash(message) {
        return (0, crypto_1.createHash)('sha256')
            .update(message)
            .digest('hex');
    }
    pubKeyToPoint(pubKeyHex) {
        const yShouldBeOdd = pubKeyHex.substring(0, 2) === '03';
        const x = BigInt(`0x${pubKeyHex.substring(2)}`);
        const y2 = ((0, math_1.powMod)(x, 3n) + secp256k1_1.default.b) % secp256k1_1.default.P;
        let y = (0, math_1.powMod)(y2, (secp256k1_1.default.P + 1n) / 4n);
        const tempIsOdd = y.toString(2)[0] === '0';
        if (tempIsOdd !== yShouldBeOdd) {
            y = secp256k1_1.default.P - y;
        }
        return new Point_1.default(x, y);
    }
    ;
    pointToPublicKey(P) {
        // eslint-disable-next-line no-bitwise
        const prefix = P.y & 1n ? '03' : '02'; // is odd
        return `${prefix}${P.x.toString(16)}`;
    }
    ;
}
exports.default = Crypto;
//# sourceMappingURL=index.js.map