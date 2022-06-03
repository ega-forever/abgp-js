"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || function (mod) {
    if (mod && mod.__esModule) return mod;
    var result = {};
    if (mod != null) for (var k in mod) if (k !== "default" && Object.prototype.hasOwnProperty.call(mod, k)) __createBinding(result, mod, k);
    __setModuleDefault(result, mod);
    return result;
};
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
/* eslint-disable import/no-extraneous-dependencies */
const crypto = __importStar(require("crypto"));
const elliptic_1 = require("elliptic");
const bn_js_1 = __importDefault(require("bn.js"));
const ec = new elliptic_1.ec('secp256k1');
class CryptoMath {
    addMod(hash1, hash2) {
        return new bn_js_1.default(hash1, 16).add(new bn_js_1.default(hash2, 16)).mod(ec.n).toString(16);
    }
    ;
}
class Bnelliptic {
    constructor() {
        this.math = new CryptoMath();
    }
    async generatePrivateKey() {
        const node = crypto.createECDH('secp256k1');
        node.generateKeys();
        return node.getPrivateKey().toString('hex');
    }
    async getPublicKey(privateKeyHex) {
        const pg = ec.g.mul(privateKeyHex);
        return this.pointToPublicKey(pg).toString('hex');
    }
    async buildPartialSignature(privateKeyK, dataHash) {
        return new bn_js_1.default(privateKeyK, 16)
            .mul(new bn_js_1.default(dataHash, 16))
            .mod(ec.n)
            .toString(16);
    }
    async buildSharedPublicKeyX(publicKeys, hash) {
        let X = null;
        for (const publicKey of publicKeys) {
            const XI = this.pubKeyToPoint(Buffer.from(publicKey, 'hex')).mul(new bn_js_1.default(hash, 16));
            X = X === null ? XI : X.add(XI);
        }
        return this.pointToPublicKey(X).toString('hex');
    }
    async buildSharedSignature(partialSignatures) {
        let signature = new bn_js_1.default(0);
        for (const sig of partialSignatures) {
            signature = signature.add(new bn_js_1.default(sig, 16));
        }
        return signature.toString(16);
    }
    async partialSignatureVerify(partialSignature, publicKeyHex, hash) {
        const spG = ec.g.mul(partialSignature);
        const check = this.pubKeyToPoint(Buffer.from(publicKeyHex, 'hex')).mul(hash);
        return this.pointToPublicKey(spG).toString('hex') === this.pointToPublicKey(check).toString('hex');
    }
    async verify(signature, sharedPublicKeyX) {
        const sg = ec.g.mul(signature);
        const check = this.pubKeyToPoint(Buffer.from(sharedPublicKeyX, 'hex'));
        return this.pointToPublicKey(sg).toString('hex') === this.pointToPublicKey(check).toString('hex');
    }
    hash(message) {
        return crypto.createHash('sha256')
            .update(message)
            .digest('hex');
    }
    pubKeyToPoint(pubKey) {
        const pubKeyEven = (pubKey[0] - 0x02) === 0;
        return ec.curve.pointFromX(pubKey.slice(1, 33).toString('hex'), !pubKeyEven);
    }
    pointToPublicKey(P) {
        const buffer = Buffer.allocUnsafe(1);
        // keep sign, if is odd
        buffer.writeUInt8(P.getY().isEven() ? 0x02 : 0x03, 0);
        return Buffer.concat([buffer, P.getX().toArrayLike(Buffer)]);
    }
}
exports.default = Bnelliptic;
//# sourceMappingURL=index.js.map