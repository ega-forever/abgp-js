/* eslint-disable import/no-extraneous-dependencies */
import * as crypto from 'crypto';
import { ec as EC } from 'elliptic';
import BN from 'bn.js';
import ICryptoInterface, { ICryptoMathInterface } from 'abgp-js/src/consensus/interfaces/ICryptoInterface';

const ec = new EC('secp256k1');

class CryptoMath implements ICryptoMathInterface {
  addMod(hash1: string, hash2: string): string {
    return new BN(hash1, 16).add(new BN(hash2, 16)).mod(ec.n).toString(16);
  };
}

export default class implements ICryptoInterface {
  public math: ICryptoMathInterface;

  public constructor() {
    this.math = new CryptoMath();
  }

  public async generatePrivateKey(): Promise<string> {
    const node = crypto.createECDH('secp256k1');
    node.generateKeys();
    return node.getPrivateKey().toString('hex');
  }

  public async getPublicKey(privateKeyHex: string): Promise<string> {
    const pg = ec.g.mul(privateKeyHex);
    return this.pointToPublicKey(pg).toString('hex');
  }

  public async buildPartialSignature(privateKeyK: string, dataHash: string): Promise<string> {
    return new BN(privateKeyK, 16)
      .mul(new BN(dataHash, 16))
      .mod(ec.n)
      .toString(16);
  }

  public async buildSharedPublicKeyX(publicKeys: string[], hash: string): Promise<string> {
    let X = null;
    for (const publicKey of publicKeys) {
      const XI = this.pubKeyToPoint(Buffer.from(publicKey, 'hex')).mul(new BN(hash, 16));
      X = X === null ? XI : X.add(XI);
    }

    return this.pointToPublicKey(X).toString('hex');
  }

  public async buildSharedSignature(partialSignatures: string[]): Promise<string> {
    let signature = new BN(0);

    for (const sig of partialSignatures) {
      signature = signature.add(new BN(sig, 16));
    }

    return signature.toString(16);
  }

  public async partialSignatureVerify(partialSignature: string, publicKeyHex: string, hash: string): Promise<boolean> {
    const spG = ec.g.mul(partialSignature);
    const check = this.pubKeyToPoint(Buffer.from(publicKeyHex, 'hex')).mul(hash);
    return this.pointToPublicKey(spG).toString('hex') === this.pointToPublicKey(check).toString('hex');
  }

  public async verify(signature: string, sharedPublicKeyX: string): Promise<boolean> {
    const sg = ec.g.mul(signature);
    const check = this.pubKeyToPoint(Buffer.from(sharedPublicKeyX, 'hex'));
    return this.pointToPublicKey(sg).toString('hex') === this.pointToPublicKey(check).toString('hex');
  }

  public hash(message: string): string {
    return crypto.createHash('sha256')
      .update(message)
      .digest('hex');
  }

  private pubKeyToPoint(pubKey) {
    const pubKeyEven = (pubKey[0] - 0x02) === 0;
    return ec.curve.pointFromX(pubKey.slice(1, 33).toString('hex'), !pubKeyEven);
  }

  private pointToPublicKey(P): Buffer {
    const buffer = Buffer.allocUnsafe(1);
    // keep sign, if is odd
    buffer.writeUInt8(P.getY().isEven() ? 0x02 : 0x03, 0);
    return Buffer.concat([buffer, P.getX().toArrayLike(Buffer)]);
  }
}
