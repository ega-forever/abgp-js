import { randomBytes, createHash } from 'crypto';
// eslint-disable-next-line import/no-extraneous-dependencies
import ICryptoInterface, { ICryptoMathInterface } from 'abgp-js/dist/consensus/interfaces/ICryptoInterface';
import Point from './Point';
import curveParams from './secp256k1';
import { addMod, powMod } from './math';
import JacobianPoint from './JacobianPoint';

class CryptoMath implements ICryptoMathInterface {
  addMod(hash1: string, hash2: string): string {
    return addMod(hash1, hash2);
  };
}

export default class Crypto implements ICryptoInterface {
  private readonly G: JacobianPoint;

  public math: ICryptoMathInterface;

  public constructor() {
    this.G = JacobianPoint.fromAffine(new Point(curveParams.Gx, curveParams.Gy));
    this.math = new CryptoMath();
  }

  public async generatePrivateKey(): Promise<string> {
    const privateKey = BigInt(`0x${randomBytes(64).toString('hex')}`) % curveParams.P;
    const publicKey = this.G.multiplyPrecomputes(privateKey).toAffine();
    const publicKeyRestored = this.pubKeyToPoint(this.pointToPublicKey(publicKey));

    if (publicKey.x !== publicKeyRestored.x || publicKey.y !== publicKeyRestored.y) {
      return this.generatePrivateKey();
    }

    return privateKey.toString(16);
  }

  public async getPublicKey(privateKeyHex: string): Promise<string> {
    const privKey = BigInt(`0x${privateKeyHex}`);
    const publicKey = this.G.multiplyPrecomputes(privKey).toAffine();
    return this.pointToPublicKey(publicKey);
  }

  /* X = X1 * a1 + X2 * a2 + ..Xn * an */
  public async buildSharedPublicKeyX(publicKeys: string[], hash: string): Promise<string> {
    let X = null;
    for (const publicKey of publicKeys) {
      const XI = JacobianPoint.fromAffine(this.pubKeyToPoint(publicKey));
      X = X === null ? XI : X.add(XI);
    }
    X = X.multiply(BigInt(`0x${hash}`)).toAffine();
    return this.pointToPublicKey(X);
  }

  /* let s1 = (R1 + k1 * a1 * e) mod n, where n - is a curve param
  * the "n" has been introduced to reduce the signature size
  * */
  public async buildPartialSignature(privateKeyK: string, dataHash: string): Promise<string> {
    const hash = BigInt(`0x${dataHash}`);
    const privateKey = BigInt(`0x${privateKeyK}`);
    const signature = (privateKey * hash) % curveParams.n;
    return signature.toString(16);
  }

  /* s = s1 + s2 + ...sn */
  public async buildSharedSignature(partialSignatures: string[]): Promise<string> {
    let signature = 0n;

    for (const sig of partialSignatures) {
      signature = (signature + BigInt(`0x${sig}`)) % curveParams.n;
    }

    return signature.toString(16);
  }

  /* let s1 * G = k1 * a1 * e * G = k1 * a1 * G * e = X1 * a1 * e */
  public async partialSignatureVerify(partialSignature: string, publicKeyHex: string, hash: string): Promise<boolean> {
    const signature = BigInt(`0x${partialSignature}`);
    const publicKey = JacobianPoint.fromAffine(this.pubKeyToPoint(publicKeyHex));
    const m = BigInt(`0x${hash}`);

    const spg = this.G.multiplyPrecomputes(signature).toAffine();
    const check = publicKey.multiply(m).toAffine();
    return spg.x === check.x && spg.y === check.y;
  }

  /* sG = X * e */
  public async verify(signature: string, sharedPublicKeyX: string): Promise<boolean> {
    const sg = this.G.multiplyPrecomputes(BigInt(`0x${signature}`)).toAffine();
    const check = this.pubKeyToPoint(sharedPublicKeyX);
    return sg.x === check.x;
  }

  public hash(message: string): string {
    return createHash('sha256')
      .update(message)
      .digest('hex');
  }

  private pubKeyToPoint(pubKeyHex: string): Point {
    const yShouldBeOdd = pubKeyHex.substring(0, 2) === '03';
    const x = BigInt(`0x${pubKeyHex.substring(2)}`);

    const y2 = (powMod(x, 3n) + curveParams.b) % curveParams.P;
    let y = powMod(y2, (curveParams.P + 1n) / 4n);

    const tempIsOdd = y.toString(2)[0] === '0';
    if (tempIsOdd !== yShouldBeOdd) {
      y = curveParams.P - y;
    }

    return new Point(x, y);
  };

  private pointToPublicKey(P: Point | JacobianPoint): string {
    // eslint-disable-next-line no-bitwise
    const prefix = P.y & 1n ? '03' : '02'; // is odd
    return `${prefix}${P.x.toString(16)}`;
  };
}
