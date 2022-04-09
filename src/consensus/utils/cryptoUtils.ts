// tslint:disable:variable-name
import BN from 'bn.js';
import { ec as EC } from 'elliptic';

const ec = new EC('secp256k1');

export const pubKeyToPoint = (pubKey) => {
  const pubKeyEven = (pubKey[0] - 0x02) === 0;
  return ec.curve.pointFromX(pubKey.slice(1, 33).toString('hex'), !pubKeyEven);
};

export const pointToPublicKey = (P): Buffer => {
  const buffer = Buffer.allocUnsafe(1);
  // keep sign, if is odd
  buffer.writeUInt8(P.getY().isEven() ? 0x02 : 0x03, 0);
  return Buffer.concat([buffer, P.getX().toArrayLike(Buffer)]);
};

/* X = X1 * a1 + X2 * a2 + ..Xn * an */
export const buildSharedPublicKeyX = (
  publicKeys: string[],
  hash: string
) => {
  let X = null;
  for (const publicKey of publicKeys) {
    const XI = pubKeyToPoint(Buffer.from(publicKey, 'hex')).mul(new BN(hash, 16));
    X = X === null ? XI : X.add(XI);
  }

  return pointToPublicKey(X).toString('hex');
};

/* let s1 = (R1 + k1 * a1 * e) mod n, where n - is a curve param
* the "n" has been introduced to reduce the signature size
* */
export const buildPartialSignature = (
  privateKeyK: string,
  dataHash: string
): string => new BN(privateKeyK, 16)
  .mul(new BN(dataHash, 16))
  .mod(ec.n)
  .toString(16);

/* let s1 * G = k1 * a1 * e * G = k1 * a1 * G * e = X1 * a1 * e */
export const partialSignatureVerify = (
  partialSignature: string,
  publicKey: string,
  hash: string
): boolean => {
  const spG = ec.g.mul(partialSignature);
  const check = pubKeyToPoint(Buffer.from(publicKey, 'hex')).mul(hash);
  return pointToPublicKey(spG).toString('hex') === pointToPublicKey(check).toString('hex');
};

/* s = s1 + s2 + ...sn */
export const buildSharedSignature = (partialSignatures: string[]): string => {
  let signature = new BN(0);

  for (const sig of partialSignatures) {
    signature = signature.add(new BN(sig, 16));
  }

  return signature.toString(16);
};

/* sG = X * e */
export const verify = (
  signature: string,
  sharedPublicKeyX: string
): boolean => {
  const sg = ec.g.mul(signature);
  const check = pubKeyToPoint(Buffer.from(sharedPublicKeyX, 'hex'));
  return pointToPublicKey(sg).toString('hex') === pointToPublicKey(check).toString('hex');
};
