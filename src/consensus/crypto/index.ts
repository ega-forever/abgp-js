import crypto from 'crypto';
import Point from './Point';
import curveParams from './secp256k1';
import { powMod } from './math';

export const G = new Point(curveParams.Gx, curveParams.Gy);

export const generatePrivateKey = (): string => {
  const privateKey = BigInt(`0x${crypto.randomBytes(64).toString('hex')}`) % curveParams.P;
  const publicKey = G.multiplyCTJ(privateKey);
  const publicKeyRestored = pubKeyToPoint(pointToPublicKey(publicKey));

  if (publicKey.x !== publicKeyRestored.x || publicKey.y !== publicKeyRestored.y) {
    return generatePrivateKey();
  }

  return privateKey.toString(16);
};

export const getPublicKey = (privKeyHex: string): string => {
  const privKey = BigInt(`0x${privKeyHex}`);
  const publicKey = G.multiplyCTJ(privKey);
  // eslint-disable-next-line no-use-before-define
  return pointToPublicKey(publicKey);
};

export const pubKeyToPoint = (pubKeyHex: string) => {
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

export const pointToPublicKey = (P: Point): string => {
  // eslint-disable-next-line no-bitwise
  const prefix = P.y & 1n ? '03' : '02'; // is odd
  return `${prefix}${P.x.toString(16)}`;
};

/* X = X1 * a1 + X2 * a2 + ..Xn * an */
export const buildSharedPublicKeyX = (
  publicKeys: string[],
  hash: string
) => {
  let X = null;
  for (const publicKey of publicKeys) {
    const XI = pubKeyToPoint(publicKey).multiplyCTJ(BigInt(`0x${hash}`));
    X = X === null ? XI : X.add(XI);
  }

  return pointToPublicKey(X);
};

/* let s1 = (R1 + k1 * a1 * e) mod n, where n - is a curve param
* the "n" has been introduced to reduce the signature size
* */
export const buildPartialSignature = (
  privateKeyK: string,
  dataHash: string
): string => {
  const hash = BigInt(`0x${dataHash}`);
  const privateKey = BigInt(`0x${privateKeyK}`);
  const signature = (BigInt(privateKey) * hash) % curveParams.n;
  return signature.toString(16);
};

/* let s1 * G = k1 * a1 * e * G = k1 * a1 * G * e = X1 * a1 * e */
export const partialSignatureVerify = (
  partialSignature: string,
  publicKeyHex: string,
  hash: string
): boolean => {
  const signature = BigInt(`0x${partialSignature}`);
  const publicKey = pubKeyToPoint(publicKeyHex);
  const m = BigInt(`0x${hash}`);

  const spg = G.multiplyCTJ(signature);
  const check = publicKey.multiplyCTJ(m);
  return spg.x === check.x && spg.y === check.y;
};

/* s = s1 + s2 + ...sn */
export const buildSharedSignature = (partialSignatures: string[]): string => {
  let signature = 0n;

  for (const sig of partialSignatures) {
    signature = (signature + BigInt(`0x${sig}`)) % curveParams.n;
  }

  return signature.toString(16);
};

/* sG = X * e */
export const verify = (
  signature: string,
  sharedPublicKeyX: string
): boolean => {
  const sg = G.multiplyCTJ(BigInt(`0x${signature}`));
  const check = pubKeyToPoint(sharedPublicKeyX);
  return sg.x === check.x;
};
