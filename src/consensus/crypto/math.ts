import curveParams from './secp256k1';

export const mod = (a: bigint, b: bigint = curveParams.P): bigint => {
  const result = a % b;
  return result >= 0 ? result : b + result;
};

// Inverses number over modulo
export const invert = (number: bigint, modulo: bigint = curveParams.P): bigint => {
  if (number === 0n || modulo <= 0n) {
    throw new Error(`invert: expected positive integers, got n=${number} mod=${modulo}`);
  }
  // Eucledian GCD https://brilliant.org/wiki/extended-euclidean-algorithm/
  let a = mod(number, modulo);
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
  if (gcd !== 1n) throw new Error('invert: does not exist');
  return mod(x, modulo);
};

export const powMod = (x: bigint, n: bigint, p: bigint = curveParams.P): bigint => {
  if (n === 0n) {
    return 1n;
  }
  // eslint-disable-next-line no-bitwise
  if (n & 1n) {
    return (powMod(x, n - 1n, p) * x) % p;
  }
  // eslint-disable-next-line no-param-reassign
  x = powMod(x, n / 2n, p);
  return (x * x) % p;
};
