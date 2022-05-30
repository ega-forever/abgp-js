// @ts-ignore
// eslint-disable-next-line import/no-import-module-exports
import crypto from 'crypto';
import curveParams from './src/consensus/crypto/secp256k1';

const CURVE = {
  P: 2n ** 256n - 2n ** 32n - 977n,
  n: 2n ** 256n - 432420386565659656852420866394968145599n,
  Gx: 55066263022277343669578718895168534326250603453777594175500187360389116729240n,
  Gy: 32670510020758816978083085130507043184471273380659243275938904335757337482424n
};

class Point {
  static ZERO = new Point(0n, 0n); // Point at infinity aka identity point aka zero

  public readonly x: bigint;

  public readonly y: bigint;

  private precomputes;

  constructor(x: bigint, y: bigint) {
    this.x = x;
    this.y = y;
  }

  // Adds point to itself. http://hyperelliptic.org/EFD/g1p/auto-shortw.html
  double(): Point {
    const X1 = this.x;
    const Y1 = this.y;
    const lam = mod(3n * X1 ** 2n * invert(2n * Y1, CURVE.P));
    const X3 = mod(lam * lam - 2n * X1);
    const Y3 = mod(lam * (X1 - X3) - Y1);
    return new Point(X3, Y3);
  }

  // Adds point to other point. http://hyperelliptic.org/EFD/g1p/auto-shortw.html
  add(other: Point): Point {
    const [a, b] = [this, other];
    const [X1, Y1, X2, Y2] = [a.x, a.y, b.x, b.y];
    if (X1 === 0n || Y1 === 0n) return b;
    if (X2 === 0n || Y2 === 0n) return a;
    if (X1 === X2 && Y1 === Y2) return this.double();
    if (X1 === X2 && Y1 === -Y2) return Point.ZERO;
    const lam = mod((Y2 - Y1) * invert(X2 - X1, CURVE.P));
    const X3 = mod(lam * lam - X1 - X2);
    const Y3 = mod(lam * (X1 - X3) - Y1);
    return new Point(X3, Y3);
  }

  multiplyCT(n: bigint) {
    const dbls = this.getPrecomputes();
    let p = Point.ZERO;
    let f = Point.ZERO; // fake point
    for (let i = 0; i < 256; i++) {
      if (n & 1n) {
        p = p.add(dbls[i]);
      } else {
        f = f.add(dbls[i]);
      }
      n >>= 1n;
    }
    return p;
  }

  getPrecomputes() {
    if (this.precomputes) {
      return this.precomputes;
    }
    this.precomputes = [];
    let dbl: Point = this;
    for (let i = 0; i < 256; i++) {
      this.precomputes.push(dbl);
      dbl = dbl.double(); // [G, 2G, 4G, 8G..., 256G], optimized
    }

    return this.precomputes;
  }

  getPrecomputesJ() {
    if (this.precomputes) {
      return this.precomputes;
    }
    this.precomputes = [];

    let dbl = JacobianPoint.fromAffine(this);
    for (let i = 0; i < 256; i++) {
      this.precomputes.push(dbl);
      dbl = dbl.double(); // [G, 2G, 4G, 8G..., 256G], optimized
    }

    return this.precomputes;
  }

  multiplyCTJ(n: bigint) {
    const precomputes = this.getPrecomputesJ();
    let p = JacobianPoint.ZERO;
    let f = JacobianPoint.ZERO; // fake point
    for (let i = 0; i < 256; i++) {
      if (n & 1n) {
        p = p.add(precomputes[i]);
      } else {
        f = f.add(precomputes[i]);
      }
      n >>= 1n;
    }
    return p.toAffine();
  }
}

class JacobianPoint {
  static ZERO = new JacobianPoint(0n, 1n, 0n);

  public x: bigint;

  public y: bigint;

  public z: bigint;

  constructor(x: bigint, y: bigint, z: bigint) {
    this.x = x;
    this.y = y;
    this.z = z;
  }

  static fromAffine(p: Point): JacobianPoint {
    return new JacobianPoint(p.x, p.y, 1n);
  }

  // http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
  double(): JacobianPoint {
    const X1 = this.x;
    const Y1 = this.y;
    const Z1 = this.z;

    const A = mod(X1 ** 2n);
    const B = mod(Y1 ** 2n);
    const C = mod(B ** 2n);
    const D = mod(2n * (mod((X1 + B) ** 2n) - A - C));
    const E = mod(3n * A);
    const F = mod(E ** 2n);
    const X3 = mod(F - 2n * D);
    const Y3 = mod(E * (D - X3) - 8n * C);
    const Z3 = mod(2n * Y1 * Z1);

    return new JacobianPoint(X3, Y3, Z3);
  }

  // http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-1998-cmo-2
  add(other: JacobianPoint): JacobianPoint {
    const [a, b] = [this, other];
    const [X1, Y1, X2, Y2, Z1, Z2] = [a.x, a.y, b.x, b.y, a.z, b.z];

    if (X1 === 0n || Y1 === 0n) return b;
    if (X2 === 0n || Y2 === 0n) return a;

    const Z1Z1 = mod(Z1 ** 2n);
    const Z2Z2 = mod(Z2 ** 2n);
    const U1 = mod(X1 * Z2Z2);
    const U2 = mod(X2 * Z1Z1);
    const S1 = mod(mod(Y1 * Z2) * Z2Z2);
    const S2 = mod(mod(Y2 * Z1) * Z1Z1);
    const H = mod(U2 - U1);
    const r = mod(S2 - S1);
    // H = 0 meaning it's the same point.
    if (H === 0n) {
      return r === 0n ? this.double() : JacobianPoint.ZERO;
    }
    const HH = mod(H ** 2n);
    const HHH = mod(H * HH);
    const V = mod(U1 * HH);
    const X3 = mod(r ** 2n - HHH - 2n * V);
    const Y3 = mod(r * (V - X3) - S1 * HHH);
    const Z3 = mod(Z1 * Z2 * H);
    return new JacobianPoint(X3, Y3, Z3);

    /*    const Z1Z1 = Z1 ** 2n;
        const Z2Z2 = Z2 ** 2n;
        const U1 = X1 * Z2Z2;
        const U2 = X2 * Z1Z1;
        const S1 = Y1 * Z2 * Z2Z2;
        const S2 = Y2 * Z1 * Z1Z1;
        const H = U2 - U1;
        const HH = H ** 2n;
        const HHH = H * HH;
        const r = S2 - S1;
        const V = U1 * HH;
        const X3 = mod(r ** 2n - HHH - 2n * V);
        const Y3 = mod(r * (V - X3) - S1 * HHH);
        const Z3 = mod(Z1 * Z2 * H);

        return new JacobianPoint(X3, Y3, Z3); */
  }

  toAffine(invZ?: bigint): Point {
    const { x, y, z } = this;
    const iz1 = invZ || invert(this.z);
    const iz2 = mod(iz1 * iz1);
    const iz3 = mod(iz2 * iz1);
    const ax = mod(x * iz2);
    const ay = mod(y * iz3);
    const zz = mod(z * iz1);
    if (zz !== 1n) throw new Error('invZ was invalid');
    return new Point(ax, ay);
  }
}

const G = new Point(CURVE.Gx, CURVE.Gy);

function mod(a: bigint, b: bigint = CURVE.P): bigint {
  const result = a % b;
  return result >= 0 ? result : b + result;
}

// Inverses number over modulo
function invert(number: bigint, modulo: bigint = CURVE.P): bigint {
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
}

function getPublicKey(privKey: bigint) {
  return G.multiplyCTJ(privKey);
}

function sign(m: bigint, privateKey: bigint) {
  /*
  sign(m, d, k) where
  m = message to sign and h(m) is its hash converted to number
  d = private key converted to number
  k = random number
  (x1, y1) = G × k
  r = x1 mod n
  s = (k**-1 * (h(m) + d * r) mod n
   */
  const randomNumber = mod(BigInt(`0x${crypto.randomBytes(64).toString('hex')}`));
  const { x: x1 } = G.multiplyCTJ(randomNumber);
  const r = mod(x1, CURVE.n);
  const s = mod((invert(randomNumber, CURVE.n) * (m + privateKey * r)), CURVE.n);
  return {
    r, s
  };
}

function verify(r: bigint, s: bigint, m: bigint, publicKey: Point) {
  /*
  verify(r, s, m, Q) where
    r, s = outputs from sign()
    m = message to sign
    h(m) message hash converted to number
    Q = public key for private key d which signed m
  w = s**-1 mod n
  u1 = h(m)*w mod n
  u2 = rw mod n
  (x2, y2) = G × u1 + Q × u2
  x2 == r
   */

  const w = mod(invert(s, CURVE.n));
  const u1 = mod(m * w, CURVE.n);
  const u2 = mod(r * w, CURVE.n);
  const { x: x2 } = G.multiplyCTJ(u1).add(publicKey.multiplyCTJ(u2));
  return x2 === r;
}

function pow2(x: bigint, power: bigint): bigint {
  const { P } = CURVE;
  let res = x;
  // eslint-disable-next-line no-param-reassign
  while (power-- > 0n) {
    res = (res * res) % P;
  }
  return res;
}

// Used to calculate y - the square root of y².
// Exponentiates it to very big number (P+1)/4.
// We are unwrapping the loop because it's 2x faster.
// (P+1n/4n).toString(2) would produce bits [223x 1, 0, 22x 1, 4x 0, 11, 00]
// We are multiplying it bit-by-bit
function sqrtMod(x: bigint): bigint {
  const { P } = CURVE;
  const b2 = (x * x * x) % P; // x^3, 11
  const b3 = (b2 * b2 * x) % P; // x ** 7
  const b6 = (pow2(b3, 3n) * b3) % P; // x ** 7 ** 2 ** 3 * 3
  const b9 = (pow2(b6, 3n) * b3) % P; // x^
  const b11 = (pow2(b9, 2n) * b2) % P; // x^
  const b22 = (pow2(b11, 11n) * b11) % P; // x^
  const b44 = (pow2(b22, 22n) * b22) % P; // x^
  const b88 = (pow2(b44, 44n) * b44) % P; // x^
  const b176 = (pow2(b88, 88n) * b88) % P; // x^
  const b220 = (pow2(b176, 44n) * b44) % P; // x^
  const b223 = (pow2(b220, 3n) * b3) % P; // x^
  const t1 = (pow2(b223, 23n) * b22) % P; // x^
  const t2 = (pow2(t1, 6n) * b2) % P; // x^
  return pow2(t2, 2n);
}

/*
const sqrtModC = (val: bigint, k: bigint = 2n) => {
  let o = 0n; // old approx value
  let x = val;

  while (x ** k !== k && x !== o) {
    o = x;
    x = ((k - 1n) * x + val / x ** (k - 1n)) / k;
  }

  return x;
};
*/

/*
const sqrtModB = (n, p) => {
  const powerMod = (base: bigint, exponent: bigint, modulus: bigint) => {
    let result = 1n;
    // eslint-disable-next-line no-param-reassign
    base %= modulus;
    while (exponent > 0) {
      if (exponent % 2n === 1n) {
        result = (result * base) % modulus;
      }

      // eslint-disable-next-line no-bitwise,no-param-reassign
      exponent >>= 1n;
      // eslint-disable-next-line no-param-reassign
      base = (base * base) % modulus;
    }
    return result;
  };

  const gcd = (a: bigint, b: bigint) => (b === 0n ? a : gcd(b, a % b));

  const orderValues = (p: bigint, b: bigint) => {
    if (gcd(p, b) !== 1n) {
      return -1n;
    }
    let k = 3n;
    while (powerMod(b, k, p) !== 1n) {
      k++;
    }
    return k;
  };

  const findx2e = (x: bigint) => {
    let e = 0n;
    while (x % 2n === 0n) {
      // eslint-disable-next-line no-param-reassign
      x /= 2n;
      e++;
      // eslint-disable-next-line no-unused-vars
    }
    return { s: x, e };
  };

  const calcSquareRoot = (n: bigint, p: bigint) => {
    if (gcd(n, p) !== 1n) {
      return -1n;
    }
    if (powerMod(n, (p - 1n) / 2n, p) === (p - 1n)) {
      return -1n;
    }

    const { s, e } = findx2e(p - 1n);
    let q = 2n;

    while (powerMod(q, (p - 1n) / 2n, p) !== (p - 1n)) {
      q++;
    }

    let x = powerMod(n, (s + 1n) / 2n, p);
    let b = powerMod(n, s, p);
    let g = powerMod(q, s, p);
    let r: bigint = e;
    while (1) {
      let m: bigint;
      for (m = 0n; m < r; m++) {
        console.log('!!');
        if (orderValues(p, b) === -1n) return -1n;
        if (orderValues(p, b) === 2n ** m) break;
      }
      if (m === 0n) return x;

      let exp;
      const expCoef = r - m - 1n;

      if (expCoef < 0) {
        console.log('---0')
        exp = invert(2n ** (-expCoef));
      } else {
        console.log('---1')
        exp = 2n ** expCoef;
      }

      x = (x * powerMod(g, exp, p)) % p;
      g = powerMod(g, 2n ** (r - m), p);
      b = (b * g) % p;
      if (b === 1n) return x;
      r = m;
    }
  };

  return calcSquareRoot(n, p);
};
*/

const powMod = (x: bigint, n: bigint, p: bigint = CURVE.P): bigint => {
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

/*
const sqrtModB = (n: bigint, p: bigint = CURVE.P): bigint => {
  /!* Takes as input an odd prime p and n < p and returns r
   * such that r * r = n [mod p]. *!/
  let s = 0n;
  let q: bigint = p - 1n;
  // eslint-disable-next-line no-bitwise
  while ((q & 1n) === 0n) {
    q /= 2n;
    ++s;
  }
  if (s === 1n) {
    const r = powMod(n, (p + 1n) / 4n);

    if ((r * r) % p === n) return r;
    return 0n;
  }
  // Find the first quadratic non-residue z by brute-force search
  let z = 1n;
  while (powMod(z, (p - 1n) / 2n) !== p - 1n) {
    z++;
  }
  let c = powMod(z, q);
  let r = powMod(n, (q + 1n) / 2n);
  let t = powMod(n, q);
  let m = s;
  while (t !== 1n) {
    let tt = t;
    let i = 0n;
    while (tt !== 1n) {
      tt = (tt * tt) % p;
      ++i;
      if (i === m) return 0n;
    }
    const b = powMod(c, powMod(2n, m - i - 1n));
    const b2 = (b * b) % p;
    r = (r * b) % p;
    t = (t * b2) % p;
    c = b2;
    m = i;
  }
  if ((r * r) % p === n) return r;
  return 0n;
};
*/


const restoreY = (x: bigint, yShouldBeOdd: boolean) => {
  // Check array length and type indicator byte
  console.log(Buffer.from(x.toString(16), 'hex').length);
  const y2 = (powMod(x, 3n) + curveParams.b) % curveParams.P;
  let y = powMod(y2, (curveParams.P + 1n) / 4n);

  const tempIsOdd = y.toString(2)[0] === '0';
  if (tempIsOdd !== yShouldBeOdd) {
    y = curveParams.P - y;
  }

  return y;
}


// Given x, this returns a value y such that y^2 % MODULUS == x.
const sqrtMod2 = (x: bigint) => {
  const pow = (curveParams.P + 1n) >> 2n;
  return powMod(x, pow);
}


const init = async () => {
  const node = crypto.createECDH('secp256k1');
  node.generateKeys();
  const privateKey = BigInt(`0x${node.getPrivateKey().toString('hex')}`);
  const publicKey = getPublicKey(privateKey);

  console.log(publicKey.x.toString(16));

  // eslint-disable-next-line no-bitwise
  console.log(restoreY(publicKey.x, (publicKey.y & 1n) === 1n) === publicKey.y);
  console.log(publicKey.y);

  /*const y2c = mod(mod(mod(publicKey.x * publicKey.x) * publicKey.x) + curveParams.a * publicKey.x + curveParams.b);
  let y1 = sqrtMod(y2c);

  // eslint-disable-next-line no-bitwise
  const isYOdd = (y1 & 1n) === 1n;
  const y1Bytes = Buffer.from(y1.toString(16), 'hex');

  if (isYOdd) {
    y1 = mod(-y1);
    console.log('inverted');
  } else {
    console.log(y1Bytes[0]);
  }
*/
  //  const y1b = sqrtModB(y2c, CURVE.P);
  /*
      const y2 = pow2(
        sqrtModC(mod(mod(publicKey.x * mod(publicKey.x * publicKey.x)) + curveParams.a + curveParams.b))
      , 2n);
  */

//  console.log(y1 === publicKey.y);

  // error on true true
  /*
    console.log(y1 === publicKey.y);
    console.log(y1, publicKey.y)*/
  /*
      console.log('----')
      console.log((sqrtMod(publicKey.x) ** 2n) % CURVE.P === publicKey.x)
      console.log((sqrtModC(publicKey.x) ** 2n), publicKey.x) */

  /*  const hash = BigInt('0x025fe4bbee09ea3e9933ee43982fa25d4a83180ae11f336c6ee75a6dc3c58d11');

    const p1 = new Point(hash, 1n);
    const result = publicKey.add(p1);
    console.log(result);

    const p2 = JacobianPoint.fromAffine(p1);
    const result2 = JacobianPoint.fromAffine(publicKey).add(p2);
    console.log(result2.toAffine());

    const start = Date.now();
    const signature = sign(hash, privateKey);

    const isValid = verify(signature.r, signature.s, hash, publicKey);
    console.log(isValid);
    console.log(Date.now() - start); */
};

module.exports = init();
