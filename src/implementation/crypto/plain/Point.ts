import { mod, invert } from './math';
import curveParams from './secp256k1';

/* eslint-disable no-bitwise */
export default class Point {
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
    const lam = mod(3n * X1 ** 2n * invert(2n * Y1, curveParams.P));
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
    const lam = mod((Y2 - Y1) * invert(X2 - X1, curveParams.P));
    const X3 = mod(lam * lam - X1 - X2);
    const Y3 = mod(lam * (X1 - X3) - Y1);
    return new Point(X3, Y3);
  }

  multiply(n: bigint) {
    const dbls = this.getPrecomputes();
    let p = Point.ZERO;
    let f = Point.ZERO; // fake point
    for (let i = 0; i < 256; i++) {
      if (n & 1n) {
        p = p.add(dbls[i]);
      } else {
        f = f.add(dbls[i]);
      }
      // eslint-disable-next-line no-param-reassign
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
}
