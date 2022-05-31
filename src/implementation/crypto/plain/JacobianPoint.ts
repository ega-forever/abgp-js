import Point from './Point';
import { invert, mod } from './math';

export default class JacobianPoint {
  static ZERO = new JacobianPoint(0n, 1n, 0n);

  public x: bigint;

  public y: bigint;

  public z: bigint;

  private precomputes;

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
  }

  getPrecomputes() {
    if (this.precomputes) {
      return this.precomputes;
    }
    this.precomputes = [];

    let dbl = new JacobianPoint(this.x, this.y, this.z);
    for (let i = 0; i < 256; i++) {
      this.precomputes.push(dbl);
      dbl = dbl.double(); // [G, 2G, 4G, 8G..., 256G], optimized
    }

    return this.precomputes;
  }

  multiply(n: bigint) {
    const precomputes = this.getPrecomputes();
    let p = JacobianPoint.ZERO;
    let f = JacobianPoint.ZERO; // fake point
    for (let i = 0; i < 256; i++) {
      if (n & 1n) {
        p = p.add(precomputes[i]);
      } else {
        f = f.add(precomputes[i]);
      }
      // eslint-disable-next-line no-param-reassign
      n >>= 1n;
    }
    return p.toAffine();
  }

  multiplyUnsafe(n: bigint) {
    let p = JacobianPoint.ZERO;
    let d: JacobianPoint = this;
    while (n > 0n) {
      if (n & 1n) p = p.add(d);
      d = d.double();
      n >>= 1n;
    }
    return p;
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
