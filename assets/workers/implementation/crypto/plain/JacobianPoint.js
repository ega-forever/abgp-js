"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const Point_1 = __importDefault(require("./Point"));
const math_1 = require("./math");
/**
 * algorithm is based on the following article: https://paulmillr.com/posts/noble-secp256k1-fast-ecc/
 */
class JacobianPoint {
    constructor(x, y, z) {
        this.x = x;
        this.y = y;
        this.z = z;
    }
    static fromAffine(p) {
        return new JacobianPoint(p.x, p.y, 1n);
    }
    // http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#doubling-dbl-2009-l
    double() {
        const X1 = this.x;
        const Y1 = this.y;
        const Z1 = this.z;
        const A = (0, math_1.mod)(X1 ** 2n);
        const B = (0, math_1.mod)(Y1 ** 2n);
        const C = (0, math_1.mod)(B ** 2n);
        const D = (0, math_1.mod)(2n * ((0, math_1.mod)((X1 + B) ** 2n) - A - C));
        const E = (0, math_1.mod)(3n * A);
        const F = (0, math_1.mod)(E ** 2n);
        const X3 = (0, math_1.mod)(F - 2n * D);
        const Y3 = (0, math_1.mod)(E * (D - X3) - 8n * C);
        const Z3 = (0, math_1.mod)(2n * Y1 * Z1);
        return new JacobianPoint(X3, Y3, Z3);
    }
    // http://hyperelliptic.org/EFD/g1p/auto-shortw-jacobian-0.html#addition-add-1998-cmo-2
    add(other) {
        const [a, b] = [this, other];
        const [X1, Y1, X2, Y2, Z1, Z2] = [a.x, a.y, b.x, b.y, a.z, b.z];
        if (X1 === 0n || Y1 === 0n)
            return b;
        if (X2 === 0n || Y2 === 0n)
            return a;
        const Z1Z1 = (0, math_1.mod)(Z1 ** 2n);
        const Z2Z2 = (0, math_1.mod)(Z2 ** 2n);
        const U1 = (0, math_1.mod)(X1 * Z2Z2);
        const U2 = (0, math_1.mod)(X2 * Z1Z1);
        const S1 = (0, math_1.mod)((0, math_1.mod)(Y1 * Z2) * Z2Z2);
        const S2 = (0, math_1.mod)((0, math_1.mod)(Y2 * Z1) * Z1Z1);
        const H = (0, math_1.mod)(U2 - U1);
        const r = (0, math_1.mod)(S2 - S1);
        // H = 0 meaning it's the same point.
        if (H === 0n) {
            return r === 0n ? this.double() : JacobianPoint.ZERO;
        }
        const HH = (0, math_1.mod)(H ** 2n);
        const HHH = (0, math_1.mod)(H * HH);
        const V = (0, math_1.mod)(U1 * HH);
        const X3 = (0, math_1.mod)(r ** 2n - HHH - 2n * V);
        const Y3 = (0, math_1.mod)(r * (V - X3) - S1 * HHH);
        const Z3 = (0, math_1.mod)(Z1 * Z2 * H);
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
    multiplyPrecomputes(n) {
        const precomputes = this.getPrecomputes();
        let p = JacobianPoint.ZERO;
        for (let i = 0; i < 256; i++) {
            if (n & 1n) {
                p = p.add(precomputes[i]);
            }
            // eslint-disable-next-line no-param-reassign
            n /= 2n;
        }
        return p;
    }
    // Double-and-add multiplication. https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication#Double-and-add
    multiply(n) {
        let p = JacobianPoint.ZERO;
        let d = this;
        while (n > 0n) {
            if (n & 1n)
                p = p.add(d);
            d = d.double();
            // eslint-disable-next-line no-param-reassign
            n /= 2n;
        }
        return p;
    }
    toAffine(invZ) {
        const { x, y, z } = this;
        const iz1 = invZ || (0, math_1.invert)(this.z);
        const iz2 = (0, math_1.mod)(iz1 * iz1);
        const iz3 = (0, math_1.mod)(iz2 * iz1);
        const ax = (0, math_1.mod)(x * iz2);
        const ay = (0, math_1.mod)(y * iz3);
        const zz = (0, math_1.mod)(z * iz1);
        if (zz !== 1n)
            throw new Error('invZ was invalid');
        return new Point_1.default(ax, ay);
    }
}
exports.default = JacobianPoint;
JacobianPoint.ZERO = new JacobianPoint(0n, 1n, 0n);
//# sourceMappingURL=JacobianPoint.js.map