"use strict";
var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};
Object.defineProperty(exports, "__esModule", { value: true });
const math_1 = require("./math");
const secp256k1_1 = __importDefault(require("./secp256k1"));
/**
 * algorithm is based on the following article: https://paulmillr.com/posts/noble-secp256k1-fast-ecc/
 */
class Point {
    constructor(x, y) {
        this.x = x;
        this.y = y;
    }
    // Adds point to itself. http://hyperelliptic.org/EFD/g1p/auto-shortw.html
    double() {
        const X1 = this.x;
        const Y1 = this.y;
        const lam = (0, math_1.mod)(3n * X1 ** 2n * (0, math_1.invert)(2n * Y1, secp256k1_1.default.P));
        const X3 = (0, math_1.mod)(lam * lam - 2n * X1);
        const Y3 = (0, math_1.mod)(lam * (X1 - X3) - Y1);
        return new Point(X3, Y3);
    }
    // Adds point to other point. http://hyperelliptic.org/EFD/g1p/auto-shortw.html
    add(other) {
        const [a, b] = [this, other];
        const [X1, Y1, X2, Y2] = [a.x, a.y, b.x, b.y];
        if (X1 === 0n || Y1 === 0n)
            return b;
        if (X2 === 0n || Y2 === 0n)
            return a;
        if (X1 === X2 && Y1 === Y2)
            return this.double();
        if (X1 === X2 && Y1 === -Y2)
            return Point.ZERO;
        const lam = (0, math_1.mod)((Y2 - Y1) * (0, math_1.invert)(X2 - X1, secp256k1_1.default.P));
        const X3 = (0, math_1.mod)(lam * lam - X1 - X2);
        const Y3 = (0, math_1.mod)(lam * (X1 - X3) - Y1);
        return new Point(X3, Y3);
    }
    // Double-and-add multiplication. https://en.wikipedia.org/wiki/Elliptic_curve_point_multiplication#Double-and-add
    multiply(n) {
        let p = Point.ZERO;
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
}
exports.default = Point;
Point.ZERO = new Point(0n, 0n); // Point at infinity aka identity point aka zero
//# sourceMappingURL=Point.js.map