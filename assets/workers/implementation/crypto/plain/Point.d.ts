/**
 * algorithm is based on the following article: https://paulmillr.com/posts/noble-secp256k1-fast-ecc/
 */
export default class Point {
    static ZERO: Point;
    readonly x: bigint;
    readonly y: bigint;
    constructor(x: bigint, y: bigint);
    double(): Point;
    add(other: Point): Point;
    multiply(n: bigint): Point;
}
