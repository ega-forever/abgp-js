import Point from './Point';
/**
 * algorithm is based on the following article: https://paulmillr.com/posts/noble-secp256k1-fast-ecc/
 */
export default class JacobianPoint {
    static ZERO: JacobianPoint;
    x: bigint;
    y: bigint;
    z: bigint;
    private precomputes;
    constructor(x: bigint, y: bigint, z: bigint);
    static fromAffine(p: Point): JacobianPoint;
    double(): JacobianPoint;
    add(other: JacobianPoint): JacobianPoint;
    getPrecomputes(): any;
    multiplyPrecomputes(n: bigint): JacobianPoint;
    multiply(n: bigint): JacobianPoint;
    toAffine(invZ?: bigint): Point;
}
