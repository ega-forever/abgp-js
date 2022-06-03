import ICryptoInterface, { ICryptoMathInterface } from '../../../consensus/interfaces/ICryptoInterface';
export default class Bnelliptic implements ICryptoInterface {
    math: ICryptoMathInterface;
    constructor();
    generatePrivateKey(): Promise<string>;
    getPublicKey(privateKeyHex: string): Promise<string>;
    buildPartialSignature(privateKeyK: string, dataHash: string): Promise<string>;
    buildSharedPublicKeyX(publicKeys: string[], hash: string): Promise<string>;
    buildSharedSignature(partialSignatures: string[]): Promise<string>;
    partialSignatureVerify(partialSignature: string, publicKeyHex: string, hash: string): Promise<boolean>;
    verify(signature: string, sharedPublicKeyX: string): Promise<boolean>;
    hash(message: string): string;
    private pubKeyToPoint;
    private pointToPublicKey;
}
