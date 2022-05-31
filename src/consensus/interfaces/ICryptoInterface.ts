/* eslint-disable no-unused-vars */

export default interface ICryptoInterface {
  generatePrivateKey(): Promise<string>;

  getPublicKey(privateKeyHex: string): Promise<string>;

  buildSharedPublicKeyX(publicKeys: string[], hash: string): Promise<string>;

  buildPartialSignature(privateKeyK: string, dataHash: string): Promise<string>;

  partialSignatureVerify(partialSignature: string, publicKeyHex: string, hash: string): Promise<boolean>;

  buildSharedSignature(partialSignatures: string[]): Promise<string>;

  verify(signature: string, sharedPublicKeyX: string): Promise<boolean>;
}