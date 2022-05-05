export default class RecordModel {
  public hash: string;

  public stateHash: string;

  public key: string;

  public value: string;

  public version: number;

  public timestamp: number;

  public timestampIndex: number;

  public signaturesMap: Map<string, string>; // signature to public key

  public signatureType: number;

  public publicKeys?: Set<string>;

  public publicKeyMap?: number;

  public static fromPlainObject(obj: any) {
    const dbItem = new RecordModel();

    dbItem.hash = obj.hash;
    dbItem.stateHash = obj.stateHash;
    dbItem.key = obj.key;
    dbItem.value = obj.value;
    dbItem.version = obj.version;
    dbItem.timestamp = obj.timestamp;
    dbItem.timestampIndex = obj.timestampIndex;
    dbItem.signaturesMap = obj.signaturesMap ? new Map(Object.entries(obj.signaturesMap)) : new Map<string, string>();
    dbItem.signatureType = obj.signatureType;
    dbItem.publicKeys = obj.publicKeys ? new Set(obj.publicKeys) : new Set<string>();
    dbItem.publicKeyMap = obj.publicKeyMap;

    return dbItem;
  }

  public toPlainObject(publicKeys?: string[]) {
    const signaturesMapObj = [...this.signaturesMap.keys()]
      .reduce((result, key) => {
        // eslint-disable-next-line no-param-reassign
        result[key] = this.signaturesMap.get(key);
        return result;
      }, {});

    const publicKeysMapDouble = publicKeys ? publicKeys.sort().map((publicKey) => (this.publicKeys.has(publicKey) ? 1 : 0)).join('') : null;

    return {
      hash: this.hash,
      stateHash: this.stateHash,
      key: this.key,
      value: this.value,
      version: this.version,
      timestamp: this.timestamp,
      timestampIndex: this.timestampIndex,
      signaturesMap: signaturesMapObj,
      signatureType: this.signatureType,
      publicKeys: publicKeys ? null : (this.publicKeys ? [...this.publicKeys] : []),
      publicKeyMap: this.publicKeyMap || parseInt(publicKeysMapDouble, 2)
    };
  }

  public cloneObject() {
    const obj = this.toPlainObject();
    return RecordModel.fromPlainObject(obj);
  }
}
