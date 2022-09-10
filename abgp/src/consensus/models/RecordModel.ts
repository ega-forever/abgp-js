class RecordModelBase {
  public hash: string;

  public key: string;

  public value: string;

  public version: number;

  public timestamp: number;

  public timestampIndex: number;

  public signatureType: number;
}

export class RecordModelPlain extends RecordModelBase {
  public signatures: any; // signature to public key

  public publicKeyMap: number;
}

class RecordModelConstructorParams extends RecordModelBase {
  public signaturesMap: Map<string, string>; // signature to public key

  public publicKeys: Set<string>;
}

export default class RecordModel extends RecordModelConstructorParams {
  public constructor(obj: RecordModelConstructorParams) {
    super();
    Object.assign(this, obj);
  }

  public static fromPlainObject(obj: RecordModelPlain, sortedPublicKeys: string[]): RecordModel {
    const involvedPublicKeys = obj.publicKeyMap.toString(2)
      .padStart(sortedPublicKeys.length, '0')
      .split('')
      .reduce((arr, elem, index) => {
        if (elem === '0') {
          return arr;
        }

        const publicKey = sortedPublicKeys[index];
        arr.add(publicKey);

        return arr;
      }, new Set<string>());

    return new RecordModel({
      hash: obj.hash,
      key: obj.key,
      value: obj.value,
      version: obj.version,
      timestamp: obj.timestamp,
      timestampIndex: obj.timestampIndex,
      signaturesMap: new Map(Object.entries(obj.signatures)),
      signatureType: obj.signatureType,
      publicKeys: involvedPublicKeys
    });
  }

  public toPlainObject(sortedPublicKeys: string[]): RecordModelPlain {
    const signaturesMapObj = [...this.signaturesMap.keys()]
      .reduce((result, key) => {
        // eslint-disable-next-line no-param-reassign
        result[key] = this.signaturesMap.get(key);
        return result;
      }, {});

    const publicKeysMapDouble = sortedPublicKeys.map((publicKey) => (this.publicKeys.has(publicKey) ? 1 : 0)).join('');

    return {
      hash: this.hash,
      key: this.key,
      value: this.value,
      version: this.version,
      timestamp: this.timestamp,
      timestampIndex: this.timestampIndex,
      signatures: signaturesMapObj,
      signatureType: this.signatureType,
      publicKeyMap: parseInt(publicKeysMapDouble, 2)
    };
  }

  public cloneObject() {
    return new RecordModel({
      hash: this.hash,
      key: this.key,
      value: this.value,
      version: this.version,
      timestamp: this.timestamp,
      timestampIndex: this.timestampIndex,
      signaturesMap: new Map<string, string>(this.signaturesMap),
      signatureType: this.signatureType,
      publicKeys: new Set<string>(this.publicKeys)
    });
  }
}
