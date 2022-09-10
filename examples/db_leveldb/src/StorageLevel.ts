import { IRecord, IState, IStorageInterface } from 'abgp-js/dist/consensus/interfaces/IStorageInterface';
import StateModel from 'abgp-js/dist/consensus/models/StateModel';
import RecordModel from 'abgp-js/dist/consensus/models/RecordModel';
import { ClassicLevel } from 'classic-level';
import path from 'path';

class Utils {
  public static async has(db: ClassicLevel, key: string): Promise<boolean> {
    try {
      await db.get(key);
      return true;
    } catch (e) {
      if (e.code === 'LEVEL_NOT_FOUND') {
        return false;
      }
      throw e;
    }
  }
}

export class StorageLevelRecord implements IRecord {
  private recordRangeDb: ClassicLevel;
  private readonly recordDb: ClassicLevel;

  constructor(p: string) {
    this.recordDb = new ClassicLevel(path.join(p, 'record'), { valueEncoding: 'json' });
    this.recordRangeDb = new ClassicLevel(path.join(p, 'record_range'), { valueEncoding: 'json' });
  }

  async del(hash: string): Promise<void> {
    const isRecordExist = await Utils.has(this.recordDb, hash);

    if (!isRecordExist) {
      return null;
    }

    const levelRecord = await this.recordDb.get(hash);
    const record = JSON.parse(levelRecord);

    await this.recordRangeDb.del(`${record.timestamp}:${record.timestampIndex}`);
    await this.recordDb.del(hash);
  }

  async get(hash: string): Promise<RecordModel | null> {
    const isRecordExist = await Utils.has(this.recordDb, hash);

    if (!isRecordExist) {
      return null;
    }

    const levelRecord = await this.recordDb.get(hash);
    const record = JSON.parse(levelRecord);
    return new RecordModel({
      hash: record.hash,
      key: record.key,
      value: record.value,
      version: record.version,
      timestamp: record.timestamp,
      timestampIndex: record.timestampIndex,
      signatureType: record.signatureType,
      signaturesMap: new Map(Object.entries(record.signatures)),
      publicKeys: new Set<string>(record.publicKeys)
    });
  }

  async getAfterTimestamp(timestamp: number, timestampIndex: number, limit: number): Promise<RecordModel[]> {
    const rangeRecordsKeys = await this.recordRangeDb.keys({ gt: `${timestamp}:${timestampIndex}`, limit }).all();
    const rangeRecordHashes = await this.recordRangeDb.getMany(rangeRecordsKeys);

    if (!rangeRecordHashes) {
      return [];
    }

    const records = await this.recordDb.getMany(rangeRecordHashes);

    return records.map(levelRecord => {
      const record = JSON.parse(levelRecord);
      return new RecordModel({
        hash: record.hash,
        key: record.key,
        value: record.value,
        version: record.version,
        timestamp: record.timestamp,
        timestampIndex: record.timestampIndex,
        signatureType: record.signatureType,
        signaturesMap: new Map(Object.entries(record.signatures)),
        publicKeys: new Set<string>(record.publicKeys)
      });
    });
  }

  async getByTimestamp(timestamp: number): Promise<RecordModel[]> {
    const rangeRecordsKeys = await this.recordRangeDb.keys({
      gte: `${timestamp}:0`,
      lt: `${timestamp + 1}:0`
    }).all();

    const rangeRecordHashes = await this.recordRangeDb.getMany(rangeRecordsKeys);

    if (!rangeRecordHashes) {
      return [];
    }

    const records = await this.recordDb.getMany(rangeRecordHashes);

    return records.map(levelRecord => {
      const record = JSON.parse(levelRecord);
      return new RecordModel({
        hash: record.hash,
        key: record.key,
        value: record.value,
        version: record.version,
        timestamp: record.timestamp,
        timestampIndex: record.timestampIndex,
        signatureType: record.signatureType,
        signaturesMap: new Map(Object.entries(record.signatures)),
        publicKeys: new Set<string>(record.publicKeys)
      });
    });
  }

  async save(record: RecordModel): Promise<void> {
    const levelRecord = {
      hash: record.hash,
      key: record.key,
      value: record.value,
      version: record.version,
      timestamp: record.timestamp,
      timestampIndex: record.timestampIndex,
      signatureType: record.signatureType,
      publicKeys: Array.from(record.publicKeys),
      signatures: Object.fromEntries(record.signaturesMap)
    }

    const isExistedRecord = await Utils.has(this.recordDb, levelRecord.hash);

    if (isExistedRecord) {
      await this.del(levelRecord.hash);
    }

    await this.recordRangeDb.put(`${levelRecord.timestamp}:${levelRecord.timestampIndex}`, levelRecord.hash);
    await this.recordDb.put(levelRecord.hash, JSON.stringify(levelRecord));
  }

  async has(hash: string): Promise<boolean> {
    return await Utils.has(this.recordDb, hash);
  }
}

export class StorageLevelState implements IState {
  private readonly stateDb: ClassicLevel;

  constructor(p: string) {
    this.stateDb = new ClassicLevel(path.join(p, 'state'), { valueEncoding: 'json' });
  }

  async get(publicKey: string): Promise<StateModel> {
    const isStateExist = await Utils.has(this.stateDb, publicKey);

    if (!isStateExist) {
      return {
        timestamp: 0,
        timestampIndex: -1,
        root: '0',
        publicKey
      };
    }

    const levelState = await this.stateDb.get(publicKey);
    const state = JSON.parse(levelState);

    return {
      timestamp: state.timestamp,
      timestampIndex: state.timestampIndex,
      root: state.root,
      publicKey: state.publicKey
    }
  }

  async save(state: StateModel): Promise<void> {
    await this.stateDb.put(state.publicKey, JSON.stringify(state));
  }

}

export default class StorageLevel implements IStorageInterface {
  Record: StorageLevelRecord;
  State: StorageLevelState;

  public constructor(path: string) {
    this.Record = new StorageLevelRecord(path);
    this.State = new StorageLevelState(path);
  }
}