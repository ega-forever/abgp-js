import RecordModel from '../../consensus/models/RecordModel';
import { IRecord, IState, IStorageInterface } from '../../consensus/interfaces/IStorageInterface';
import StateModel from '../../consensus/models/StateModel';

class PlainStorageRecord implements IRecord {
  private readonly db: Map<string, RecordModel>;

  public constructor() {
    this.db = new Map<string, RecordModel>();
  }

  async get(hash: string): Promise<RecordModel | null> {
    const item = this.db.get(hash);

    if (!item) {
      return null;
    }

    return item.cloneObject();
  }

  async save(record: RecordModel): Promise<void> {
    this.db.set(record.hash, record.cloneObject());
  }

  async has(hash: string): Promise<boolean> {
    return this.db.has(hash);
  }

  async getByTimestamp(timestamp: number): Promise<RecordModel[]> {
    return [...this.db.values()]
      .filter((v) => v.timestamp === timestamp)
      .map((item) => item.cloneObject());
  }

  async getAfterTimestamp(timestamp: number, timestampIndex: number, limit: number): Promise<RecordModel[]> {
    return [...this.db.values()]
      .filter((v) =>
        v.timestamp > timestamp ||
        (v.timestamp === timestamp && v.timestampIndex > timestampIndex))
      .sort((a, b) =>
        ((a.timestamp > b.timestamp ||
          (a.timestamp === b.timestamp && a.timestampIndex > b.timestampIndex)
        ) ? 1 : -1))
      .slice(0, limit)
      .map((item) => item.cloneObject());
  }

  async del(hash: string): Promise<void> {
    this.db.delete(hash);
  }

  async getLast(signatureType: number): Promise<RecordModel | null> {
    const item = [...this.db.values()]
      .sort((a, b) =>
        ((a.timestamp < b.timestamp ||
          (a.timestamp === b.timestamp && a.timestampIndex < b.timestampIndex)
        ) ? 1 : -1))
      .find((v) => v.signatureType === signatureType);

    return item ? item.cloneObject() : null;
  }
}

class PlainStorageState implements IState {
  private readonly db: Map<string, StateModel>;

  public constructor() {
    this.db = new Map<string, StateModel>();
  }

  async get(publicKey: string): Promise<StateModel> {
    const state = this.db.get(publicKey);

    if (!state) {
      return {
        timestamp: 0,
        timestampIndex: -1,
        root: '0',
        publicKey
      };
    }

    return state;
  }

  async save(state: StateModel): Promise<void> {
    this.db.set(state.publicKey, state);
  }
}

export default class PlainStorage implements IStorageInterface {
  public readonly Record: IRecord;

  public readonly State: IState;

  public constructor() {
    this.Record = new PlainStorageRecord();
    this.State = new PlainStorageState();
  }
}
