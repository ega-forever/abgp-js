import RecordModel from '../../consensus/models/RecordModel';
import { IStorageInterface } from '../../consensus/interfaces/IStorageInterface';

export default class PlainStorage implements IStorageInterface {
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
}
