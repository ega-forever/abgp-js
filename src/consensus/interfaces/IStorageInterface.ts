/* eslint-disable no-unused-vars */
import RecordModel from '../models/RecordModel';

export interface IStorageInterface {
  save(record: RecordModel): Promise<void>;

  get(hash: string): Promise<RecordModel | null>;

  del(hash: string): Promise<void>;

  has(hash: string): Promise<boolean>;

  getByTimestamp(timestamp: number): Promise<RecordModel[]>;

  getAfterTimestamp(timestamp: number, timestampIndex: number, limit: number): Promise<RecordModel[]>;

}
