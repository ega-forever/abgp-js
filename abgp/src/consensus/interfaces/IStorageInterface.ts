/* eslint-disable no-unused-vars */
import RecordModel from '../models/RecordModel';
import StateModel from '../models/StateModel';

export interface IRecord {
  save(record: RecordModel): Promise<void>;

  get(hash: string): Promise<RecordModel | null>;

  del(hash: string): Promise<void>;

  has(hash: string): Promise<boolean>;

  getByTimestamp(timestamp: number): Promise<RecordModel[]>;

  getAfterTimestamp(timestamp: number, timestampIndex: number, limit: number): Promise<RecordModel[]>;
}

export interface IState {
  save(state: StateModel): Promise<void>;

  get(publicKey: string): Promise<StateModel>;
}

export interface IStorageInterface {
  Record: IRecord;

  State: IState;
}
