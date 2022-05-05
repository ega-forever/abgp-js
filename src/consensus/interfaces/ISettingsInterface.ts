import PacketModel from '../models/PacketModel';
import { IStorageInterface } from './IStorageInterface';

/* eslint-disable no-unused-vars */
export interface ISettingsInterface {
  privateKey: string;
  address: string;
  gossipInterval: {
    min: number,
    max: number
  };
  publicKeys?: string[];
  majorityAmount?: number;
  sendSignalToRandomPeer: boolean;
  batchReplicationSize?: number;
  reqMiddleware?: (packet: PacketModel) => Promise<PacketModel>;
  resMiddleware?: (packet: PacketModel, peerPublicKey: string) => Promise<PacketModel>;
  logger: {
    error: () => void,
    info: () => void,
    trace: () => void
  };
  storage: IStorageInterface
}
