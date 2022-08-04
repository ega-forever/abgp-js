// eslint-disable-next-line import/no-extraneous-dependencies
import { expect } from 'chai';
import MessageTypes from '../../consensus/constants/MessageTypes';
import ABGP from '../../consensus/main';
import SignatureType from '../../consensus/constants/SignatureType';
import RecordModel from '../../consensus/models/RecordModel';

export const generateRandomRecords = async (node: ABGP, amount?: number) => {
  if (!amount) {
    // eslint-disable-next-line no-param-reassign
    amount = 7 + Math.ceil((15 - 7) * Math.random());
  }

  const hashes = [];

  for (let i = 0; i < amount; i++) {
    const record = {
      key: Math.random().toString(16).substring(2) + i,
      value: Math.random().toString(16).substring(2) + i,
      version: 1
    };
    const hash = await node.appendApi.append(record.key, record.key, record.version);
    hashes.push(hash);
  }

  return { amount, hashes };
};

export const generateRandomRecordsWorker = (node: any, amount?: number) => {
  if (!amount) {
    // eslint-disable-next-line no-param-reassign
    amount = 7 + Math.ceil((15 - 7) * Math.random());
  }

  for (let i = 0; i < amount; i++) {
    const record = {
      key: Math.random().toString(16).substr(2) + i,
      value: Math.random().toString(16).substr(2) + i,
      version: 1
    };
    node.send({ type: 'append', args: [record.key, record.key, record.version] });
  }

  return amount;
};

export const syncNodesBetweenEachOther = async (nodes: ABGP[], totalGeneratedRecords: number, batchSize: number) => {
  for (let n = 0; n < nodes.length * nodes.length * Math.round(totalGeneratedRecords / batchSize); n++) {
    for (let i = 0; i < nodes.length; i++) {
      for (let s = 0; s < nodes.length; s++) {
        if (i === s) {
          continue;
        }

        const node1: ABGP = nodes[i];
        const node2: ABGP = nodes[s];

        if (!node1.nodes.has(node2.publicKey)) {
          continue;
        }

        const node1PeerStateNode2 = await node1.nodes.get(node2.publicKey).getState();

        const node1PacketDataReq = await node1.messageApi.packet(MessageTypes.DATA_REQ, {
          lastUpdateTimestamp: node1PeerStateNode2.timestamp,
          lastUpdateTimestampIndex: node1PeerStateNode2.timestampIndex
        });

        const node2DataForNode1 = await node2.requestProcessorService.process(node1PacketDataReq);

        if (!node2DataForNode1.data) {
          continue;
        }

        const sortedPublicKeys = [...node1.publicKeys.keys()].sort();

        const data: any[] = node2DataForNode1.data.data
          .sort((a, b) =>
            ((a.timestamp > b.timestamp ||
              (a.timestamp === b.timestamp && a.timestampIndex > b.timestampIndex)
            ) ? 1 : -1));

        for (const item of data) {
          await node1.appendApi.remoteAppend(
            RecordModel.fromPlainObject(item, sortedPublicKeys),
            node1.nodes.get(node2.publicKey),
            node2DataForNode1.root
          );
        }
      }
    }
  }
};

export const getUniqueRoots = async (nodes: ABGP[]) => {
  const states = await Promise.all(nodes.map((node) => node.getState()));
  const rootSet = new Set<string>(states.map((s) => s.root));
  return [...rootSet];
};

export const areNotUniqueHashes = async (nodes: ABGP[], totalRecordsCount: number) => {
  const keys: any = {};

  for (const node of nodes) {
    const records = await node.storage.Record.getAfterTimestamp(0, -1, totalRecordsCount);
    for (const record of records) {
      if (!keys[record.hash]) {
        keys[record.hash] = new Set<string>();
      }
      keys[record.hash].add(record.hash);
    }
  }

  return !!Object.values(keys).find((v: any) => v.size > 1);
};

export const getUniqueDbItemsCount = async (nodes: ABGP[], totalRecordsCount: number) => {
  const state = {};

  for (const node of nodes) {
    const records = await node.storage.Record.getAfterTimestamp(0, -1, totalRecordsCount);

    for (const record of records) {
      state[record.hash] = state[record.hash] ? state[record.hash] + 1 : 1;

      if (state[record.hash] === nodes.length) {
        delete state[record.hash];
      }
    }
  }

  return state;
};

export const getUniqueMultiSigDbItemsCount = async (nodes: ABGP[], totalRecordsCount: number) => {
  const state = {};

  for (const node of nodes) {
    const records = await node.storage.Record.getAfterTimestamp(0, -1, totalRecordsCount);

    for (const record of records) {
      if (record.signatureType !== SignatureType.MULTISIG) {
        continue;
      }

      expect(record.stateHash).to.not.eq(null);
      state[record.hash] = state[record.hash] ? state[record.hash] + 1 : 1;

      if (state[record.hash] === nodes.length) {
        delete state[record.hash];
      }
    }
  }

  return state;
};

export const awaitNodesSynced = async (nodes: any[], keys: any[]) => {
  const stateReplyMapInitialNodes: Map<string, {
    stateRoot: string,
    dataUpdateTimestamp: number
  }> = new Map<string, { stateRoot: string; dataUpdateTimestamp: number; dbSize: number }>();

  const promises: Array<Promise<any>> = [];

  for (let i = 0; i < nodes.length; i++) {
    const { publicKey } = keys[i];
    stateReplyMapInitialNodes.set(publicKey, null);

    const promise = new Promise((res) => {
      nodes[i].on('message', (msg: any) => {
        if (msg.type !== 'state_synced') return;

        const stateRoot = msg.args[0];
        const dataUpdateTimestamp = msg.args[1];
        stateReplyMapInitialNodes.set(publicKey, {
          stateRoot,
          dataUpdateTimestamp
        });

        const uniqueRoots = Object.keys([...stateReplyMapInitialNodes.values()].reduce((acc, cur) => {
          acc[cur ? cur.stateRoot : '0'] = 1;
          return acc;
        }, {} as any));

        const uniqueTimestamps = Object.keys([...stateReplyMapInitialNodes.values()].reduce((acc, cur) => {
          acc[cur ? cur.dataUpdateTimestamp : 0] = 1;
          return acc;
        }, {} as any));

        if (uniqueRoots.length === 1) {
          return res([uniqueRoots, uniqueTimestamps]);
        }
      });
    });
    promises.push(promise);
  }

  return Promise.all(promises);
};
