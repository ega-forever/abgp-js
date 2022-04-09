import MessageTypes from '../../consensus/constants/MessageTypes';
import ABGP from '../../consensus/main';
import PacketModel from '../../consensus/models/PacketModel';

export const generateRandomRecords = (node: ABGP, amount?: number) => {
  if (!amount) {
    // eslint-disable-next-line no-param-reassign
    amount = 7 + Math.ceil((15 - 7) * Math.random());
  }

  const hashes = [];

  for (let i = 0; i < amount; i++) {
    const record = {
      key: Math.random().toString(16).substr(2) + i,
      value: Math.random().toString(16).substr(2) + i,
      version: 1
    };
    const hash = node.append(record.key, record.key, record.version);
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

        const node1PacketAck = node1.messageApi.packet(MessageTypes.ACK);

        // @ts-ignore
        const node2ValidateState: PacketModel = await node2.requestProcessorService.process(node1PacketAck);
        if (!node2ValidateState) {
          continue;
        }

        // @ts-ignore
        const node1DataRequest: PacketModel = await node1.requestProcessorService.process(node2ValidateState);
        if (!node1DataRequest) {
          continue;
        }
        // @ts-ignore
        await node2.requestProcessorService.process(node1DataRequest);
      }
    }
  }
};

export const getUniqueRoots = (nodes: ABGP[]) => {
  const roots = nodes.map((node) => node.getStateRoot());
  const rootSet = new Set<string>(roots);
  return [...rootSet];
};

export const areNotUniqueHashes = (nodes: ABGP[]) => {
  const keys: any = {};

  for (const node of nodes) {
    for (const key of node.db.keys()) {
      if (!keys[key]) {
        keys[key] = new Set<string>();
      }
      keys[key].add(node.db.get(key).stateHash);
    }
  }

  return !!Object.values(keys).find((v: any) => v.size > 1);
};

export const getUniqueDbItemsCount = (nodes: ABGP[]) => {
  const state = {};

  for (const node of nodes) {
    for (const item of node.db.values()) {
      state[item.stateHash] = state[item.stateHash] ? state[item.stateHash] + 1 : 1;

      if (state[item.stateHash] === nodes.length) {
        delete state[item.stateHash];
      }
    }
  }

  return state;
};

export const awaitNodesSynced = async (nodes: any[], keys: any[]) => {
  const stateReplyMapInitialNodes: Map<string, {
    stateRoot: string,
    dataUpdateTimestamp: number,
    dbSize: number
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
        const dbSize = msg.args[2];
        stateReplyMapInitialNodes.set(publicKey, {
          stateRoot,
          dataUpdateTimestamp,
          dbSize
        });

        const uniqueRoots = Object.keys([...stateReplyMapInitialNodes.values()].reduce((acc, cur) => {
          acc[cur ? cur.stateRoot : '0'] = 1;
          return acc;
        }, {} as any));

        const uniqueTimestamps = Object.keys([...stateReplyMapInitialNodes.values()].reduce((acc, cur) => {
          acc[cur ? cur.dataUpdateTimestamp : 0] = 1;
          return acc;
        }, {} as any));

        const uniqueDbSizes = Object.keys([...stateReplyMapInitialNodes.values()].reduce((acc, cur) => {
          acc[cur ? cur.dbSize : 0] = 1;
          return acc;
        }, {} as any));

        if (uniqueRoots.length === 1 && uniqueDbSizes.length === 1) {
          return res([uniqueRoots, uniqueTimestamps, uniqueDbSizes]);
        }
      });
    });
    promises.push(promise);
  }

  return Promise.all(promises);
};
