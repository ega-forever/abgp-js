// eslint-disable-next-line import/no-extraneous-dependencies
import { expect } from 'chai';
import { fork } from 'child_process';
import crypto from 'crypto';
import * as path from 'path';
import { awaitNodesSynced, generateRandomRecordsWorker } from '../../utils/helpers';

const runInstance = (index: number, keys: any, settings: any, implementationType: any, connectionLinkMap: any) => {
  const implementationTypes = {
    RPC: 'ABGPRPCWorker.ts',
    TCP: 'ABGPTCPWorker.ts'
  };

  const instance = fork(path.join(__dirname, `../workers/${implementationTypes[implementationType]}`), [], {
    execArgv: ['-r', 'ts-node/register']
  });
  instance.send({
    args: [
      {
        index,
        keys,
        settings,
        links: connectionLinkMap ? connectionLinkMap.get(index) : null
      }
    ],
    type: 'init'
  });

  return instance;
};

export default function testSuite(ctx: any = {}, nodesCount: number = 0, implementationType: string = 'TCP', sendSignalToRandomPeer: boolean = true, connectionLinkMap: Map<number, number[]> = null) {
  beforeEach(async () => {
    const instances: any = [];

    ctx.keys = [];
    ctx.settings = {
      gossipInterval: {
        min: 150,
        max: 300
      },
      sendSignalToRandomPeer
    };

    for (let i = 0; i < nodesCount; i++) {
      const node = crypto.createECDH('secp256k1');
      node.generateKeys();

      if (node.getPrivateKey().toString('hex').length !== 64) {
        i--;
        continue;
      }

      ctx.keys.push({
        privateKey: node.getPrivateKey('hex'),
        publicKey: node.getPublicKey('hex', 'compressed')
      });
    }

    for (let index = 0; index < ctx.keys.length; index++) {
      const instance = runInstance(index, ctx.keys, ctx.settings, implementationType, connectionLinkMap);
      instances.push(instance);
    }

    const kill = () => {
      for (const instance of instances) instance.kill();
    };

    process.on('SIGINT', kill);
    process.on('SIGTERM', kill);
    ctx.instances = instances;
  });

  afterEach(async () => {
    for (const instance of ctx.instances) {
      instance.kill();
    }
  });

/*
  it('should sync changes, once most nodes online (51%), then all nodes online', async () => {
    const majority = Math.floor(ctx.instances.length / 2) + 1;
    const initialNodes = ctx.instances.slice(0, majority);
    const otherNodes = ctx.instances.slice(majority);

    for (const instance of initialNodes) {
      instance.send({ type: 'connect' });
      generateRandomRecordsWorker(instance);
    }

    const [results] = await awaitNodesSynced(initialNodes, ctx.keys.slice(0, majority));
    expect(results[0].length).to.eq(1);

    for (const instance of otherNodes) {
      instance.send({ type: 'connect' });
    }

    const [resultsAllNodesOnline] = await awaitNodesSynced(ctx.instances, ctx.keys);
    expect(resultsAllNodesOnline[0].length).to.eq(1);
  });
*/

  it('should sync changes, after node dropped', async () => {
    for (const instance of ctx.instances) {
      instance.send({ type: 'connect' });
      generateRandomRecordsWorker(instance);
    }

    const [results] = await awaitNodesSynced(ctx.instances, ctx.keys);
    expect(results[0].length).to.eq(1);

    console.log('before')

    const dropIndex = ctx.instances.length - 1;
    ctx.instances[dropIndex].kill();

    ctx.instances[dropIndex] = runInstance(
      dropIndex,
      ctx.keys,
      ctx.settings,
      implementationType,
      connectionLinkMap
    );

    ctx.instances[dropIndex].send({ type: 'connect' });

    const [resultsAfterResync] = await awaitNodesSynced(ctx.instances, ctx.keys);
    console.log('after')
    expect(resultsAfterResync[0].length).to.eq(1);
  });
}
