import { expect } from 'chai';
import { fork } from 'child_process';
import crypto from 'crypto';
import * as path from 'path';
import { awaitNodesSynced, generateRandomRecordsWorker } from '../../utils/helpers';

export function testSuite(ctx: any = {}, nodesCount: number = 0, implementationType: string = 'TCP', sendSignalToRandomPeer: boolean = true, connectionLinkMap: Map<number, number[]> = null) {

  beforeEach(async () => {

    const instances: any = [];

    ctx.keys = [];
    ctx.settings = {
      gossipInterval: {
        min: 300,
        max: 1000
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

    const implementationTypes = {
      RPC: 'ABGPRPCWorker.ts',
      TCP: 'ABGPTCPWorker.ts'
    };

    for (let index = 0; index < ctx.keys.length; index++) {
      const instance = fork(path.join(__dirname, `../workers/${implementationTypes[implementationType]}`), [], {
        execArgv: ['-r', 'ts-node/register']
      });
      instances.push(instance);
      instance.send({
        args: [
          {
            index,
            keys: ctx.keys,
            settings: ctx.settings,
            links: connectionLinkMap ? connectionLinkMap.get(index) : null
          }
        ],
        type: 'init'
      });
    }

    const kill = () => {
      for (const instance of instances)
        instance.kill();
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

  it(`should sync changes, once most nodes online (51%), then all nodes online`, async () => {

    const majority = Math.floor(ctx.instances.length / 2) + 1;
    const initialNodes = ctx.instances.slice(0, majority);
    const otherNodes = ctx.instances.slice(majority);

    let totalGeneratedAmount = 0;

    for (const instance of initialNodes) {
      instance.send({ type: 'connect' });
      totalGeneratedAmount += generateRandomRecordsWorker(instance);
    }

    const [results] = await awaitNodesSynced(initialNodes, ctx.keys.slice(0, majority));
    const dbSize = results[2][0];

    expect(parseInt(dbSize, 10)).to.eq(totalGeneratedAmount);

    for (const instance of otherNodes) {
      instance.send({ type: 'connect' });
    }

    const [resultsAllNodesOnline] = await awaitNodesSynced(ctx.instances, ctx.keys);
    const dbSizeAllNodesOnline = resultsAllNodesOnline[2][0];

    expect(parseInt(dbSizeAllNodesOnline, 10)).to.eq(totalGeneratedAmount);

  });

}
