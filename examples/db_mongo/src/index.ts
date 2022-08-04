import express from 'express';
import * as bodyParser from 'body-parser';
import cors from 'express-cors';
import config from './config';
import * as bunyan from 'bunyan';
import TCPABGP from 'abgp-js-modules-node-tcp';
import eventTypes from 'abgp-js/dist/consensus/constants/EventTypes';
import Crypto from 'abgp-js-modules-crypto-bnelliptic';
import StorageMongo from './StorageMongo';

const init = async () => {
  const app = express();
  const logger = bunyan.createLogger({ name: 'abgp.logger', level: config.logLevel });

  app.use(bodyParser.json({ limit: '3mb' }));
  app.use(bodyParser.urlencoded({
    extended: true
  }));
  app.use(cors());

  const storageMongo = new StorageMongo();
  await storageMongo.init(config.db.uri);

  const instance = new TCPABGP({
    address: `tcp://${config.node.host}:${config.node.port}/${config.node.publicKey}`,
    gossipInterval: {
      min: config.node.gossipInterval.min,
      max: config.node.gossipInterval.max
    },
    sendSignalToRandomPeer: config.node.sendSignalToRandomPeer,
    logger,
    privateKey: config.node.privateKey,
    storage: storageMongo,
    crypto: new Crypto()
  });


  for (const peer of config.node.peers) {
    instance.nodeApi.join(peer);
  }

  instance.on(eventTypes.STATE_UPDATE, async () => {
    const state = await instance.getState();
    logger.info(`root ${state.root} / lastTimestamp: ${state.timestamp}`);
  });


  app.post('/record', async (req, res) => {
    if (!req.body.key || !req.body.value || !req.body.version) {
      return res.status(400).send({
        error: 'object should include [key, value, version]'
      });
    }

    const hash = await instance.appendApi.append(req.body.key, req.body.value, req.body.version);

    res.send({
      key: req.body.key,
      value: req.body.value,
      version: req.body.version,
      hash
    });
  });

  app.get('/:hash', async (req, res) => {
    if (!req.params.hash) {
      return res.send({});
    }

    const record: any = await instance.storage.Record.get(req.params.hash);

    if (!record) {
      return res.send({});
    }

    record.publicKeys = Array.from(record.publicKeys);
    record.signatures = Object.fromEntries(record.signaturesMap);
    delete record.signaturesMap;

    res.send(record);
  });


  app.get('/test/:timestamp/:timestampIndex', async (req, res) => {
    const timestamp = parseInt(req.params.timestamp, 10);
    const lastUpdateTimestampIndex = parseInt(req.params.timestampIndex)

    const records = await instance.storage.Record.getAfterTimestamp(timestamp, lastUpdateTimestampIndex, instance.batchReplicationSize);
    res.send(records);
  });



  app.listen(config.rest.port, () => {
    logger.info(`rest started at ${config.rest.port}`);
  });

  await instance.connect();
  logger.info(`node started at ${config.node.port}`);
}

module.exports = init();