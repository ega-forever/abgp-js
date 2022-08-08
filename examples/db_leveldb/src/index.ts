import express from 'express';
import * as bodyParser from 'body-parser';
import cors from 'express-cors';
import config from './config';
import * as bunyan from 'bunyan';
import TCPABGP from 'abgp-js-modules-node-tcp';
import eventTypes from 'abgp-js/dist/consensus/constants/EventTypes';
import Crypto from 'abgp-js-modules-crypto-bnelliptic';
import StorageLevel from './StorageLevel';

const init = async () => {
  const app = express();
  const logger = bunyan.createLogger({ name: 'abgp.logger', level: config.logLevel });

  app.use(bodyParser.json({ limit: '3mb' }));
  app.use(bodyParser.urlencoded({
    extended: true
  }));
  app.use(cors());

  const storageLevel = new StorageLevel(config.db.path);

  const instance = new TCPABGP({
    address: `tcp://${config.node.host}:${config.node.port}/${config.node.publicKey}`,
    gossipInterval: {
      min: config.node.gossipInterval.min,
      max: config.node.gossipInterval.max
    },
    sendSignalToRandomPeer: config.node.sendSignalToRandomPeer,
    logger,
    privateKey: config.node.privateKey,
    storage: storageLevel,
    crypto: new Crypto()
  });


  for (const peer of config.node.peers) {
    instance.nodeApi.join(peer);
  }

  instance.on(eventTypes.STATE_UPDATE, async () => {
    const state = await instance.getState();
    logger.info(`root ${state.root} / lastTimestamp: ${state.timestamp}`);
  });


  app.post('/records', async (req, res) => {
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

  app.get('/records/:hash', async (req, res) => {
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

  app.get('/records/range/:timestamp/:timestampIndex/:limit', async (req, res) => {
    const timestamp = parseInt(req.params.timestamp, 10);
    const lastUpdateTimestampIndex = parseInt(req.params.timestampIndex);
    const limit = parseInt(req.params.limit);
    const safeLimit = limit < 1 || limit > 100 ? instance.batchReplicationSize : limit;
    const records = await instance.storage.Record.getAfterTimestamp(timestamp, lastUpdateTimestampIndex, safeLimit);

    const recordObjs = records.map((record: any) => {
      record.publicKeys = Array.from(record.publicKeys);
      record.signatures = Object.fromEntries(record.signaturesMap);
      delete record.signaturesMap;
      return record;
    })

    res.send(recordObjs);
  });

  app.get('/records/range/:timestamp', async (req, res) => {
    const timestamp = parseInt(req.params.timestamp, 10);
    const records = await instance.storage.Record.getByTimestamp(timestamp);

    const recordObjs = records.map((record: any) => {
      record.publicKeys = Array.from(record.publicKeys);
      record.signatures = Object.fromEntries(record.signaturesMap);
      delete record.signaturesMap;
      return record;
    })

    res.send(recordObjs);
  });

  app.get('/states', async (req, res) => {

    const states = await Promise.all(
      [...instance.publicKeys.values()].map(pk =>
        instance.storage.State.get(pk)
      )
    );

    res.send(states);
  });


  app.listen(config.rest.port, () => {
    logger.info(`rest started at ${config.rest.port}`);
  });

  await instance.connect();
  logger.info(`node started at ${config.node.port}`);
}

module.exports = init();