import * as dotenv from 'dotenv';

dotenv.config();

const config = {
  db: {
    uri: process.env.DB_URI || 'mongodb://localhost:27017/test'
  },
  rest: {
    port: process.env.REST_PORT ? parseInt(process.env.REST_PORT, 10) : 3001
  },
  node: {
    host: process.env.NODE_HOST || 'localhost',
    port: process.env.NODE_PORT ? parseInt(process.env.NODE_PORT, 10) : 3002,
    privateKey: process.env.NODE_PRIVATE_KEY,
    publicKey: process.env.NODE_PUBLIC_KEY,
    sendSignalToRandomPeer: process.env.NODE_SEND_SIGNAL_TO_RANDOM_PEER ? !!parseInt(process.env.NODE_SEND_SIGNAL_TO_RANDOM_PEER) : false,
    gossipInterval: {
      min: process.env.NODE_GOSSIP_INTERVAL_MIN ? parseInt(process.env.NODE_GOSSIP_INTERVAL_MIN, 10) : 50,
      max: process.env.NODE_GOSSIP_INTERVAL_MAX ? parseInt(process.env.NODE_GOSSIP_INTERVAL_MAX, 10) : 300
    },
    peers: process.env.NODE_PEERS ? process.env.NODE_PEERS.split(';').map(s => s.trim()) : []
  },
  logLevel: process.env.LOG_LEVEL ? parseInt(process.env.LOG_LEVEL, 10) : 50,
};

export default config;
