# Authenticated Byzantine Gossip Protocol (ABGP)

 [![Build Status](https://app.travis-ci.com/ega-forever/abgp-js.svg?token=HMksZg3K4cbPvAAXtLTy&branch=master)](https://travis-ci.com/ega-forever/abgp-js) 

ABGP Consensus Algorithm implementation in Node.js.

[Concept description](https://arxiv.org/ftp/arxiv/papers/2206/2206.03811.pdf) (PDF)

Checkout [website](https://ega-forever.github.io/abgp-js/) for live version (JS with web workers).

consensus features
* authenticated Gossip protocol (each node have its own private/public keypair)
* replication confirmed by multisignature (using ECC)
* M-of-N links supported (no need to directly connect all nodes between each other)
* 2f+1 BFT
* TLA+ (PlusCal) specs

implementation features
* Zero dependencies (pure implementation with extensions)
* Custom transport layer support: ABGP separates interface implementation and consensus.
* Custom storage layer support: There is an option to implement custom storage interface and connect different 
databases as storage layer (like Redis or MongoDB)

## Installation

### Via npm
```bash
$ npm install abgp-js --save
```

### From repo
```bash
$ npm run build
```

## How does it work?

### Algorithm
The algorithm represents an authenticated gossip protocol version of the original algorithm.
This means, that each network node (i.e. node) should be aware of the rest nodes in network. 
For node validation the ECC signatures (SECP256K1 in current implementation) are used. As a result, each node has its own private/public keypair.
All nodes should know about all public keys. For instance, in cluster of nodes [A, B, C], the node A should have public keys of [A (self public key), B, C].

The algorithm have 2 data structures: the db (i.e. database) and nodes state: 
1) The db keeps all current data. The data represents as key-value-version pair + signatures and involved public keys
2) The state of other linked nodes represents the  (merkle root and last updated timestamp)

The communication between nodes happens in bi-direction way. For instance in cluster of nodes [A, B, C], if node A sends DATA_REQ message to node B, 
then node B will send the reply back immediately (DATA_RES message). 

There are 3 types of messages:
1) DATA_REQ - each node sends periodically this packet, which contains root, last updated timestamp and 
last updated timestamp index of sender node + last updated timestamp and timestamp index of receiver node 
(which is cached locally on sender node, like "last seen record from receiver node"). 
The receiver node validates last timestamp + last timestamp index, and send back delta of changes 
(which happened after this timestamp and timestamp index). If there is no delta - then empty array returns.
2) DATA_REP - contains an array of requested record entries. These record entries then are applied to local state
3) ERR - returns if there is an error happened on receiver node during request process (for instance on DATA_REQ)

### Append process
There are 2 types of append: 
1) local - when user append data (key-value-version pair) to local node
2) remote - when node append locally remote changes (obtained from another node)

During the local append, a new record item is generated. The record item includes 
key-value-version pair, signature, hash and stateHash. The signature is obtained by signing hash of item 
with private key: ``signature = privateKey * SHA256(key, value, version)``. 
Then a hash for state is formed as: SHA256(key, value, version, signature). 
The stateHash is null for local append and will be generated once enough nodes (i.e. quorum) sign 
the record and multisig will be produced

During the remote append, local node append changes, received from another node. There are several possible scenarios:
1) in case there is a new record (haven't seen earlier by the node), then node validate this record, add its own signature and add to the database. If there is enough signatures (quorum, or 2f+1 by default), then node will build multisig.
2) in case node already has this record, then node compare signatures, add unique signatures to record, or create the multisig based on them (in case quorum has been reached).

Once node generates multisig for the record (or receive multisig from remote node) - it appends its hash to the root.
The formula looks like: ```current_root = (previous_root + record_hash) mod n ```, where n - is a secp256k1 param.

### signature types
There are 2 types for signatures:
1) intermediate - the single signature, calculated as: ``signature = privateKey * SHA256(key, value, version)``
2) multisig - the aggregated signature, built up from M-of-N nodes. In current implementation it requires quorum (2f+1 by default). 
The multisig is generated as: ```multisig = partialSig1 + partialSig2...```. 

### Signature validation
Based on type, there are 2 types of signature validation:
1) single signature - the validation happens against public key: ```publicKey * SHA256(key, value, version) = signature * G```
2) multisig validation: happens with 2 steps. On step 1 - the algorithm generates multiPublicKey, which includes all involved public keys in 
signature process: ```multiPublicKey = publicKey1 * SHA256(key, value, version) + publicKey2 * SHA256(key, value, version)...```. 
On step 2, the multiPublicKey validates against signature: ```multiPublicKey * SHA256(key, value, version) = signature * G```

In case the signature is not valid - then the following state item will be ignored and not appended.


## Limitations and assumptions
1) no key deletion. However, you can set null value for key
2) although algorithm doesn't require all nodes to be connected to each other, it's strongly recommend 
that each node will have at least f+1 linked connections with rest nodes.

# API

### new ABGP (options)

Returns a new ABGP instance. As ABGP is agnostic to protocol implementation, 
you have to create your own.
Please check the ``Custom transport layer`` section.

Arguments:

* `address: string`:  an address in custom format. The only rule is that address should include the public key in the end
 (example: `"tcp://127.0.0.1:2003/03fec1b3d32dbb0641877f65b4e77ba8466f37ab948c0b4780e4ed191be411d694"`)
* `gossipInterval: {min: number, max: number}`: min and max gossip interval between each new sync round
* `majorityAmount: number`: quorum size. If not set - then will be calculated by formula (2f + 1)
* `sendSignalToRandomPeer: boolean`: should send message only to single random node (during new sync round) or broadcast to everyone
* `batchReplicationSize: number`: how many records send per each round (default 10)
* `reqMiddleware: function`: request middleware (will be triggered on every new packet received)
* `resMiddleware: function`: response middleware (will be triggered on every new packet sent)
* `logger` (ILoggerInterface): logger instance. If omitted, then console.log will be used
* `privateKey`: the 64 length private key generated by secp256k1 standard. Please take a look at [example](test/unit/BFT.spec.ts) how key pairs are generated in tests.
* `storage` (IStorageInterface): storage layer implementation. Example can be found under (src/implementation/storage) 
* `crypto` (ICryptoInterface): crypto logic implementation. Examples can be found under (src/implementation/crypto) 

### instance.join(multiaddr: string): NodeModel

Add new node node by uri.

### await instance.appendApi.append(key: string, value: string, version?: number = 1): Promise<string>

Append new item to local state. Returns hash.

### await instance.messageApi.packet(type: number, data: any = null): Promise<PacketModel>

Create new packet, where ``type`` is packet type, and ``data`` some custom data

### instance.messageApi.decodePacket(message: Buffer): PacketModel

Decode packet from buffer

### await instance.messageApi.message(packet: PacketModel, nodePublicKey: string): Promise<PacketModel>

Send message to node

## Events

A ABGP instance emits the following events (available at ``/components/shared/EventTypes.ts``):

* `JOIN`: once we add new node
* `LEAVE`: once we remove node
* `STATE_UPDATE`: emits on each state update
* `STATE_SYNCED`: emits when comparing local and remote state and both states are equal

# Customizable transport layer

## Custom implementation

In order to communicate between nodes, you can use exciting modules (listed below) or implement the interface by yourself. 
In order to write your own implementation you have to implement 2 methods:
 
* The ```async initialize()``` function, which fires on ABGP start. This method is useful, when you want to open the connection, for instance, tcp one, or connect to certain message broker like rabbitMQ.

* The ```async call(address: string, packet: PacketModel): Promise<PacketModel>``` function, which fires each time instance wants to broadcast message to other node (address param).

Also, keep in mind, that instance doesn't handle the disconnected / dead nodes, which means that instance will try to make requests to all presented members in cluster, 
even if they are not available. So, you need to handle it on your own.

## Out of the box protocols

| Protocol | npm package
| --- | --- |
| [TCP](implementations/node/tcp/src/index.ts) | abgp-js-modules-node-tcp 
| [HTTP](implementations/node/rpc/src/index.ts) | abgp-js-modules-node-rpc


# Custom storage layer

## Custom implementation

In order to keep all state and records, there is an option to provide custom storage layer. The only requirement is to implement the interface (IStorageInterface). 
The storage layer can be anything: Redis, MongoDB, Postgres, SqLite and so on. An example with in-memory storage provider can be found under `src/implementation/storage/PlainStorage.ts`.

## Out of the box protocols

| Protocol | npm package
| --- | --- |
| [Plain (in-memory)](implementations/storage/plain/src/index.ts) | abgp-js-modules-storage-plain

# Custom crypto

## Custom implementation

As some projects try to reduce amount of dependencies, the crypto implementation has been moved to extensions, and right now have 2 implementations: pure (only native API used, like crypto)
and elliptic + bn.js (to speed up some calculations). However, you can create your own implementation, all you need is to follow the ```ICryptoInterface``` interface.

## Out of the box protocols

| Protocol | npm package
| --- | --- |
| [bigNumber + elliptic](implementations/crypto/bnelliptic/src/index.ts) | abgp-js-modules-crypto-bnelliptic
| [plain](implementations/crypto/plain/src/index.ts) | abgp-js-modules-crypto-plain

# Usage
Please check tests for usage examples

However, you still can implement your own protocol.

# Implemented examples

| Implementation | 
| --- | 
| [MongoDB](examples/db_mongo) | 

# TLA+ specs

| Test type | 
| --- | 
| [Concurrency](tla/ConcurrentAppend.tla) |
| [Ordering + connections links](tla/NoOrderingSync.tla) |

# License

[GNU AGPLv3](LICENSE)

# Copyright

Copyright (c) 2018-2022 Egor Zuev
