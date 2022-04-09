# Authenticated Byzantine Gossip Protocol (ABGP)

 [![Build Status](https://app.travis-ci.com/ega-forever/abgp-js.svg?token=HMksZg3K4cbPvAAXtLTy&branch=master)](https://travis-ci.com/ega-forever/abgp-js) 

ABGP Consensus Algorithm implementation in Node.js.

consensus features
* authenticated Gossip protocol (each node have its own private/public keypair)
* replication confirmed by multisignature (using ECC)
* M-of-N links supported (no need to directly connect all nodes between each other)
* 2f+1 BFT

implementation features
* Custom transport layer support: ABGP separates interface implementation and consensus.

## How does it work?

### Algorithm
The algorithm represents an authenticated gossip protocol version of the original algorithm.
This means, that each network peer (i.e. node) should be aware of the rest peers in network. 
For peer validation the ECC signatures (SECP256K1 in current implementation) are used. As a result, each peer has its own private/public keypair.
All peers should know about all public keys. For instance, in cluster of nodes [A, B, C], the node A should have public keys of [A (self public key), B, C].

The algorithm have 2 data structures: the db (i.e. database) and peers state: 
1) The db keeps all current data. The data represents as key-value-version pair + signatures and involved public keys
2) The state of other linked peers represents the  (merkle root and last updated timestamp)

The communication between peers happens in one direction. For instance in cluster of nodes [A, B, C], if node A sends ACK message to node B, 
then node B will not send the reply immediately, so don't expect atomic sync between 2 peers. 

There are 3 types of messages:
1) ACK - each node sends periodically this packet, which contains merkle root and last updated timestamp. So, if node A sends ACK message to node B,
then node B check its state + its local state of node A. If node A has more recent state, then node B send to node A STATE_REQ message.
4) DATA_REQ - this message contains last seen state of peer, with which sync happens (comparing local state against remove).
5) DATA_REP - contains an array of requested log entries. These log entries then are applied to local state


### Append process
There are 2 types of append: 
1) local - when user append data (key-value-version pair) to local state
2) remote - when peer append locally remote changes (obtained from another peer)

During the local append, a single new state item is generated. The state item includes key-value-version pair, signature and hash.
The signature is obtained by signing hash of item with private key: ``signature = privateKey * SHA256(key, value, version)``. 
Then a hash for state is formed as: SHA256(key, value, version, signature). 

During the remote append, several state items can be generated. There are several possible scenarios:
1) received new state item from remote peer with the same key-value-version pair (N = 2f+1, f > 1, signatures amount < f+1). In this case, 
2 state items are generated: one for received state item with signature from remote peer and one state item with own signature. 
2) received new state items (several state items with the same key-value-version pair, but with different signatures) from remote peer (N = 2f+1, f > 1, signatures amount >= f+1). In this case, 
all state items for the corresponding key-value-version pair got dropped, but a new state item with aggregated multi-signature is generated.
3) received new state item from remote peer with the same key-value-version pair, as peer has locally (N = 2f+1, f > 1, signatures amount < f+1). 
In this case, 1 state item is generated: one for received state item with signature from remote peer.

### signature types
There are 2 types for signatures:
1) intermediate - the single signature, calculated as: ``signature = privateKey * SHA256(key, value, version)``
2) multisig - the aggregated signature, built up from M-of-N peers. In current implementation it requires quorum (f+1). 
The multisig is generated as: ```multisig = partialSig1 + partialSig2...```. 

### Signature validation
Based on type, there are 2 types of signature validation:
1) single signature - the validation happens against public key: ```publicKey * SHA256(key, value, version) = signature * G```
2) multisig validation: happens with 2 steps. On step 1 - the algorithm generates multiPublicKey, which includes all involved public keys in 
signature process: ```multiPublicKey = publicKey1 * SHA256(key, value, version) + publicKey2 * SHA256(key, value, version)...```. 
On step 2, the multiPublicKey validates against signature: ```multiPublicKey * SHA256(key, value, version) = signature * G```

In case the signature is not valid - then the following state item will be ignored and not appended.


## Limitations and assumptions
1) the state tree sync is not optimized (the whole tree is passed during single request)
2) no key deletion. However, you can set null value for key
3) although algorithm doesn't require all nodes to be connected to each other, it's strongly recommend 
that each node will have at least f+1 linked connections with rest peers.

## Installation

### Via npm
```bash
$ npm install abgp-js --save
```

### From repo
```bash
$ npm run build
```

# API

### new ABGP (options)

Returns a new ABGP instance. As ABGP is agnostic to protocol implementation, 
you have to create your own.
Please check the ``Custom transport layer`` section.

Arguments:

* `address: string`:  an address in custom format. The only rule is that address should include the public key in the end
 (example: `"tcp://127.0.0.1:2003/03fec1b3d32dbb0641877f65b4e77ba8466f37ab948c0b4780e4ed191be411d694"`)
* `gossipInterval: {min: number, max: number}`: min and max gossip interval between each new sync round
* `sendSignalToRandomPeer: boolean`: should send message only to single random peer (during new sync round) or broadcast to everyone
* `reqMiddleware: function`: request middleware (will be triggered on every new packet received)
* `resMiddleware: function`: response middleware (will be triggered on every new packet sent)
* `logger` (ILoggerInterface): logger instance. If omitted, then console.log will be used
* `privateKey`: the 64 length private key generated by secp256k1 standard. Please take a look at [example](test/unit/BFT.spec.ts) how key pairs are generated in tests.

### instance.join(multiaddr: string): NodeModel

Add new peer node by uri.

### await instance.append(key: string, value: string, version?: number = 1): Promise<void>

Append new item to local state.

### instance.messageApi.packet(type: number, data: any = null): PacketModel

Create new packet, where ``type`` is packet type, and ``data`` some custom data

### instance.messageApi.decodePacket(message: Buffer): PacketModel

Decode packet from buffer

### await instance.messageApi.message(packet: PacketModel, peerPublicKey: string): Promise<void>

Send message to peer

## Events

A ABGP instance emits the following events (available at ``/components/shared/EventTypes.ts``):

* `JOIN`: once we add new peer
* `LEAVE`: once we remove peer
* `STATE_UPDATE`: emits on each state update
* `STATE_SYNCED`: emits when comparing local and remote state and both states are equal

# Custom transport layer

In order to communicate between nodes, you have to implement the interface by yourself. As an example you can take a look at TCP implementation: ```src/implementation/TCP```.
 In order to write your own implementation you have to implement 2 methods:
 
* The ```async initialize()``` function, which fires on ABGP start. This method is useful, when you want to open the connection, for instance, tcp one, or connect to certain message broker like rabbitMQ.

* The ```async write(address: string, packet: Buffer)``` function, which fires each time instance wants to broadcast message to other peer (address param).

Also, keep in mind, that instance doesn't handle the disconnected / dead peers, which means that instance will try to make requests to all presented members in cluster, 
even if they are not available. So, you need to handle it on your own.

# Usage
Please check tests for usage examples

# Implemented protocols out of the box


| Node.js | 
| --- | 
| [TCP](src/implementation/TCP.ts) | 
| [HTTP](src/implementation/RPC.ts) | 


However, you still can implement your own protocol.

# License

[GNU AGPLv3](LICENSE)

# Copyright

Copyright (c) 2018-2021 Egor Zuev
