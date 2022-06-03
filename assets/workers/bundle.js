!function(e,t){"object"==typeof exports&&"object"==typeof module?module.exports=t():"function"==typeof define&&define.amd?define([],t):"object"==typeof exports?exports.ABGP=t():e.ABGP=t()}(self,(()=>(()=>{"use strict";var e={187:e=>{var t,s="object"==typeof Reflect?Reflect:null,i=s&&"function"==typeof s.apply?s.apply:function(e,t,s){return Function.prototype.apply.call(e,t,s)};t=s&&"function"==typeof s.ownKeys?s.ownKeys:Object.getOwnPropertySymbols?function(e){return Object.getOwnPropertyNames(e).concat(Object.getOwnPropertySymbols(e))}:function(e){return Object.getOwnPropertyNames(e)};var a=Number.isNaN||function(e){return e!=e};function n(){n.init.call(this)}e.exports=n,e.exports.once=function(e,t){return new Promise((function(s,i){function a(s){e.removeListener(t,n),i(s)}function n(){"function"==typeof e.removeListener&&e.removeListener("error",a),s([].slice.call(arguments))}f(e,t,n,{once:!0}),"error"!==t&&function(e,t,s){"function"==typeof e.on&&f(e,"error",t,{once:!0})}(e,a)}))},n.EventEmitter=n,n.prototype._events=void 0,n.prototype._eventsCount=0,n.prototype._maxListeners=void 0;var r=10;function o(e){if("function"!=typeof e)throw new TypeError('The "listener" argument must be of type Function. Received type '+typeof e)}function p(e){return void 0===e._maxListeners?n.defaultMaxListeners:e._maxListeners}function u(e,t,s,i){var a,n,r,u;if(o(s),void 0===(n=e._events)?(n=e._events=Object.create(null),e._eventsCount=0):(void 0!==n.newListener&&(e.emit("newListener",t,s.listener?s.listener:s),n=e._events),r=n[t]),void 0===r)r=n[t]=s,++e._eventsCount;else if("function"==typeof r?r=n[t]=i?[s,r]:[r,s]:i?r.unshift(s):r.push(s),(a=p(e))>0&&r.length>a&&!r.warned){r.warned=!0;var l=new Error("Possible EventEmitter memory leak detected. "+r.length+" "+String(t)+" listeners added. Use emitter.setMaxListeners() to increase limit");l.name="MaxListenersExceededWarning",l.emitter=e,l.type=t,l.count=r.length,u=l,console&&console.warn&&console.warn(u)}return e}function l(){if(!this.fired)return this.target.removeListener(this.type,this.wrapFn),this.fired=!0,0===arguments.length?this.listener.call(this.target):this.listener.apply(this.target,arguments)}function c(e,t,s){var i={fired:!1,wrapFn:void 0,target:e,type:t,listener:s},a=l.bind(i);return a.listener=s,i.wrapFn=a,a}function h(e,t,s){var i=e._events;if(void 0===i)return[];var a=i[t];return void 0===a?[]:"function"==typeof a?s?[a.listener||a]:[a]:s?function(e){for(var t=new Array(e.length),s=0;s<t.length;++s)t[s]=e[s].listener||e[s];return t}(a):g(a,a.length)}function d(e){var t=this._events;if(void 0!==t){var s=t[e];if("function"==typeof s)return 1;if(void 0!==s)return s.length}return 0}function g(e,t){for(var s=new Array(t),i=0;i<t;++i)s[i]=e[i];return s}function f(e,t,s,i){if("function"==typeof e.on)i.once?e.once(t,s):e.on(t,s);else{if("function"!=typeof e.addEventListener)throw new TypeError('The "emitter" argument must be of type EventEmitter. Received type '+typeof e);e.addEventListener(t,(function a(n){i.once&&e.removeEventListener(t,a),s(n)}))}}Object.defineProperty(n,"defaultMaxListeners",{enumerable:!0,get:function(){return r},set:function(e){if("number"!=typeof e||e<0||a(e))throw new RangeError('The value of "defaultMaxListeners" is out of range. It must be a non-negative number. Received '+e+".");r=e}}),n.init=function(){void 0!==this._events&&this._events!==Object.getPrototypeOf(this)._events||(this._events=Object.create(null),this._eventsCount=0),this._maxListeners=this._maxListeners||void 0},n.prototype.setMaxListeners=function(e){if("number"!=typeof e||e<0||a(e))throw new RangeError('The value of "n" is out of range. It must be a non-negative number. Received '+e+".");return this._maxListeners=e,this},n.prototype.getMaxListeners=function(){return p(this)},n.prototype.emit=function(e){for(var t=[],s=1;s<arguments.length;s++)t.push(arguments[s]);var a="error"===e,n=this._events;if(void 0!==n)a=a&&void 0===n.error;else if(!a)return!1;if(a){var r;if(t.length>0&&(r=t[0]),r instanceof Error)throw r;var o=new Error("Unhandled error."+(r?" ("+r.message+")":""));throw o.context=r,o}var p=n[e];if(void 0===p)return!1;if("function"==typeof p)i(p,this,t);else{var u=p.length,l=g(p,u);for(s=0;s<u;++s)i(l[s],this,t)}return!0},n.prototype.addListener=function(e,t){return u(this,e,t,!1)},n.prototype.on=n.prototype.addListener,n.prototype.prependListener=function(e,t){return u(this,e,t,!0)},n.prototype.once=function(e,t){return o(t),this.on(e,c(this,e,t)),this},n.prototype.prependOnceListener=function(e,t){return o(t),this.prependListener(e,c(this,e,t)),this},n.prototype.removeListener=function(e,t){var s,i,a,n,r;if(o(t),void 0===(i=this._events))return this;if(void 0===(s=i[e]))return this;if(s===t||s.listener===t)0==--this._eventsCount?this._events=Object.create(null):(delete i[e],i.removeListener&&this.emit("removeListener",e,s.listener||t));else if("function"!=typeof s){for(a=-1,n=s.length-1;n>=0;n--)if(s[n]===t||s[n].listener===t){r=s[n].listener,a=n;break}if(a<0)return this;0===a?s.shift():function(e,t){for(;t+1<e.length;t++)e[t]=e[t+1];e.pop()}(s,a),1===s.length&&(i[e]=s[0]),void 0!==i.removeListener&&this.emit("removeListener",e,r||t)}return this},n.prototype.off=n.prototype.removeListener,n.prototype.removeAllListeners=function(e){var t,s,i;if(void 0===(s=this._events))return this;if(void 0===s.removeListener)return 0===arguments.length?(this._events=Object.create(null),this._eventsCount=0):void 0!==s[e]&&(0==--this._eventsCount?this._events=Object.create(null):delete s[e]),this;if(0===arguments.length){var a,n=Object.keys(s);for(i=0;i<n.length;++i)"removeListener"!==(a=n[i])&&this.removeAllListeners(a);return this.removeAllListeners("removeListener"),this._events=Object.create(null),this._eventsCount=0,this}if("function"==typeof(t=s[e]))this.removeListener(e,t);else if(void 0!==t)for(i=t.length-1;i>=0;i--)this.removeListener(e,t[i]);return this},n.prototype.listeners=function(e){return h(this,e,!0)},n.prototype.rawListeners=function(e){return h(this,e,!1)},n.listenerCount=function(e,t){return"function"==typeof e.listenerCount?e.listenerCount(t):d.call(e,t)},n.prototype.listenerCount=d,n.prototype.eventNames=function(){return this._eventsCount>0?t(this._events):[]}},531:function(e,t,s){var i=this&&this.__importDefault||function(e){return e&&e.__esModule?e:{default:e}};Object.defineProperty(t,"__esModule",{value:!0});const a=i(s(998)),n=i(s(227)),r=i(s(905)),o=s(939),p=i(s(269));t.default=class{constructor(e){this.abgp=e,this.semaphore=new p.default(1)}async append(e,t,s=1){return this.semaphore.callFunction(this.appendUnSafe.bind(this),e,t,s)}async appendUnSafe(e,t,s=1){const i=this.abgp.crypto.hash(`${e}:${t}:${s}`);if(await this.abgp.storage.Record.has(i))return;const o=Date.now(),p=(await this.abgp.storage.Record.getByTimestamp(o)).length,u=await this.abgp.crypto.buildPartialSignature(this.abgp.privateKey,i),l=new r.default({hash:i,key:e,value:t,version:s,signaturesMap:new Map([[this.abgp.publicKey,u]]),timestamp:o,timestampIndex:p,signatureType:a.default.INTERMEDIATE,publicKeys:new Set([this.abgp.publicKey])});return await this.saveItem(l),this.abgp.emit(n.default.STATE_UPDATE),i}async remoteAppend(e,t,s){return this.semaphore.callFunction(this.remoteAppendUnsafe.bind(this),e,t,s)}async remoteAppendUnsafe(e,t,s){const i=this.abgp.crypto.hash(`${e.key}:${e.value}:${e.version}`);if(i!==e.hash)return this.abgp.logger.trace(`different hashes for record ${i} vs ${e.hash} on public key ${t.publicKey}`),null;const p=await t.getState();if(e.timestamp<p.timestamp||e.timestamp===p.timestamp&&e.timestampIndex<p.timestampIndex)return this.abgp.logger.trace(`supplied outdated remote record with timestamp ${e.timestamp} vs ${p.timestamp}`),null;let u=await this.abgp.storage.Record.get(i);if(e.signatureType===a.default.INTERMEDIATE)for(const s of e.signaturesMap.keys()){const n=e.signaturesMap.get(s);let r=!1;if(r=u&&u.publicKeys.has(s)?u.signaturesMap.get(s)===n:!(!u||u.signatureType!==a.default.MULTISIG)||await this.abgp.crypto.partialSignatureVerify(n,s,i),!r)return this.abgp.logger.trace(`wrong INTERMEDIATE signature for record ${e.hash} and public key ${t.publicKey}`),null}else{const s=[...e.signaturesMap.keys()][0];let n=!1;if(u&&u.signatureType===a.default.MULTISIG&&[...u.signaturesMap.keys()][0]===s)n=e.signaturesMap.get(s)===u.signaturesMap.get(s);else{if(await this.abgp.crypto.buildSharedPublicKeyX(Array.from(e.publicKeys),i)!==s)return this.abgp.logger.trace(`wrong MULTISIG publickey for record ${e.hash} and public key ${t.publicKey}`),null;const a=e.signaturesMap.get(s);n=await this.abgp.crypto.verify(a,s)}if(!n)return this.abgp.logger.trace(`wrong MULTISIG signature for record ${e.hash} and public key ${t.publicKey}`),null}const l=Date.now(),c=(await this.abgp.storage.Record.getByTimestamp(l)).length;if(u&&u.signatureType===a.default.MULTISIG&&e.signatureType===a.default.INTERMEDIATE||u&&(0,o.isSetIncludesAllKeys)(e.publicKeys,u.publicKeys)||u&&(0,o.isEqualSet)(u.publicKeys,e.publicKeys))return await t.saveState(e.timestamp,e.timestampIndex,s),this.abgp.logger.trace(`update peer node state (record is not updated with hash ${e.hash} and public key ${t.publicKey})`),null;if(u&&u.signatureType===a.default.MULTISIG&&e.signatureType===a.default.MULTISIG){const i=[...u.signaturesMap.keys()][0],a=[...e.signaturesMap.keys()][0];if(i===a||i>a)return await t.saveState(e.timestamp,e.timestampIndex,s),this.abgp.logger.trace(`update peer node state (MULTISIG record is not updated with hash ${e.hash} and public key ${t.publicKey})`),null;const r=e.signaturesMap.get(a);return u.signaturesMap=new Map([[a,r]]),u.publicKeys=new Set(e.publicKeys),u.timestamp=l,u.timestampIndex=c,await this.saveItem(u,t,s,e.timestamp,e.timestampIndex),this.abgp.emit(n.default.STATE_UPDATE),this.abgp.logger.trace(`update peer node state and record (higher MULTISIG signatures) for record with hash ${e.hash} and public key ${t.publicKey})`),null}if(e.signatureType===a.default.MULTISIG){const i=[...e.signaturesMap.keys()][0],o=e.signaturesMap.get(i);return u?(u.timestamp=l,u.timestampIndex=c,u.signaturesMap=new Map([[i,o]]),u.publicKeys=new Set(e.publicKeys),u.signatureType=a.default.MULTISIG):u=new r.default({hash:e.hash,timestamp:l,timestampIndex:c,key:e.key,value:e.value,version:e.version,signaturesMap:new Map(e.signaturesMap),signatureType:a.default.MULTISIG,publicKeys:new Set(e.publicKeys)}),await this.saveItem(u,t,s,e.timestamp,e.timestampIndex),this.abgp.emit(n.default.STATE_UPDATE),this.abgp.logger.trace(`save MULTISIG record (no local record exist) with hash ${e.hash} and public key ${t.publicKey})`),null}if(u){for(const t of e.signaturesMap.keys()){const s=e.signaturesMap.get(t);u.signaturesMap.set(t,s),u.publicKeys.add(t)}u.timestamp=l,u.timestampIndex=c}else{u=e.cloneObject(),u.timestamp=l,u.timestampIndex=c,u.signatureType=a.default.INTERMEDIATE;const t=await this.abgp.crypto.buildPartialSignature(this.abgp.privateKey,i);u.signaturesMap.set(this.abgp.publicKey,t),u.publicKeys.add(this.abgp.publicKey)}if(u.signaturesMap.size>=this.abgp.majority()){const e=[...u.signaturesMap.keys()].sort().slice(0,this.abgp.majority()),t=e.map((e=>u.signaturesMap.get(e))),s=await this.abgp.crypto.buildSharedPublicKeyX(e,i),n=await this.abgp.crypto.buildSharedSignature(t);u.signaturesMap=new Map([[s,n]]),u.signatureType=a.default.MULTISIG,u.publicKeys=new Set(e)}this.abgp.logger.trace(`save record ${u.signatureType===a.default.MULTISIG?"MULTISIG":"INTERMEDIATE"} with hash ${e.hash} and public key ${t.publicKey})`),await this.saveItem(u,t,s,e.timestamp,e.timestampIndex),this.abgp.emit(n.default.STATE_UPDATE)}async saveItem(e,t,s,i,n){const r=await this.abgp.storage.Record.get(e.hash),o=await this.abgp.getState();o.timestamp>e.timestamp&&this.abgp.logger.trace(`WARNING! downgrade timestamp ${o.timestamp} vs ${e.timestamp}`),e.signatureType===a.default.MULTISIG&&(r&&r.signatureType===a.default.INTERMEDIATE||!r)?(e.stateHash=this.abgp.crypto.math.addMod(o.root,e.hash),await this.abgp.saveState(e.timestamp,e.timestampIndex,e.stateHash)):await this.abgp.saveState(e.timestamp,e.timestampIndex,o.root),await this.abgp.storage.Record.save(e),t&&await t.saveState(i,n,s)}}},690:function(e,t,s){var i=this&&this.__importDefault||function(e){return e&&e.__esModule?e:{default:e}};Object.defineProperty(t,"__esModule",{value:!0});const a=i(s(832));t.default=class{constructor(e){this.abgp=e}async message(e,t){const s=await this.abgp.reqMiddleware(e),i=this.abgp.nodes.get(t),a=await this.abgp.call(i.address,s);return await this.abgp.resMiddleware(a,t)}async packet(e,t=null){const s=await this.abgp.getState();return new a.default(s.root,this.abgp.publicKey,e,s.timestamp,s.timestampIndex,t)}decodePacket(e){return JSON.parse(e)}}},195:function(e,t,s){var i=this&&this.__importDefault||function(e){return e&&e.__esModule?e:{default:e}};Object.defineProperty(t,"__esModule",{value:!0});const a=i(s(227)),n=i(s(782)),r=i(s(822)),o=i(s(690));t.default=class{constructor(e){this.abgp=e,this.messageApi=new o.default(e)}join(e){const t=e.match(/\w+$/).toString();if(this.abgp.publicKey===t)return;const s=new r.default(null,e,this.abgp.storage,this.abgp.crypto);return this.abgp.publicKeys.add(s.publicKey),s.once("end",(()=>this.leave(s.publicKey))),this.abgp.nodes.set(t,s),this.abgp.emit(a.default.NODE_JOIN,s),s}leave(e){const t=this.abgp.nodes.get(e);this.abgp.nodes.delete(e),this.abgp.emit(a.default.NODE_LEAVE,t)}validatePacket(e){return!this.abgp.nodes.has(e.publicKey)||e.lastUpdateTimestamp>Date.now()?null:e}async dataRequest(e){const t=[...this.abgp.publicKeys.keys()].sort();this.abgp.logger.trace(`requesting records for node [${e.publicKey}] with timestamp ${e.lastUpdateTimestamp}`);const s=(await this.abgp.storage.Record.getAfterTimestamp(e.data.lastUpdateTimestamp,e.data.lastUpdateTimestampIndex,this.abgp.batchReplicationSize)).map((e=>e.toPlainObject(t)));return this.messageApi.packet(n.default.DATA_REP,{data:s})}}},227:(e,t)=>{Object.defineProperty(t,"__esModule",{value:!0}),t.default={NODE_JOIN:"JOIN",NODE_LEAVE:"LEAVE",STATE_UPDATE:"STATE_UPDATE",STATE_SYNCED:"STATE_SYNCED"}},782:(e,t)=>{Object.defineProperty(t,"__esModule",{value:!0}),t.default={ERR:10,DATA_REQ:11,DATA_REP:12}},998:(e,t)=>{Object.defineProperty(t,"__esModule",{value:!0}),t.default={INTERMEDIATE:0,MULTISIG:1}},304:function(e,t,s){var i=this&&this.__importDefault||function(e){return e&&e.__esModule?e:{default:e}};Object.defineProperty(t,"__esModule",{value:!0});const a=i(s(690)),n=i(s(195)),r=i(s(782)),o=i(s(905)),p=i(s(227));t.default=class{constructor(e){this.abgp=e,this.messageApi=new a.default(e),this.nodeApi=new n.default(e),this.runBeat=!1}async stopBeat(){this.runBeat=!1}async watchBeat(){for(this.runBeat=!0;this.runBeat;){const e=[],t=[...this.abgp.publicKeys.keys()].sort();if(this.abgp.sendSignalToRandomPeer){const t=this.abgp.nodes.size,s=[...this.abgp.nodes.values()][Math.round(Math.random()*(t-1))];e.push(s)}else e.push(...this.abgp.nodes.values());const s=await Promise.all(e.map((async t=>{const s=await t.getState(),i=await this.messageApi.packet(r.default.DATA_REQ,{lastUpdateTimestamp:s.timestamp,lastUpdateTimestampIndex:s.timestampIndex});let a;try{a=await this.abgp.messageApi.message(i,t.publicKey)}catch(s){return this.abgp.logger.warn(`error peer (${e.length}) not available: ${s.toString()}`),{node:t,root:"0",data:[]}}return s.root===a.root&&s.timestamp===a.lastUpdateTimestamp&&s.timestampIndex===a.lastUpdateTimestampIndex?(this.abgp.emit(p.default.STATE_SYNCED,a.publicKey),{node:t,root:"0",data:[]}):a.data?{node:t,data:a.data.data.sort(((e,t)=>e.timestamp>t.timestamp||e.timestamp===t.timestamp&&e.timestampIndex>t.timestampIndex?1:-1)),root:a.root}:(this.abgp.logger.trace(`error packet from peer (${e.length}) with type ${a.type}`),{node:t,root:"0",data:[]})})));for(const e of s)for(const s of e.data)await this.abgp.appendApi.remoteAppend(o.default.fromPlainObject(s,t),e.node,e.root);this.abgp.logger.trace(`sent ack signal to peers (${e.length})`);const i=Math.random()*(this.abgp.gossipInterval.max-this.abgp.gossipInterval.min)+this.abgp.gossipInterval.min;await new Promise((e=>setTimeout(e,i)))}}}},935:function(e,t,s){var i=this&&this.__importDefault||function(e){return e&&e.__esModule?e:{default:e}};Object.defineProperty(t,"__esModule",{value:!0});const a=i(s(690)),n=i(s(195)),r=i(s(304)),o=i(s(822)),p=i(s(379)),u=i(s(531));class l extends o.default{constructor(e){if(super(e.privateKey,e.address,e.storage,e.crypto),this.nodes=new Map,this.gossipInterval=e.gossipInterval,this.sendSignalToRandomPeer=e.sendSignalToRandomPeer,this.batchReplicationSize=e.batchReplicationSize||10,this.logger=e.logger||{error:console.log,warn:console.log,info:console.log,trace:console.log},this.majorityAmount=e.majorityAmount,this.reqMiddleware=e.reqMiddleware?e.reqMiddleware:async e=>e,this.resMiddleware=e.resMiddleware?e.resMiddleware:async e=>e,this.gossipCtrl=new r.default(this),this.requestProcessorService=new p.default(this),this.nodeApi=new n.default(this),this.messageApi=new a.default(this),this.appendApi=new u.default(this),this.publicKeys=new Set,e.publicKeys)for(const t of e.publicKeys)this.publicKeys.add(t);this.publicKeys.add(this.publicKey)}connect(){this.gossipCtrl.watchBeat()}majority(){return this.majorityAmount||Math.floor(this.publicKeys.size/2)+1}async disconnect(){await this.gossipCtrl.stopBeat()}async call(e,t){throw new Error("should be implemented!")}}t.default=l},822:(e,t,s)=>{Object.defineProperty(t,"__esModule",{value:!0});const i=s(187);class a extends i.EventEmitter{constructor(e,t,s,i){super(),this.privateKey=e,this.publicKey=t.match(/\w+$/).toString(),this.nodeAddress=t.split(/\w+$/)[0].replace(/\/$/,""),this.storage=s,this.crypto=i}get address(){return this.nodeAddress}async getState(){return await this.storage.State.get(this.publicKey)||{timestamp:0,timestampIndex:-1,root:"0",publicKey:this.publicKey}}async saveState(e,t,s){await this.storage.State.save({timestamp:e,timestampIndex:t,root:s,publicKey:this.publicKey})}}t.default=a},832:(e,t)=>{Object.defineProperty(t,"__esModule",{value:!0}),t.default=class{constructor(e,t,s,i,a,n=null){this.root=e,this.type=s,this.publicKey=t,this.lastUpdateTimestamp=i,this.lastUpdateTimestampIndex=a,this.data=n,this.timestamp=Date.now()}}},905:(e,t)=>{Object.defineProperty(t,"__esModule",{value:!0}),t.RecordModelPlain=void 0;class s{}t.RecordModelPlain=class extends s{};class i extends s{}class a extends i{constructor(e){super(),Object.assign(this,e)}static fromPlainObject(e,t){const s=e.publicKeyMap.toString(2).padStart(t.length,"0").split("").reduce(((e,s,i)=>{if("0"===s)return e;const a=t[i];return e.add(a),e}),new Set);return new a({hash:e.hash,stateHash:e.stateHash,key:e.key,value:e.value,version:e.version,timestamp:e.timestamp,timestampIndex:e.timestampIndex,signaturesMap:new Map(Object.entries(e.signatures)),signatureType:e.signatureType,publicKeys:s})}toPlainObject(e){const t=[...this.signaturesMap.keys()].reduce(((e,t)=>(e[t]=this.signaturesMap.get(t),e)),{}),s=e.map((e=>this.publicKeys.has(e)?1:0)).join("");return{hash:this.hash,stateHash:this.stateHash,key:this.key,value:this.value,version:this.version,timestamp:this.timestamp,timestampIndex:this.timestampIndex,signatures:t,signatureType:this.signatureType,publicKeyMap:parseInt(s,2)}}cloneObject(){return new a({hash:this.hash,stateHash:this.stateHash,key:this.key,value:this.value,version:this.version,timestamp:this.timestamp,timestampIndex:this.timestampIndex,signaturesMap:new Map(this.signaturesMap),signatureType:this.signatureType,publicKeys:new Set(this.publicKeys)})}}t.default=a},379:function(e,t,s){var i=this&&this.__importDefault||function(e){return e&&e.__esModule?e:{default:e}};Object.defineProperty(t,"__esModule",{value:!0});const a=i(s(690)),n=i(s(195)),r=i(s(782));t.default=class{constructor(e){this.messageApi=new a.default(e),this.nodeApi=new n.default(e),this.abgp=e,this.actionMap=new Map,this.actionMap.set(r.default.DATA_REQ,[this.nodeApi.validatePacket.bind(this.nodeApi),this.nodeApi.dataRequest.bind(this.nodeApi)])}async process(e){if(!this.abgp.nodes.get(e.publicKey)||!this.actionMap.has(e.type))return this.abgp.messageApi.packet(r.default.ERR);let t=!1;for(const s of this.actionMap.get(e.type))null!==t&&(t=await s(!1===t?e:t));return t||this.abgp.messageApi.packet(r.default.ERR)}}},269:(e,t)=>{Object.defineProperty(t,"__esModule",{value:!0}),t.default=class{constructor(e=1){this.currentRequests=[],this.runningRequests=0,this.maxConcurrentRequests=e}getLeftRequests(){return this.currentRequests.length}callFunction(e,...t){return new Promise(((s,i)=>{this.currentRequests.push({resolve:s,reject:i,fnToCall:e,args:t}),this.tryNext()}))}tryNext(){if(this.currentRequests.length&&this.runningRequests<this.maxConcurrentRequests){const{resolve:e,reject:t,fnToCall:s,args:i}=this.currentRequests.shift();this.runningRequests++,s(...i).then((t=>e(t))).catch((e=>t(e))).finally((()=>{this.runningRequests--,this.tryNext()}))}}}},939:(e,t)=>{Object.defineProperty(t,"__esModule",{value:!0}),t.isSetIncludesAllKeys=t.isEqualSet=void 0,t.isEqualSet=(e,t)=>{if(e.size!==t.size)return!1;for(const s of e)if(!t.has(s))return!1;for(const s of t)if(!e.has(s))return!1;return!0},t.isSetIncludesAllKeys=(e,t)=>{for(const s of e.keys())if(!t.has(s))return!1;return!0}}},t={};return function s(i){var a=t[i];if(void 0!==a)return a.exports;var n=t[i]={exports:{}};return e[i].call(n.exports,n,n.exports,s),n.exports}(935)})()));