"use strict";
Object.defineProperty(exports, "__esModule", { value: true });
class PlainStorageRecord {
    constructor() {
        this.db = new Map();
    }
    async get(hash) {
        const item = this.db.get(hash);
        if (!item) {
            return null;
        }
        return item.cloneObject();
    }
    async save(record) {
        this.db.set(record.hash, record.cloneObject());
    }
    async has(hash) {
        return this.db.has(hash);
    }
    async getByTimestamp(timestamp) {
        return [...this.db.values()]
            .filter((v) => v.timestamp === timestamp)
            .map((item) => item.cloneObject());
    }
    async getAfterTimestamp(timestamp, timestampIndex, limit) {
        return [...this.db.values()]
            .filter((v) => v.timestamp > timestamp ||
            (v.timestamp === timestamp && v.timestampIndex > timestampIndex))
            .sort((a, b) => ((a.timestamp > b.timestamp ||
            (a.timestamp === b.timestamp && a.timestampIndex > b.timestampIndex)) ? 1 : -1))
            .slice(0, limit)
            .map((item) => item.cloneObject());
    }
    async del(hash) {
        this.db.delete(hash);
    }
}
class PlainStorageState {
    constructor() {
        this.db = new Map();
    }
    async get(publicKey) {
        const state = this.db.get(publicKey);
        if (!state) {
            return {
                timestamp: 0,
                timestampIndex: -1,
                root: '0',
                publicKey
            };
        }
        return state;
    }
    async save(state) {
        this.db.set(state.publicKey, state);
    }
}
class PlainStorage {
    constructor() {
        this.Record = new PlainStorageRecord();
        this.State = new PlainStorageState();
    }
}
exports.default = PlainStorage;
//# sourceMappingURL=PlainStorage.js.map