export default class Semaphore {
  private readonly currentRequests: any;

  private runningRequests: number;

  private readonly maxConcurrentRequests: number;

  constructor(maxConcurrentRequests = 1) {
    this.currentRequests = [];
    this.runningRequests = 0;
    this.maxConcurrentRequests = maxConcurrentRequests;
  }

  callFunction(fnToCall, ...args) {
    return new Promise((resolve, reject) => {
      this.currentRequests.push({
        resolve,
        reject,
        fnToCall,
        args
      });
      this.tryNext();
    });
  }

  tryNext() {
    if (!this.currentRequests.length) {

    } else if (this.runningRequests < this.maxConcurrentRequests) {
      const {
        resolve, reject, fnToCall, args
      } = this.currentRequests.shift();
      this.runningRequests++;
      const req = fnToCall(...args);
      req.then((res) => resolve(res))
        .catch((err) => reject(err))
        .finally(() => {
          this.runningRequests--;
          this.tryNext();
        });
    }
  }
}
