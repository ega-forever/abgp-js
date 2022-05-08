export default class Semaphore {
  private readonly currentRequests: any;

  private runningRequests: number;

  private readonly maxConcurrentRequests: number;

  constructor(maxConcurrentRequests = 1) {
    this.currentRequests = [];
    this.runningRequests = 0;
    this.maxConcurrentRequests = maxConcurrentRequests;
  }

  /**
   * Returns a Promise that will eventually return the result of the function passed in
   * Use this to limit the number of concurrent function executions
   * @param {*} fnToCall function that has a cap on the number of concurrent executions
   * @param  {...any} args any arguments to be passed to fnToCall
   * @returns Promise that will resolve with the resolved value as if the function passed in was directly called
   */
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
      const req = Promise.resolve(fnToCall(...args));
      req.then((res) => resolve(res))
        .catch((err) => reject(err))
        .finally(() => {
          this.runningRequests--;
          this.tryNext();
        });
    }
  }
}
