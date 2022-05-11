const Benchmark: MethodDecorator = (
  target: Object,
  prop: PropertyKey,
  descriptor: PropertyDescriptor
): void => {
  const method: Function = descriptor.value;

  // eslint-disable-next-line no-param-reassign,func-names
  descriptor.value = function (): any {
    // eslint-disable-next-line prefer-rest-params
    const action: Function = method.apply.bind(method, this, arguments);
    const start = Date.now();
    const result: any = action();
    this.abgp.logger.trace(`Benchmark for method [${prop as string}]: ${Date.now() - start}`);
    return result;
  };
};

export default Benchmark;
