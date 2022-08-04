/* eslint-disable no-unused-vars */
export interface ILoggerInterface {

  info(text: string): void;
  trace(text: string): void;
  warn(text: string): void;
  error(text: string): void;

}
