import { IRecord, IState, IStorageInterface } from '../../consensus/interfaces/IStorageInterface';
export default class PlainStorage implements IStorageInterface {
    readonly Record: IRecord;
    readonly State: IState;
    constructor();
}
