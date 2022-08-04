import CryptoPlain from 'abgp-js-modules-crypto-plain/src';
import CryptoBNElliptic from 'abgp-js-modules-crypto-bnelliptic/src';
import testSuite from './testSuite';

describe('BFT tests (3 nodes, plain crypto)', () => testSuite({} as any, 3, CryptoPlain));

describe('BFT tests (4 nodes, plain crypto)', () => testSuite({} as any, 4, CryptoPlain));

describe('BFT tests (5 nodes, plain crypto)', () => testSuite({} as any, 5, CryptoPlain));

describe('BFT tests (3 nodes, bn + elliptic crypto)', () => testSuite({} as any, 3, CryptoBNElliptic));

describe('BFT tests (4 nodes, bn + elliptic crypto)', () => testSuite({} as any, 4, CryptoBNElliptic));

describe('BFT tests (5 nodes, bn + elliptic crypto)', () => testSuite({} as any, 5, CryptoBNElliptic));
