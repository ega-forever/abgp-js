import testSuite from './consensus/testSuite';

describe('consensus tests (3 nodes, TCP, random peer selection, links n-to-n)', () => testSuite({}, 3, 'TCP', true));

describe('consensus tests (4 nodes, TCP, random peer selection, links n-to-n)', () => testSuite({}, 4, 'TCP', true));

describe('consensus tests (5 nodes, TCP, random peer selection, links n-to-n)', () => testSuite({}, 5, 'TCP', true));

describe('consensus tests (3 nodes, TCP, all peers selection, links n-to-n)', () => testSuite({}, 3, 'TCP', false));

describe('consensus tests (4 nodes, TCP, all peers selection, links n-to-n)', () => testSuite({}, 4, 'TCP', false));

describe('consensus tests (5 nodes, TCP, all peer selection, links n-to-n)', () => testSuite({}, 5, 'TCP', false));

describe('consensus tests (3 nodes, RPC, random peer selection, links n-to-n)', () => testSuite({}, 3, 'RPC', true));

describe('consensus tests (4 nodes, RPC, random peer selection, links n-to-n)', () => testSuite({}, 4, 'RPC', true));

describe('consensus tests (5 nodes, RPC, random peer selection, links n-to-n)', () => testSuite({}, 5, 'RPC', true));

describe('consensus tests (3 nodes, RPC, all peers selection, links n-to-n)', () => testSuite({}, 3, 'RPC', false));

describe('consensus tests (4 nodes, RPC, all peers selection, links n-to-n)', () => testSuite({}, 4, 'RPC', false));

describe('consensus tests (5 nodes, RPC, all peer selection, links n-to-n)', () => testSuite({}, 5, 'RPC', false));

describe('consensus tests (3 nodes, TCP, random peer selection, links m-to-n, links >= 2f+1)', () => testSuite(
  {},
  3,
  'TCP',
  true,
  new Map<number, number[]>([
    [0, [0, 1]],
    [1, [1, 0, 2]],
    [2, [2, 1]]
  ])
));

describe('consensus tests (4 nodes, TCP, random peer selection, links m-to-n, links >= 2f+1)', () => testSuite(
  {},
  4,
  'TCP',
  true,
  new Map<number, number[]>([
    [0, [0, 1, 2]],
    [1, [1, 0, 3]],
    [2, [2, 0, 3]],
    [3, [3, 1, 2]]
  ])
));

describe('consensus tests (5 nodes, TCP, random peer selection, links m-to-n, links >= 2f+1)', () => testSuite(
  {},
  5,
  'TCP',
  true,
  new Map<number, number[]>([
    [0, [0, 1, 2]],
    [1, [1, 0, 3]],
    [2, [2, 0, 4]],
    [3, [3, 4, 2]],
    [4, [4, 3, 1, 2]]
  ])
));
