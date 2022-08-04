/* eslint-disable import/prefer-default-export */
export const isEqualSet = (as: Set<string>, bs: Set<string>) => {
  if (as.size !== bs.size) {
    return false;
  }

  for (const a of as) {
    if (!bs.has(a)) {
      return false;
    }
  }
  for (const b of bs) {
    if (!as.has(b)) {
      return false;
    }
  }
  return true;
};

export const isSetIncludesAllKeys = (as: Set<string>, bs: Set<string>) => {
  for (const key of as.keys()) {
    if (!bs.has(key)) {
      return false;
    }
  }

  return true;
};
