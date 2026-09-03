// Copyright 2026 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// Flags: --allow-natives-syntax --array-numeric-sort

function compareNumeric(a, b) {
  if (Number.isNaN(a)) return Number.isNaN(b) ? 0 : 1;
  if (Number.isNaN(b)) return -1;
  if (a === 0 && b === 0) {
    if (Object.is(a, -0)) return Object.is(b, -0) ? 0 : -1;
    return Object.is(b, -0) ? 1 : 0;
  }
  return a < b ? -1 : a > b ? 1 : 0;
}

function assertNumericSort(input) {
  const expected = input.slice().sort(compareNumeric);
  input.sort();
  assertEquals(expected.length, input.length);
  for (let i = 0; i < expected.length; ++i) {
    if (Number.isNaN(expected[i])) {
      assertTrue(Number.isNaN(input[i]));
    } else {
      assertTrue(Object.is(expected[i], input[i]),
                 `index ${i}: expected ${expected[i]}, got ${input[i]}`);
    }
  }
}

// Small sorting network and insertion-sort paths.
assertNumericSort([2, 10]);
assertNumericSort([3, 20, 1]);
assertNumericSort([9, -3, 20, 1, 0, 8, 7]);
assertNumericSort([3.5, -0, 0, -2.25, NaN, Infinity, -Infinity]);

// Exact insertion/quicksort and quicksort/radix boundaries.
for (const length of [15, 16, 2047, 2048]) {
  const values = [];
  for (let i = 0; i < length; ++i) {
    values.push(((i * 1543) % 4099) - 2049.5);
  }
  assertTrue(%HasDoubleElements(values));
  assertNumericSort(values);
}

// Narrow-range Smis select counting sort.
const countingSmis = [];
for (let i = 0; i < 64; ++i) countingSmis.push((i * 17) % 11 - 5);
assertTrue(%HasSmiElements(countingSmis));
assertNumericSort(countingSmis);

// Hole-free HOLEY_SMI_ELEMENTS is eligible.
const holeFreeHoleySmi = [4, 3, 2, 1];
delete holeFreeHoleySmi[0];
holeFreeHoleySmi[0] = 10;
assertTrue(%HasHoleyElements(holeFreeHoleySmi));
assertNumericSort(holeFreeHoleySmi);

// Hole-free HOLEY_DOUBLE_ELEMENTS is eligible.
const holeFreeHoleyDouble = [4.5, 3.5, 2.5, 1.5];
delete holeFreeHoleyDouble[1];
holeFreeHoleyDouble[1] = 10.5;
assertTrue(%HasDoubleElements(holeFreeHoleyDouble));
assertTrue(%HasHoleyElements(holeFreeHoleyDouble));
assertNumericSort(holeFreeHoleyDouble);

// A real hole falls back to the specification's default string order.
const withHole = [10, , 2];
withHole.sort();
assertEquals(10, withHole[0]);
assertEquals(2, withHole[1]);
assertFalse(Object.hasOwn(withHole, 2));

// A holey length can exceed the elements backing-store capacity.
const sparseSmiTail = [10, 2];
sparseSmiTail.length = 1000;
sparseSmiTail.sort();
assertEquals(10, sparseSmiTail[0]);
assertEquals(2, sparseSmiTail[1]);

const sparseDoubleTail = [10.5, 2.5];
sparseDoubleTail.length = 1000;
sparseDoubleTail.sort();
assertEquals(10.5, sparseDoubleTail[0]);
assertEquals(2.5, sparseDoubleTail[1]);

// Undefined-in-double representations are values, not NaNs.
if (%IsUndefinedDoubleEnabled()) {
  const withUndefined = [3.5, undefined, 2.5];
  assertTrue(%HasDoubleElements(withUndefined));
  withUndefined.sort();
  assertEquals([2.5, 3.5, undefined], withUndefined);
}

// Smi counting-sort range checks must not overflow.
const wideSmis = [];
for (let i = 0; i < 16; ++i) {
  wideSmis.push(i & 1 ? 1073741823 : -1073741824);
}
assertNumericSort(wideSmis);

// Double counting sort retains the observable sign of zero.
const countingDoubles =
    [-0, 0, 2, -1, 1, 2, -1, 0, -0, 2, 1, -1, 0, 2, -0, 1];
assertTrue(%HasDoubleElements(countingDoubles));
assertNumericSort(countingDoubles);

// Quicksort path.
const quickDoubles = [];
for (let i = 0; i < 128; ++i) {
  quickDoubles.push(((i * 997) % 211) - 100.5);
}
quickDoubles[17] = -0;
quickDoubles[91] = 0;
assertTrue(%HasDoubleElements(quickDoubles));
assertNumericSort(quickDoubles);

// Radix path, including infinities, signed zero, and NaNs.
const radixDoubles = [];
for (let i = 0; i < 2052; ++i) {
  radixDoubles.push(((i * 1543) % 4099) - 2049.5);
}
radixDoubles[3] = NaN;
radixDoubles[701] = NaN;
radixDoubles[1100] = -0;
radixDoubles[1101] = 0;
radixDoubles[1800] = Infinity;
radixDoubles[1801] = -Infinity;
assertTrue(%HasDoubleElements(radixDoubles));
assertNumericSort(radixDoubles);

// An explicit compare function always wins.
const explicitCompare = [1, 20, 3];
explicitCompare.sort((a, b) => b - a);
assertEquals([20, 3, 1], explicitCompare);
