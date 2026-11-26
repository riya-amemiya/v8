# Lean 4 model and safety proofs for the collection fast paths of `Array.from`

`ArrayFrom` in `src/builtins/array-from.tq` calls
`iterator::FastIterableToList` when it receives a single argument. Besides fast
arrays and strings, which the `ArrayFrom` library covers, that CSA macro in
`src/builtins/builtins-iterator-gen.cc` copies Map key and value iterators,
Set iterators and Sets directly into a new array through `MapIteratorToList`
and `SetOrSetIteratorToList` in `src/builtins/builtins-collections-gen.cc`.
This directory models those two builtins and the branch conditions in front of
them, and proves that the copy never writes outside the new backing store and
produces the live entries of the table in order.

## Files

| File | Contents |
| --- | --- |
| `ArrayFromCollections/Model.lean` | Ordered hash tables, iterators, the copy loops and the branch conditions |
| `ArrayFromCollections/Safety.lean` | Absence of out-of-bounds stores and agreement with the iteration order |
| `ArrayFromCollections/Examples.lean` | Executable `#guard` checks |

## Correspondence with the CSA sources

| Lean | CSA |
| --- | --- |
| `Table` | `OrderedHashMap` and `OrderedHashSet`, with `nof` and `nod` for `NumberOfElements` and `NumberOfDeletedElements` |
| `Slot.hole` | an entry whose key is the hash table hole |
| `nextSkip` | `NextSkipHashTableHoles` |
| `transition`, `transitionAndUpdate` | `TransitionAndUpdate` and the index healing it performs for obsolete tables |
| `storeAt` | the raw `Store(elements, var_offset, ...)` in both copy loops, which has no bounds check |
| `mapIteratorToList` | `MapIteratorToList` |
| `setOrSetIteratorToSet`, `setOrSetIteratorToList` | `SetOrSetIteratorToSet` and `SetOrSetIteratorToList` |
| `mapBranch` | `BranchIfIterableWithOriginalKeyOrValueMapIterator` |
| `setIterBranch`, `setBranch` | `BranchIfIterableWithOriginalValueSetIterator` |
| `fastIterableToList` | the Map and Set part of `FastIterableToList`, after `GotoIfForceSlowPath` and `IsDebugActive` |
| `Iterable.spec` | the values the iterator `next` methods return, skipping deleted entries |

## Theorems

`fastIterableToList_ne_ub`. For every table satisfying `Table.Inv`, the fast
path never stores past the backing store it allocated and never reads past the
used capacity of the table.

`fastIterableToList_spec`. When the fast path succeeds, the result is a
well-formed `PACKED_ELEMENTS` array with holes past its length, its elements
are exactly the values the iterator would have returned, its length is the
number of live entries, and the iterator is left exhausted.

The proofs rest on two facts. The array has `NumberOfElements` slots and the
loops write one slot per live entry, so the stores stay in bounds only when the
used prefix of the table holds exactly `NumberOfElements` live entries.
`Examples.lean` checks that a table whose count is too small makes the copy
store past the end. The copy starts at the iterator index, and both branch
conditions require that index to be 0. `Examples.lean` checks that copying from
a partly consumed iterator would leave a hole at the end of a packed array,
which is why the branches check the index rather than leaving it to the
`CSA_DCHECK` in `MapIteratorToList` and `SetOrSetIteratorToSet`.

## Assumptions

`Table.Inv` states the ordered hash table invariant that `OrderedHashTable`
maintains in `src/objects/ordered-hash-table.cc`: the used capacity
`NumberOfElements + NumberOfDeletedElements` fits in the entry storage, and the
used prefix holds exactly `NumberOfElements` entries whose key is not the hole.

## Not modeled

The fast array, string and interceptor branches of `FastIterableToList`, the
protector cells beyond their boolean value, and the layout of entries inside the
hash table backing store are outside the model.
