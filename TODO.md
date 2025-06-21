1. Rationals
    1. TODO: Currently getting universe resolution errors in Ch4Sec3.
       Seems to be due to the new Induction class for rationals.
       Need to find info on better tooling for looking up argument types.
       Alternatively, just comment out the computational proofs on literals for
       now, and come back to them after getting everything else working?
    1. Use Decidable to avoid long tedious proofs on literals
    1. There seems to be a performance issue resolving `OfScientific` for the
       `Q'` evaluation type (in the `AbsExp` chapter). Or maybe it could be the
       inefficient representation of natural numbers causing issues with values
       like `0.99`. We need to compute a natural value of `100` for that, maybe
       it's a lot of operations?
