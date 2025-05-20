# Shars

The general shape of the proof looks like the following.

```
  Generally available: Constants, Auxiliary, Utils, Refinement, ListIR
                
  Theta─┐              SpongeSqueeze ─┐
        │                             │
  Rho ──┤                             ├► Sponge 
        │                             │
  Pi ───┼► KeccakP ──► SpongeAbsorb ──┘         
        │                                      
  Chi ──┤                               
        │                                      
  Iota ─┘                         
```

- Generally available theorems
  - `Constants`. Progress specifications and theorems about constants in the code.
  - `Auxiliary`. Proofs about auxiliary constructs in the proofs, such as operations on defined data types.
  - `Utils`. Extensions to the environment, be it in proofs or definitions.
- Step functions: `Theta`, `Rho`, `Pi`, `Chi`, `Iota`, all used to prove `KeccakP`.
- Sponge function: `Sponge`, using `SpongeAbsorb` and `SpongeSqueeze`, to define the artifacts of the verification.

> [!INFO]
> Maybe I could split `Auxiliary` into its own files and rename `Utils` to be `Prelude`, since it's always meant to be included.
