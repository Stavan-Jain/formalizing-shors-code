import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.CheckMatrix

/-!
# Binary symplectic representation and check matrix

This module re-exports:

- **Core**: `PauliOperator.toSymplecticSingle`, `NQubitPauliOperator.toSymplectic`
- **SymplecticInner**: `symplecticInner`, `commutes_iff_symplectic_inner_zero` (latter has a sorry)
- **CheckMatrix**: `NQubitPauliGroupElement.checkMatrix`, `rowsLinearIndependent`

The equivalence between `Subgroup.IndependentGenerators` and `rowsLinearIndependent` is to be
proved later.
-/
