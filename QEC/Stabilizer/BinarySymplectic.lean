import QEC.Stabilizer.BinarySymplectic.Core
import QEC.Stabilizer.BinarySymplectic.SymplecticInner
import QEC.Stabilizer.BinarySymplectic.CheckMatrix
import QEC.Stabilizer.BinarySymplectic.IndependentEquiv

/-!
# Binary symplectic representation and check matrix

This module re-exports:

- **Core**: `PauliOperator.toSymplecticSingle`, `NQubitPauliOperator.toSymplectic`
- **SymplecticInner**: `symplecticInner`, `commutes_iff_symplectic_inner_zero`, `toSymplectic_add`
- **CheckMatrix**: `NQubitPauliGroupElement.checkMatrix`, `rowsLinearIndependent`
- **IndependentEquiv**: `listToSet`, `independentGenerators_iff_rowsLinearIndependent`
-/
