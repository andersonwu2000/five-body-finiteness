import CentralConfigurations.Enumeration.BinaryMatrices
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Reading finite candidate data from integer masks

Row-major upper-triangular entries occupy successive bits, starting with
the least significant bit. The unused higher bits have no effect. This
constructor only supplies candidate data; finite coverage is a separate proof.
-/

namespace CentralConfigurations.BinaryMatrixCode

open scoped BigOperators

def rowMajorBitIndex {n : ℕ} (p : UpperIndex n) : ℕ :=
  (∑ k ∈ Finset.range p.1.1.val, (n - k)) + (p.1.2.val - p.1.1.val)

def fromMask (n : ℕ) (mask : ℕ) : BinaryMatrixCode n :=
  fun p => mask.testBit (rowMajorBitIndex p)

end CentralConfigurations.BinaryMatrixCode
