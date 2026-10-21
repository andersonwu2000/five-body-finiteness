import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.Enumeration.NormalizedSearch

/-!
# AK Figure 11 D9 is Chang Figure 9 diagram 12

AK roles 1,2,3 form the double triangle; 14 and 25 are simple w-strokes;
all five vertices are w-circled, none z-circled. Figure
11 (printed p.568), its ninth picture, and §7.5.1.2 (p.570) specify this
support. The exact finite identities below verify its common relabeling to
the Chang masks, with the numbering correspondence made explicit.
-/

namespace CentralConfigurations
namespace FiveBody.D9Bridge
set_option maxRecDepth 10000
attribute [local irreducible] DiagramCode.orbit

def akD9Diagram : DiagramCode 5 :=
  (BinaryMatrixCode.fromMask 5 70, BinaryMatrixCode.fromMask 5 21359)

/-- New AK indices 0..4 are old Chang indices 4,3,2,0,1. -/
def canonicalToAKRoles : Equiv.Perm (Fin 5) where
  toFun i := ![4,3,2,0,1] i
  invFun i := ![3,4,2,1,0] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def akToCanonicalRoles : Equiv.Perm (Fin 5) := canonicalToAKRoles.symm

theorem role_permutations_inverse : canonicalToAKRoles.symm = akToCanonicalRoles := rfl

/-- Source index 11 means Chang's printed diagram 12. No color swap occurs. -/
theorem chang12_to_akD9 :
    DiagramCode.transform (fiveBodySourceDiagram 11) canonicalToAKRoles false = akD9Diagram := by
  decide +kernel

theorem akD9_to_chang12 :
    DiagramCode.transform akD9Diagram akToCanonicalRoles false = fiveBodySourceDiagram 11 := by
  decide +kernel

theorem akD9_mem_chang12_orbit : akD9Diagram ∈ DiagramCode.orbit (fiveBodySourceDiagram 11) :=
  (DiagramCode.mem_orbit_iff _ _).mpr ⟨canonicalToAKRoles, false, chang12_to_akD9⟩

theorem akD9_z_support (i j : Fin 5) :
    BinaryMatrixCode.decode akD9Diagram.1 i j =
      if i ≠ j ∧ i < 3 ∧ j < 3 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem akD9_w_support (i j : Fin 5) :
    BinaryMatrixCode.decode akD9Diagram.2 i j =
      if i = j ∨ (i < 3 ∧ j < 3) ∨
        (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
        (i = 1 ∧ j = 4) ∨ (i = 4 ∧ j = 1) then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem ScaledZWLimit.chang12_relabel_to_akD9 {mass : Fin 5 → ℂ}
    {q : ℕ → ZWSystem ℂ 5 mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hd : l.diagramCode = fiveBodySourceDiagram 11) :
    (l.relabelCanonical canonicalToAKRoles).diagramCode = akD9Diagram := by
  rw [l.diagramCode_relabelCanonical, hd]
  exact chang12_to_akD9

end FiveBody.D9Bridge
end CentralConfigurations
