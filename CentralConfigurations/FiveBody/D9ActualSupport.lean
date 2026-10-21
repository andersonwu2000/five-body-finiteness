import CentralConfigurations.FiveBody.D9DiagramIdentity

/-!
# Actual leading support consequences of the exact AK D9 code

These consequences use the definition of an actual leading diagram and its
proved force equations. The existence of the D9 scale-order alternative is
not assumed or concluded here. In particular, a w-stroke alone does not make
its same-color projected separation maximal.
-/

namespace CentralConfigurations
namespace FiveBody.D9Bridge
open scoped BigOperators Topology
open Filter

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass} {a : ℕ → ℂ}

theorem z_matrix (l : ScaledZWLimit q a) (hd : l.diagramCode = akD9Diagram) :
    l.z.matrix = BinaryMatrixCode.decode akD9Diagram.1 := by
  have henc := congrArg Prod.fst hd
  change BinaryMatrixCode.encode l.z.matrix = akD9Diagram.1 at henc
  rw [← henc]
  exact (BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm).symm

theorem w_matrix (l : ScaledZWLimit q a) (hd : l.diagramCode = akD9Diagram) :
    l.w.matrix = BinaryMatrixCode.decode akD9Diagram.2 := by
  have henc := congrArg Prod.snd hd
  change BinaryMatrixCode.encode l.w.matrix = akD9Diagram.2 at henc
  rw [← henc]
  exact (BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm).symm

theorem z_positions_zero (l : ScaledZWLimit q a) (hd : l.diagramCode = akD9Diagram)
    (i : Fin 5) : l.z.position i = 0 := by
  have hm : l.z.matrix i i = 0 := by rw [z_matrix l hd, akD9_z_support]; simp
  simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hm

theorem w_positions_ne_zero (l : ScaledZWLimit q a) (hd : l.diagramCode = akD9Diagram)
    (i : Fin 5) : l.w.position i ≠ 0 := by
  have hm : l.w.matrix i i = 1 := by rw [w_matrix l hd, akD9_w_support]; simp
  simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hm

theorem triangle_z_force_ne_zero (l : ScaledZWLimit q a)
    (hd : l.diagramCode = akD9Diagram) (i j : Fin 5)
    (hi : i < 3) (hj : j < 3) (hij : i ≠ j) : l.z.force i j ≠ 0 := by
  have hm : l.z.matrix i j = 1 := by
    rw [z_matrix l hd, akD9_z_support]
    simp [hi, hj, hij]
  simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using hm

theorem attachment03_w_force_ne_zero (l : ScaledZWLimit q a)
    (hd : l.diagramCode = akD9Diagram) : l.w.force 0 3 ≠ 0 := by
  have hm : l.w.matrix 0 3 = 1 := by rw [w_matrix l hd, akD9_w_support]; decide
  simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hm

theorem attachment14_w_force_ne_zero (l : ScaledZWLimit q a)
    (hd : l.diagramCode = akD9Diagram) : l.w.force 1 4 ≠ 0 := by
  have hm : l.w.matrix 1 4 = 1 := by rw [w_matrix l hd, akD9_w_support]; decide
  simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hm

theorem outer3_w_force_support (l : ScaledZWLimit q a)
    (hd : l.diagramCode = akD9Diagram) (j : Fin 5) (hj : j ≠ 0) :
    l.w.force 3 j = 0 := by
  by_cases h3j : (3 : Fin 5) = j
  · subst j; exact l.w.diagonal 3
  · have hm : l.w.matrix 3 j = 0 := by
      rw [w_matrix l hd, akD9_w_support]
      simp [h3j, hj, Ne.symm h3j]
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, h3j] using hm

theorem outer4_w_force_support (l : ScaledZWLimit q a)
    (hd : l.diagramCode = akD9Diagram) (j : Fin 5) (hj : j ≠ 1) :
    l.w.force 4 j = 0 := by
  by_cases h4j : (4 : Fin 5) = j
  · subst j; exact l.w.diagonal 4
  · have hm : l.w.matrix 4 j = 0 := by
      rw [w_matrix l hd, akD9_w_support]
      simp [h4j, hj, Ne.symm h4j]
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, h4j] using hm

theorem outer3_w_balance (l : ScaledZWLimit q a) (hd : l.diagramCode = akD9Diagram) :
    l.w.position 3 = mass 0 * l.w.force 3 0 := by
  rw [l.w.balance 3, Finset.sum_eq_single 0]
  · intro j _ hj; rw [outer3_w_force_support l hd j hj, mul_zero]
  · simp

theorem outer4_w_balance (l : ScaledZWLimit q a) (hd : l.diagramCode = akD9Diagram) :
    l.w.position 4 = mass 1 * l.w.force 4 1 := by
  rw [l.w.balance 4, Finset.sum_eq_single 1]
  · intro j _ hj; rw [outer4_w_force_support l hd j hj, mul_zero]
  · simp

theorem inner_w_leading_coincide (l : ScaledZWLimit q a)
    (hd : l.diagramCode = akD9Diagram) (ha : Tendsto a atTop (𝓝 0)) :
    l.w.position 0 = l.w.position 1 ∧ l.w.position 0 = l.w.position 2 := by
  exact ⟨l.z_stroke_w_close ha 0 1 (by decide)
    (triangle_z_force_ne_zero l hd 0 1 (by decide) (by decide) (by decide)),
    l.z_stroke_w_close ha 0 2 (by decide)
      (triangle_z_force_ne_zero l hd 0 2 (by decide) (by decide) (by decide))⟩

/-- At least one attachment is maximal in its same-color leading positions.
This uses the exact center equation and nonzero total mass, not an extra
maximal-edge rule for D9. It does not prescribe the smaller arm's rate. -/
theorem at_least_one_maximal_attachment (l : ScaledZWLimit q a)
    (hd : l.diagramCode = akD9Diagram) (ha : Tendsto a atTop (𝓝 0))
    (htotal : (∑ i, mass i) ≠ 0) :
    l.w.position 3 ≠ l.w.position 0 ∨ l.w.position 4 ≠ l.w.position 1 := by
  by_contra hn
  push Not at hn
  obtain ⟨h01, h02⟩ := inner_w_leading_coincide l hd ha
  have he : ∀ i, l.w.position i = l.w.position 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h01.symm
    · exact h02.symm
    · exact hn.1
    · exact hn.2.trans h01.symm
  have hc := l.w.component_balance Finset.univ (by simp)
  simp_rw [he, ← Finset.sum_mul] at hc
  exact w_positions_ne_zero l hd 0 ((mul_eq_zero.mp hc).resolve_left htotal)

end FiveBody.D9Bridge
end CentralConfigurations
