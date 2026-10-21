import CentralConfigurations.Enumeration.LeadingRowOrders

/-!
# Leading component balances for source mass relations

The interface reads only the diagram of an actual scaled singular limit.
Opposite-color strokes identify leading positions. Closed same-color vertex
sets have zero weighted leading center. All finite incidence hypotheses remain
explicit, so concrete source diagrams can discharge them by kernel reduction.
-/

namespace CentralConfigurations

open scoped Topology BigOperators
open Filter

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ}
  {q : ℕ → ZWSystem ℂ n mass}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  {d : DiagramCode n} (hd : l.diagramCode = d)

include hd

theorem z_force_zero_of_code (i j : Fin n)
    (hc : d.1 (upperIndex i j) = false) : l.z.force i j = 0 := by
  by_cases hij : i = j
  · subst j; exact l.z.diagonal i
  have he : l.diagramCode.1 (upperIndex i j) = false := by rw [hd]; exact hc
  simpa [l.diagramCode_z_entry, OneColorLimit.Incident, hij] using he

theorem w_force_zero_of_code (i j : Fin n)
    (hc : d.2 (upperIndex i j) = false) : l.w.force i j = 0 := by
  by_cases hij : i = j
  · subst j; exact l.w.diagonal i
  have he : l.diagramCode.2 (upperIndex i j) = false := by rw [hd]; exact hc
  simpa [l.diagramCode_w_entry, OneColorLimit.Incident, hij] using he

theorem z_force_ne_zero_of_code (i j : Fin n) (hij : i ≠ j)
    (hc : d.1 (upperIndex i j) = true) : l.z.force i j ≠ 0 := by
  have he : l.diagramCode.1 (upperIndex i j) = true := by rw [hd]; exact hc
  simpa [l.diagramCode_z_entry, OneColorLimit.Incident, hij] using he

theorem w_force_ne_zero_of_code (i j : Fin n) (hij : i ≠ j)
    (hc : d.2 (upperIndex i j) = true) : l.w.force i j ≠ 0 := by
  have he : l.diagramCode.2 (upperIndex i j) = true := by rw [hd]; exact hc
  simpa [l.diagramCode_w_entry, OneColorLimit.Incident, hij] using he

theorem z_position_zero_of_code (i : Fin n)
    (hc : d.1 (upperIndex i i) = false) : l.z.position i = 0 := by
  have he : l.diagramCode.1 (upperIndex i i) = false := by rw [hd]; exact hc
  simpa [l.diagramCode_z_entry, OneColorLimit.Incident] using he

theorem w_position_zero_of_code (i : Fin n)
    (hc : d.2 (upperIndex i i) = false) : l.w.position i = 0 := by
  have he : l.diagramCode.2 (upperIndex i i) = false := by rw [hd]; exact hc
  simpa [l.diagramCode_w_entry, OneColorLimit.Incident] using he

theorem z_position_ne_zero_of_code (i : Fin n)
    (hc : d.1 (upperIndex i i) = true) : l.z.position i ≠ 0 := by
  have he : l.diagramCode.1 (upperIndex i i) = true := by rw [hd]; exact hc
  simpa [l.diagramCode_z_entry, OneColorLimit.Incident] using he

theorem w_position_ne_zero_of_code (i : Fin n)
    (hc : d.2 (upperIndex i i) = true) : l.w.position i ≠ 0 := by
  have he : l.diagramCode.2 (upperIndex i i) = true := by rw [hd]; exact hc
  simpa [l.diagramCode_w_entry, OneColorLimit.Incident] using he

theorem z_position_eq_of_w_code_edge
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (i j : Fin n) (hij : i ≠ j) (hc : d.2 (upperIndex i j) = true) :
    l.z.position i = l.z.position j := by
  have he : l.diagramCode.2 (upperIndex i j) = true := by rw [hd]; exact hc
  have hf : l.w.force i j ≠ 0 := by
    simpa [l.diagramCode_w_entry, OneColorLimit.Incident, hij] using he
  exact l.w_stroke_z_close ha i j hij hf

theorem w_position_eq_of_z_code_edge
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (i j : Fin n) (hij : i ≠ j) (hc : d.1 (upperIndex i j) = true) :
    l.w.position i = l.w.position j := by
  have he : l.diagramCode.1 (upperIndex i j) = true := by rw [hd]; exact hc
  have hf : l.z.force i j ≠ 0 := by
    simpa [l.diagramCode_z_entry, OneColorLimit.Incident, hij] using he
  exact l.z_stroke_w_close ha i j hij hf

theorem z_component_balance_of_code (s : Finset (Fin n))
    (hc : ∀ i ∈ s, ∀ j, j ∉ s → d.1 (upperIndex i j) = false) :
    (∑ i ∈ s, mass i * l.z.position i) = 0 :=
  l.z.component_balance s (fun i hi j hj => l.z_force_zero_of_code hd i j (hc i hi j hj))

theorem w_component_balance_of_code (s : Finset (Fin n))
    (hc : ∀ i ∈ s, ∀ j, j ∉ s → d.2 (upperIndex i j) = false) :
    (∑ i ∈ s, mass i * l.w.position i) = 0 :=
  l.w.component_balance s (fun i hi j hj => l.w_force_zero_of_code hd i j (hc i hi j hj))

end ScaledZWLimit
end CentralConfigurations
