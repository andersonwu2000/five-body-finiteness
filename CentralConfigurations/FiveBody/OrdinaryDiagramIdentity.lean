import CentralConfigurations.Enumeration.FiveBodySixteen

/-!
# Common-label and color correspondence for AK and Chang diagrams

The masks encode AK Figure 11 and Chang Figure 9. Fin 16 indices equal
the printed AK diagram numbers minus one. The encodings were transcribed
from the inspected source figures; kernel-checked finite identities verify
their correspondence under common relabeling and color exchange.
-/

namespace CentralConfigurations.FiveBody.Ordinary
noncomputable section
attribute [local irreducible] DiagramCode.orbit

def akMasks : Fin 16 → ℕ × ℕ :=
  ![(35,11264),(35,32256),(4713,5667),(11299,11264),(11264,11264),(307,15872),(274,11264),(274,15872),(70,21359),(274,11538),(274,16146),(274,28467),(274,32563),(1230,1230),(1230,22271),(11742,11742)]

def akDiagram (d : Fin 16) : DiagramCode 5 :=
  (BinaryMatrixCode.fromMask 5 (akMasks d).1, BinaryMatrixCode.fromMask 5 (akMasks d).2)

def changIndex : Fin 16 → Fin 20 :=
  ![4,17,19,5,2,18,3,6,11,0,7,9,13,14,15,1]

def toChangLabels : Fin 16 → Fin 5 → Fin 5 :=
  ![![0,1,2,3,4],
    ![2,3,4,0,1],
    ![4,0,1,2,3],
    ![0,1,2,3,4],
    ![0,1,2,3,4],
    ![0,1,4,2,3],
    ![0,1,2,3,4],
    ![2,3,0,1,4],
    ![3,4,2,1,0],
    ![2,3,0,1,4],
    ![2,3,0,1,4],
    ![3,2,0,1,4],
    ![2,3,0,1,4],
    ![4,0,1,2,3],
    ![4,1,2,3,0],
    ![0,1,2,3,4]]

def toAKLabels : Fin 16 → Fin 5 → Fin 5 :=
  ![![0,1,2,3,4],
    ![3,4,0,1,2],
    ![1,2,3,4,0],
    ![0,1,2,3,4],
    ![0,1,2,3,4],
    ![0,1,3,4,2],
    ![0,1,2,3,4],
    ![2,3,0,1,4],
    ![4,3,2,0,1],
    ![2,3,0,1,4],
    ![2,3,0,1,4],
    ![2,3,1,0,4],
    ![2,3,0,1,4],
    ![1,2,3,4,0],
    ![4,1,2,3,0],
    ![0,1,2,3,4]]

def swapColors : Fin 16 → Bool :=
  ![true,false,true,true,false,true,true,false,false,true,false,false,false,false,false,false]

def akToChang (d : Fin 16) : Equiv.Perm (Fin 5) where
  toFun := toChangLabels d
  invFun := toAKLabels d
  left_inv := by
    have h : ∀ k : Fin 16, ∀ i : Fin 5, toAKLabels k (toChangLabels k i) = i := by
      decide +kernel
    exact h d
  right_inv := by
    have h : ∀ k : Fin 16, ∀ i : Fin 5, toChangLabels k (toAKLabels k i) = i := by
      decide +kernel
    exact h d

set_option maxRecDepth 10000 in
theorem ak_to_chang_identity : ∀ d : Fin 16,
    DiagramCode.transform (akDiagram d) (akToChang d) (swapColors d) =
      fiveBodySourceDiagram (changIndex d) := by decide +kernel

set_option maxRecDepth 10000 in
theorem chang_to_ak_identity : ∀ d : Fin 16,
    DiagramCode.transform (fiveBodySourceDiagram (changIndex d))
      (akToChang d).symm (swapColors d) = akDiagram d := by decide +kernel

set_option maxRecDepth 10000 in
theorem chang_indices_exact_survivors :
    Finset.univ.image changIndex = fiveBodyOrderSurvivors := by decide +kernel

end
end CentralConfigurations.FiveBody.Ordinary
