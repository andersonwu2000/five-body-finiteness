# Review guide: planar five-body finiteness in Lean

This guide explains the formal statement, the definitions that determine its mathematical meaning, and the commands for checking the proof. It assumes familiarity with central configurations, but no prior knowledge of Lean. The package contains the 385 project modules in the review closure and two Lean review clients. The accompanying manuscript is distributed separately.

Review has two complementary parts: check that the formal definitions and conclusion express the intended theorem, and reproduce the kernel checks. Reading the mathematical proof in the PDF is a further route to assessing the argument; `Paper.lean` connects its numbered statements to formal declarations.

## 1. Lean notation

| Notation | Meaning |

| --- | --- |

| `ℝ`, `ℕ` | The real numbers and natural numbers |

| `Fin n` | The labels $0,\ldots,n-1$ |

| `Fin n → ℝ` | A real vector indexed by those labels |

| `a : A` | A term of type `A`; for a proposition, a proof of that proposition |

| `(hm : P)` | A named hypothesis asserting `P` |

| `∀`, `∃`, `∧` | Universal quantification, existential quantification, conjunction |

| `∑ j, f j` | A sum over all labels |

| `t⁻¹` | Multiplicative inverse, with $0^{-1}=0$ in Lean's real field |

| `Real.sqrt` | The nonnegative real square root |

| `def`, `abbrev` | Definitions of names |

| `noncomputable` | A definition not intended for executable computation; it still has its stated mathematical meaning |

| `structure … where` | Data together with the listed conditions |

| `A × B`, `p.1`, `p.2` | A product and its two projections |

| `Setoid X`, `Quotient s` | An equivalence relation on `X`, and its quotient |

| `Finite X` | The type `X` has finitely many elements |

## 2. The theorem to review

For any fixed five labelled positive masses, the collision-free planar Newtonian central configurations have finitely many classes under translation, rotation, and positive scaling. Equal masses are allowed; labels are retained.

The declaration is in `CentralConfigurations/FiveBody/D2Regular/PositiveFiniteness.lean`:

```lean

theorem CentralConfigurations.FiveBody.finite_physical_classes_of_five_positive_masses

    (m : Fin 5 → ℝ) (hm : ∀ i, 0 < m i) :

    Finite (PhysicalSimilarityClass 5 m)

```

The parameter `m` is an arbitrary mass tuple. Its only hypothesis is `hm`, positivity of every mass. The conclusion concerns the quotient defined below, so reviewing that quotient and the force equations is essential to interpreting the theorem.

## 3. Definitions determining the statement

The following excerpts reproduce the project definitions used in the statement. Standard Lean and Mathlib constructions, such as the real numbers, finite types, and quotients, supply the remaining vocabulary.

### Squared separation

From `CentralConfigurations/Model/Normalized.lean`:

```lean

def squaredSeparation {K : Type*} [CommRing K] {n : ℕ}

    (x y : Fin n → K) (i j : Fin n) : K :=

  (x i - x j) ^ 2 + (y i - y j) ^ 2

```

This is $d_{ij}=(x_i-x_j)^2+(y_i-y_j)^2$. The definition works over any commutative ring; the physical theorem uses real coordinates. Other parts of the proof also use this polynomial over the complex numbers.

### Inverse distance

From `CentralConfigurations/Model/PhysicalCoordinates.lean`:

```lean

noncomputable def physicalInverseDistance {n : ℕ} (x y : Fin n → ℝ) (i j : Fin n) : ℝ :=

  (Real.sqrt (squaredSeparation x y i j))⁻¹

```

For distinct physical points, this is $1/r_{ij}$, where $r_{ij}=\sqrt{d_{ij}}$.

### Physical central configurations

From the same file:

```lean

structure PhysicalCentralConfiguration (n : ℕ) (mass : Fin n → ℝ) where

  x : Fin n → ℝ

  y : Fin n → ℝ

  centerX : ℝ

  centerY : ℝ

  multiplier : ℝ

  separated : ∀ i j, i ≠ j → 0 < squaredSeparation x y i j

  force_x : ∀ i, multiplier * (x i - centerX) =

    ∑ j, mass j * physicalInverseDistance x y i j ^ 3 * (x i - x j)

  force_y : ∀ i, multiplier * (y i - centerY) =

    ∑ j, mass j * physicalInverseDistance x y i j ^ 3 * (y i - y j)

```

An element consists of positions $q_i=(x_i,y_i)$, a point $c$, and a real multiplier $\lambda$, satisfying pairwise separation and

$$\lambda(q_i-c)=\sum_j m_j r_{ij}^{-3}(q_i-q_j).$$

These are the two components of the Newtonian central-configuration equation. The diagonal summand is zero: Lean defines the inverse of zero to be zero, and the coordinate difference also vanishes.

For positive masses and at least two distinct labels, the same file proves that $\lambda>0$ and that $c$ is the mass center (`multiplier_pos`, `centerX_is_mass_center`, and `centerY_is_mass_center`). Thus the free center and multiplier in the definition do not impose an extra restriction. In the five-body theorem the required distinct labels are available.

### Planar similarity

From `CentralConfigurations/Model/PhysicalSimilarity.lean`:

```lean

abbrev PlanarPoints (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def PlanarSimilar {n : ℕ} (p q : PlanarPoints n) : Prop :=

  ∃ s a b tx ty : ℝ, 0 < s ∧ a ^ 2 + b ^ 2 = 1 ∧

    (∀ k, q.1 k = s * (a * p.1 k + b * p.2 k) + tx) ∧

    (∀ k, q.2 k = s * (-b * p.1 k + a * p.2 k) + ty)

```

This says $q_k=sRp_k+t$ for every label, with $s>0$ and

$$R=\begin{pmatrix}a&b\\-b&a\end{pmatrix},\qquad a^2+b^2=1.$$

The matrix is a rotation. The relation preserves labels and does not identify reflections.

### The quotient of physical configurations

From the same file:

```lean

def physicalSimilaritySetoid (n : ℕ) (mass : Fin n → ℝ) :

    Setoid (PhysicalCentralConfiguration n mass) where

  r p q := PlanarSimilar (p.x, p.y) (q.x, q.y)

  iseqv := ⟨fun _ => PlanarSimilar.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

abbrev PhysicalSimilarityClass (n : ℕ) (mass : Fin n → ℝ) :=

  Quotient (physicalSimilaritySetoid n mass)

```

Two physical configurations are equivalent exactly when their positions are similar. The auxiliary center and multiplier are not compared separately. The `iseqv` field supplies proofs of reflexivity, symmetry, and transitivity. `PhysicalSimilarityClass n m` is the resulting quotient.

Finiteness for this quotient also implies finiteness after additionally identifying reflections or permutations of equal-mass labels.

## 4. What kernel checking establishes

Lean checks proof terms against their types. Subject to the correctness of the checking implementation and the accepted foundational axioms, a successful check establishes the formal statement. Human review of the definitions establishes how that statement relates to the intended mathematics.

The axiom inspection below checks which assumptions the declarations depend on. In particular, an admitted proof using `sorry` introduces `sorryAx`, which must not occur in the reported dependencies. The expected dependencies are `propext`, `Classical.choice`, and `Quot.sound`, the standard axioms used here for classical mathematics and quotients.

Checking the correspondence between the PDF's arguments and the formal declarations is a separate reading task. Successful compilation of an index alone does not establish that every informal sentence translates to the listed type.

## 5. Reproduce the verification

Install [elan](https://github.com/leanprover/elan) and Git. The package pins Lean `v4.30.0-rc2` in `lean-toolchain` and Mathlib revision `85e6e1b45ac3992b8b08b789e314e2b2adf4d5c5` in the Lake configuration. Dependency revisions are recorded in `lake-manifest.json`. The first build needs network access to obtain the toolchain and dependencies.

Run these commands from the package root, in a working copy of this repository:

```sh

lake exe cache get

lake build CentralConfigurations

lake env lean Check.lean

lake env lean Paper.lean

lake env leanchecker --fresh CentralConfigurations.FiveBody.D2Regular.PositiveFiniteness

```

`Check.lean` is already included. Its example applies the main theorem to an arbitrary positive mass tuple, and its print commands expose the theorem and inspect the axiom dependencies of the main theorem and selected intermediate declarations. The main theorem's expected axiom output is:

```text

'CentralConfigurations.FiveBody.finite_physical_classes_of_five_positive_masses' depends on axioms: [propext,

 Classical.choice,

 Quot.sound]

```

Any additional axiom requires investigation; `sorryAx` indicates an admitted proof. The final command performs a fresh kernel replay of the theorem module and its dependencies. Each command should finish with exit status zero.

### Recorded run

On 9 October 2026, an AI agent session rebuilt all 385 project modules from an empty project build directory. Pinned dependency caches were reused; all nine dependency working trees were checked as clean and at the manifest revisions. The build, both review clients, and fresh kernel replay completed with exit status zero. The inspected declarations reported only the three axioms above.

The historical source manifest, dependency checks, timings, and logs are retained separately from this distribution. During preparation of this package, all 391 source and configuration files were checked against that manifest and matched. The present publication preparation updated documentation and manuscript context; it did not change the Lean sources or rerun Lean.

## 6. Correspondence with the written proof

The mathematical framework is Albouy–Kaloshin's five-body singular-diagram method, together with the local and global arguments needed here for all positive masses. Chang–Chen's enumeration and order-refinement methods provide the classification route used by the formal development; no six-body finiteness theorem is used.

The classification begins with twenty candidate diagrams and excludes Chang's printed numbers 9, 11, 13, and 17, leaving the sixteen AK types. The formal development proves the required analytic rules, candidate coverage, and order exclusions. It includes arguments originating in AK, including the cluster-origin argument, the torque argument, and collapsed-complement distance estimates. The relevant files include `Asymptotics/ClusterOrigin.lean`, `Diagrams/TraceTwoCubic.lean`, and `Asymptotics/CollapsedComplement.lean`, under `CentralConfigurations/`.

The PDF uses AK's D1–D16 numbering. `CentralConfigurations/FiveBody/OrdinaryDiagramIdentity.lean` proves the correspondence with the other encoding under relabelling and color exchange. Coverage is established in `CentralConfigurations/Enumeration/FiveBodySourceCoverage.lean` and `CentralConfigurations/Enumeration/FiveBodySixteen.lean`. The D9 bounded-four-product assertion in AK Proposition 8 is not a premise; D9 is handled by the physical-potential argument.

`Paper.lean` lists the 19 numbered statements in manuscript order. Some entries involve several formal declarations; the main theorem, finite-potential-values statement, and six-factor bound also have explicitly typed wrappers. Compare the displayed types, hypotheses, and notation when following the index. For Lemma 13.2, the entries include the short-coordinate and short-direction force estimates and the exact torque identity used before deriving equality of the masses.

## 7. Contributions and review status

Anderson Wu coordinated the research and manuscript preparation and serves as corresponding author. AI agents produced the mathematical arguments, formalization, and manuscript, and performed the recorded machine checks. An independent human expert review of the complete argument has not yet been completed.

## 8. Development and circulation

An earlier manuscript and the completed Lean formalization were sent by email to Kuo-Chang Chen for expert feedback on 6 October 2026. The core formal statements and proof code have remained unchanged since then, apart from comments. Later work expanded and polished the manuscript and refined its correspondence index and review documentation. The historical build described above was performed on 9 October; it is a separate event from the earlier circulation.

The manuscript cites the contemporaneous preprints arXiv:2610.13100v2 (Tomar) and arXiv:2610.16107v3 (Chen and Tong). The present argument was developed independently of those works.
