import H0mework.Realization.Observation.Saturation

/-!
# Proposition 295: saturation-rescaled chain complexes

This file proves the reusable algebraic core behind a "saturated Khovanov"
construction.

Khovanov homology is built from a chain complex.  The saturation operation needed
by the framework is not specific to Khovanov: multiply every differential by the
same residual keep-rate `1 - σ`.  For any chain complex over a field:

* the rescaled differentials still square to zero;
* saturation rates compose by the same noisy-OR law as salience;
* if the keep-rate is nonzero, cycles and boundaries are exactly unchanged;
* if the keep-rate is zero, every chain is a cycle and the only boundaries are
  zero.

Thus any concrete Khovanov complex can be fed into this schema later without
reproving the saturation algebra.
-/

noncomputable section

namespace SaturationMonoid.SaturatedChainComplex

/-! ## A minimal sequential chain-complex carrier -/

/-- A homological chain complex over natural-number degrees, represented only by
its differentials and the square-zero law.  The differential `d n` maps degree
`n` chains to degree `n+1` chains; this cochain orientation avoids predecessor
bookkeeping and is enough for the rescaling algebra. -/
@[ext]
structure SequentialChainComplex
    (R : Type*) [Semiring R]
    (C : ℕ → Type*) [∀ n, AddCommMonoid (C n)] [∀ n, Module R (C n)] where
  d : ∀ n : ℕ, C n →ₗ[R] C (n + 1)
  d_comp_d : ∀ n : ℕ, (d (n + 1)).comp (d n) = 0

variable {R : Type*} [Field R]
variable {C : ℕ → Type*}
variable [∀ n, AddCommGroup (C n)] [∀ n, Module R (C n)]

/-- Degree-`n` cycles. -/
def IsCycle (K : SequentialChainComplex R C) (n : ℕ) (x : C n) : Prop :=
  K.d n x = 0

/-- Boundaries landing in degree `n+1`, indexed by their source degree `n`. -/
def IsBoundary (K : SequentialChainComplex R C) (n : ℕ) (x : C (n + 1)) : Prop :=
  ∃ y : C n, K.d n y = x

/-- Rescale every differential by the scalar residual `r`. -/
def rescale (r : R) (K : SequentialChainComplex R C) :
    SequentialChainComplex R C where
  d n := r • K.d n
  d_comp_d n := by
    ext x
    have h : K.d (n + 1) (K.d n x) = 0 := by
      simpa [LinearMap.comp_apply] using
        congrArg (fun f : C n →ₗ[R] C (n + 2) => f x) (K.d_comp_d n)
    simp [LinearMap.comp_apply, h]

/-- Saturate a chain complex by keeping the residual fraction `1 - σ` of every
differential. -/
def saturate (σ : R) (K : SequentialChainComplex R C) :
    SequentialChainComplex R C :=
  rescale (1 - σ) K

/-! ## Square-zero and noisy-OR composition -/

/-- THEOREM 1: rescaling differentials preserves the square-zero law. -/
theorem rescale_d_comp_d
    (r : R) (K : SequentialChainComplex R C) (n : ℕ) :
    ((rescale r K).d (n + 1)).comp ((rescale r K).d n) = 0 :=
  (rescale r K).d_comp_d n

/-- THEOREM 2: rescaling twice multiplies the keep-rates. -/
theorem rescale_compose
    (r₁ r₂ : R) (K : SequentialChainComplex R C) :
    rescale r₂ (rescale r₁ K) = rescale (r₂ * r₁) K := by
  ext n x
  simp [rescale, mul_smul]

/-- THEOREM 3: saturation steps compose by the noisy-OR law. -/
theorem saturate_compose
    (σ₁ σ₂ : R) (K : SequentialChainComplex R C) :
    saturate σ₂ (saturate σ₁ K) =
      saturate (satOrField σ₁ σ₂) K := by
  have hkeep : (1 - σ₂) * (1 - σ₁) = 1 - satOrField σ₁ σ₂ := by
    simp [satOrField]
    ring
  ext n x
  simp [saturate, rescale, smul_smul, hkeep]

/-! ## Nonzero keep-rate preserves cycles and boundaries -/

/-- THEOREM 4: nonzero keep-rate preserves the cycle predicate exactly. -/
theorem isCycle_rescale_iff_of_ne
    {r : R} (hr : r ≠ 0) (K : SequentialChainComplex R C)
    (n : ℕ) (x : C n) :
    IsCycle (rescale r K) n x ↔ IsCycle K n x := by
  unfold IsCycle rescale
  simp [hr]

/-- THEOREM 5: nonzero keep-rate preserves the boundary predicate exactly. -/
theorem isBoundary_rescale_iff_of_ne
    {r : R} (hr : r ≠ 0) (K : SequentialChainComplex R C)
    (n : ℕ) (x : C (n + 1)) :
    IsBoundary (rescale r K) n x ↔ IsBoundary K n x := by
  constructor
  · intro h
    rcases h with ⟨y, hy⟩
    refine ⟨r • y, ?_⟩
    simpa [rescale] using hy
  · intro h
    rcases h with ⟨y, hy⟩
    refine ⟨r⁻¹ • y, ?_⟩
    simp [rescale, hy, hr]

/-- THEOREM 6: nonzero saturation keep-rate preserves cycles. -/
theorem isCycle_saturate_iff_of_keep_ne
    {σ : R} (hkeep : 1 - σ ≠ 0) (K : SequentialChainComplex R C)
    (n : ℕ) (x : C n) :
    IsCycle (saturate σ K) n x ↔ IsCycle K n x :=
  isCycle_rescale_iff_of_ne hkeep K n x

/-- THEOREM 7: nonzero saturation keep-rate preserves boundaries. -/
theorem isBoundary_saturate_iff_of_keep_ne
    {σ : R} (hkeep : 1 - σ ≠ 0) (K : SequentialChainComplex R C)
    (n : ℕ) (x : C (n + 1)) :
    IsBoundary (saturate σ K) n x ↔ IsBoundary K n x :=
  isBoundary_rescale_iff_of_ne hkeep K n x

/-! ## Full saturation collapses the differential -/

/-- THEOREM 8: after zero-rescaling, every chain is a cycle. -/
theorem isCycle_rescale_zero
    (K : SequentialChainComplex R C) (n : ℕ) (x : C n) :
    IsCycle (rescale (0 : R) K) n x := by
  simp [IsCycle, rescale]

/-- THEOREM 9: after zero-rescaling, the boundaries are exactly zero. -/
theorem isBoundary_rescale_zero_iff
    (K : SequentialChainComplex R C) (n : ℕ) (x : C (n + 1)) :
    IsBoundary (rescale (0 : R) K) n x ↔ x = 0 := by
  constructor
  · intro h
    rcases h with ⟨y, hy⟩
    simpa [rescale] using hy.symm
  · intro hx
    refine ⟨0, ?_⟩
    simp [rescale, hx]

/-- THEOREM 10: full saturation (`σ = 1`) makes every chain a cycle. -/
theorem isCycle_saturate_one
    (K : SequentialChainComplex R C) (n : ℕ) (x : C n) :
    IsCycle (saturate (1 : R) K) n x := by
  simpa [saturate] using isCycle_rescale_zero K n x

/-- THEOREM 11: under full saturation (`σ = 1`), boundaries are exactly zero. -/
theorem isBoundary_saturate_one_iff
    (K : SequentialChainComplex R C) (n : ℕ) (x : C (n + 1)) :
    IsBoundary (saturate (1 : R) K) n x ↔ x = 0 := by
  simpa [saturate] using isBoundary_rescale_zero_iff K n x

/-- A bundled certificate for a saturation-rescaled chain-complex family. -/
structure SaturatedChainComplexFamilyCertificate
    (K : SequentialChainComplex R C) where
  family : R → SequentialChainComplex R C := fun σ => saturate σ K
  squareZero : ∀ σ n, ((family σ).d (n + 1)).comp ((family σ).d n) = 0
  compose :
    ∀ σ₁ σ₂,
      saturate σ₂ (family σ₁) =
        family (satOrField σ₁ σ₂)
  cycles_preserved :
    ∀ {σ} (_ : 1 - σ ≠ 0) n x, IsCycle (family σ) n x ↔ IsCycle K n x
  boundaries_preserved :
    ∀ {σ} (_ : 1 - σ ≠ 0) n x, IsBoundary (family σ) n x ↔ IsBoundary K n x
  full_saturation_cycles :
    ∀ n x, IsCycle (family 1) n x
  full_saturation_boundaries :
    ∀ n x, IsBoundary (family 1) n x ↔ x = 0

/-- THEOREM 12: every sequential chain complex has a canonical saturation
family certificate. -/
def saturatedChainComplexFamilyCertificate
    (K : SequentialChainComplex R C) :
    SaturatedChainComplexFamilyCertificate K where
  family := fun σ => saturate σ K
  squareZero := by
    intro σ n
    exact (saturate σ K).d_comp_d n
  compose := by
    intro σ₁ σ₂
    exact saturate_compose σ₁ σ₂ K
  cycles_preserved := by
    intro σ hkeep n x
    exact isCycle_saturate_iff_of_keep_ne hkeep K n x
  boundaries_preserved := by
    intro σ hkeep n x
    exact isBoundary_saturate_iff_of_keep_ne hkeep K n x
  full_saturation_cycles := by
    intro n x
    exact isCycle_saturate_one K n x
  full_saturation_boundaries := by
    intro n x
    exact isBoundary_saturate_one_iff K n x

end SaturationMonoid.SaturatedChainComplex
