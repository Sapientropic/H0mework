import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Scalar finite-projective rank-component disposition

For a finite projective module, the actual rank datum is the locally constant
function `Module.rankAtStalk M : PrimeSpectrum R → ℕ`.  This classifier
never stores a caller- or classically-chosen global rank.  Its constant branch
stores the stronger pairwise law on all of `Spec R`; its varying branch stores
two actual primes with unequal local ranks.

The clopen rank strata are unions of connected components.  They are not
identified with individual connected components.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarRankComponentDisposition

universe r m

variable (R : Type r) (M : Type m)
variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The actual stalk-local rank profile of the module. -/
noncomputable abbrev localRank : PrimeSpectrum R → ℕ :=
  Module.rankAtStalk (R := R) M

/-- The rank stratum of degree `n`.  One stratum may contain several
connected components. -/
def rankStratum (n : ℕ) : Set (PrimeSpectrum R) :=
  {p | localRank R M p = n}

/-- A legitimate single-degree bounded face is a law on the complete prime
spectrum, not a stored natural number. -/
structure ConstantRankBoundedFaceAt : Prop where
  rank_eq : ∀ p q : PrimeSpectrum R, localRank R M p = localRank R M q

/-- The exact residual when no single-degree bounded face exists. -/
structure RankVaryingResidualAt where
  left : PrimeSpectrum R
  right : PrimeSpectrum R
  rank_ne : localRank R M left ≠ localRank R M right

/-- Exhaustive outcome.  The constant constructor contains no global rank
field, so classical branch selection cannot manufacture rank authority. -/
inductive BoundedRankOutcomeAt where
  | constant (face : ConstantRankBoundedFaceAt R M)
  | varying (residual : RankVaryingResidualAt R M)

variable {R M}

/-- Finite projectivity makes the stalk-rank function locally constant. -/
theorem localRank_isLocallyConstant
    [Module.Finite R M] [Module.Projective R M] :
    IsLocallyConstant (localRank R M) := by
  let _ : Module.FinitePresentation R M :=
    Module.finitePresentation_of_projective R M
  exact Module.isLocallyConstant_rankAtStalk

/-- Only finitely many rank values occur on `Spec R`. -/
theorem localRank_range_finite
    [Module.Finite R M] [Module.Projective R M] :
    (Set.range (localRank R M)).Finite :=
  (localRank_isLocallyConstant (R := R) (M := M)).range_finite

/-- Every actual rank stratum is clopen. -/
theorem rankStratum_isClopen
    [Module.Finite R M] [Module.Projective R M] (n : ℕ) :
    IsClopen (rankStratum R M n) :=
  (localRank_isLocallyConstant (R := R) (M := M)).isClopen_fiber n

/-- Rank is constant on the connected component of every actual prime. -/
theorem localRank_eq_of_mem_connectedComponent
    [Module.Finite R M] [Module.Projective R M]
    (p q : PrimeSpectrum R) (hq : q ∈ connectedComponent p) :
    localRank R M q = localRank R M p :=
  (localRank_isLocallyConstant (R := R) (M := M)).apply_eq_of_isPreconnected
    isPreconnected_connectedComponent hq mem_connectedComponent

/-- Each connected component lies in the actual rank stratum of any one of
its points.  Equality is intentionally not asserted. -/
theorem connectedComponent_subset_rankStratum
    [Module.Finite R M] [Module.Projective R M]
    (p : PrimeSpectrum R) :
    connectedComponent p ⊆ rankStratum R M (localRank R M p) := by
  intro q hq
  exact localRank_eq_of_mem_connectedComponent p q hq

/-- Exact classical dichotomy on the actual rank function.  Classical logic
selects a branch and, in the residual branch, witnesses already forced by
failure of pairwise constancy.  It never selects a global rank. -/
noncomputable def classify : BoundedRankOutcomeAt R M := by
  classical
  by_cases h : ∀ p q : PrimeSpectrum R, localRank R M p = localRank R M q
  · exact .constant ⟨h⟩
  · simp only [not_forall] at h
    let p := Classical.choose h
    let q := Classical.choose (Classical.choose_spec h)
    have hpq := Classical.choose_spec (Classical.choose_spec h)
    exact .varying ⟨p, q, hpq⟩

/-- The two mouths are jointly exhaustive and mutually exclusive.  This
propositional form exposes exactness without eliminating existential proofs
into data. -/
theorem exact_outcome :
    (ConstantRankBoundedFaceAt R M ∨ Nonempty (RankVaryingResidualAt R M)) ∧
      ¬ (ConstantRankBoundedFaceAt R M ∧
        Nonempty (RankVaryingResidualAt R M)) := by
  classical
  constructor
  · by_cases h : ∀ p q : PrimeSpectrum R, localRank R M p = localRank R M q
    · exact Or.inl ⟨h⟩
    · simp only [not_forall] at h
      obtain ⟨p, q, hpq⟩ := h
      exact Or.inr ⟨⟨p, q, hpq⟩⟩
  · rintro ⟨face, ⟨residual⟩⟩
    exact residual.rank_ne (face.rank_eq residual.left residual.right)

namespace ConstantRankBoundedFaceAt

/-- Once a consumer supplies an actual prime, its local rank is a valid
single degree everywhere.  No `Classical.choose` anchor is used. -/
theorem rank_eq_anchor (face : ConstantRankBoundedFaceAt R M)
    (anchor p : PrimeSpectrum R) :
    localRank R M p = localRank R M anchor :=
  face.rank_eq p anchor

/-- The stratum indexed by an explicit anchor covers all of `Spec R`. -/
theorem rankStratum_anchor_eq_univ (face : ConstantRankBoundedFaceAt R M)
    (anchor : PrimeSpectrum R) :
    rankStratum R M (localRank R M anchor) = Set.univ := by
  ext p
  simp only [rankStratum, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
  exact face.rank_eq p anchor

end ConstantRankBoundedFaceAt

namespace RankVaryingResidualAt

/-- Unequal local ranks force the two residual witnesses into different
connected components. -/
theorem right_not_mem_connectedComponent
    [Module.Finite R M] [Module.Projective R M]
    (residual : RankVaryingResidualAt R M) :
    residual.right ∉ connectedComponent residual.left := by
  intro hmem
  exact residual.rank_ne
    (localRank_eq_of_mem_connectedComponent residual.left residual.right hmem).symm

/-- The two witnessed rank strata are disjoint clopen pieces. -/
theorem rankStrata_disjoint
    (residual : RankVaryingResidualAt R M) :
    Disjoint
      (rankStratum R M (localRank R M residual.left))
      (rankStratum R M (localRank R M residual.right)) := by
  rw [Set.disjoint_left]
  intro p hpLeft hpRight
  exact residual.rank_ne (hpLeft.symm.trans hpRight)

/-- No natural number can replace a rank-varying stalk profile. -/
theorem no_global_rank (residual : RankVaryingResidualAt R M) (n : ℕ) :
    ¬ ∀ p : PrimeSpectrum R, localRank R M p = n := by
  intro h
  exact residual.rank_ne ((h residual.left).trans (h residual.right).symm)

/-- In particular, the ambient `Module.finrank R M` cannot be used as a
single-degree law in the varying branch. -/
theorem no_finrank_globalization (residual : RankVaryingResidualAt R M) :
    ¬ ∀ p : PrimeSpectrum R,
      localRank R M p = Module.finrank R M :=
  residual.no_global_rank (Module.finrank R M)

/-- At least one actual stalk exposes any proposed global rank. -/
theorem exists_localRank_ne (residual : RankVaryingResidualAt R M) (n : ℕ) :
    ∃ p : PrimeSpectrum R, localRank R M p ≠ n := by
  by_contra h
  push Not at h
  exact residual.no_global_rank n h

end RankVaryingResidualAt

/-- Finite projectivity supplies topology/component laws while `classify`
supplies the exact constant-or-varying outcome. -/
structure FiniteProjectiveRankComponentDispositionAt
    [Module.Finite R M] [Module.Projective R M] where
  rankLocallyConstant : IsLocallyConstant (localRank R M)
  rankRangeFinite : (Set.range (localRank R M)).Finite
  rankStrataClopen : ∀ n, IsClopen (rankStratum R M n)
  componentLaw : ∀ p : PrimeSpectrum R,
    connectedComponent p ⊆ rankStratum R M (localRank R M p)
  outcome : BoundedRankOutcomeAt R M

/-- Generate the complete disposition from finite projectivity alone. -/
noncomputable def generate
    [Module.Finite R M] [Module.Projective R M] :
    FiniteProjectiveRankComponentDispositionAt (R := R) (M := M) where
  rankLocallyConstant := localRank_isLocallyConstant
  rankRangeFinite := localRank_range_finite
  rankStrataClopen := rankStratum_isClopen
  componentLaw := connectedComponent_subset_rankStratum
  outcome := classify

end SourceGeneratedScalarRankComponentDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
