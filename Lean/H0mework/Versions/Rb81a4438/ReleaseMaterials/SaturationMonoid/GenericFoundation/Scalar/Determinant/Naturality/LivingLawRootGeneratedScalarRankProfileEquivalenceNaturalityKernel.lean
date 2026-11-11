import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarRankComponentDispositionKernel

/-!
# Scalar rank-profile equivalence naturality

Linear equivalence transports the complete stalk-rank profile, every clopen
rank stratum, the constant-rank face, and the two-prime rank-varying residual.
Residual coordinates remain the same actual primes; only their unequal-rank
proof is transported.  Identity and composition hold on the typed data.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarRankProfileEquivalenceNaturality

open SourceGeneratedScalarRankComponentDisposition

noncomputable section

universe r m n p

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]
variable {N : Type n} [AddCommGroup N] [Module R N]
variable {P : Type p} [AddCommGroup P] [Module R P]

/-- Linear equivalence preserves the complete stalk-rank profile. -/
theorem localRank_profile (equivalence : M ≃ₗ[R] N) :
    localRank R M = localRank R N :=
  Module.rankAtStalk_eq_of_equiv equivalence

theorem localRank_apply (equivalence : M ≃ₗ[R] N)
    (prime : PrimeSpectrum R) :
    localRank R M prime = localRank R N prime :=
  congrFun (localRank_profile equivalence) prime

@[simp] theorem localRank_profile_refl :
    localRank_profile (LinearEquiv.refl R M) = rfl :=
  Subsingleton.elim _ _

theorem localRank_profile_trans (first : M ≃ₗ[R] N)
    (second : N ≃ₗ[R] P) :
    localRank_profile (first.trans second) =
      (localRank_profile first).trans (localRank_profile second) :=
  Subsingleton.elim _ _

/-- Each degree stratum is literally the same subset of the fixed spectrum. -/
theorem rankStratum_eq (equivalence : M ≃ₗ[R] N) (degree : ℕ) :
    rankStratum R M degree = rankStratum R N degree := by
  ext prime
  simp only [rankStratum, Set.mem_ofPred_eq]
  rw [localRank_apply equivalence prime]

theorem mem_rankStratum_iff (equivalence : M ≃ₗ[R] N)
    (prime : PrimeSpectrum R) (degree : ℕ) :
    prime ∈ rankStratum R M degree ↔
      prime ∈ rankStratum R N degree := by
  rw [rankStratum_eq equivalence degree]

namespace ConstantFaceTransport

/-- Transport a constant-rank law without selecting a global rank. -/
theorem map (equivalence : M ≃ₗ[R] N)
    (face : ConstantRankBoundedFaceAt R M) :
    ConstantRankBoundedFaceAt R N where
  rank_eq left right :=
    (localRank_apply equivalence left).symm.trans
      ((face.rank_eq left right).trans
        (localRank_apply equivalence right))

@[simp] theorem map_refl (face : ConstantRankBoundedFaceAt R M) :
    map (LinearEquiv.refl R M) face = face :=
  Subsingleton.elim _ _

theorem map_trans (face : ConstantRankBoundedFaceAt R M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    map second (map first face) = map (first.trans second) face :=
  Subsingleton.elim _ _

@[simp] theorem map_symm_map (face : ConstantRankBoundedFaceAt R M)
    (equivalence : M ≃ₗ[R] N) :
    map equivalence.symm (map equivalence face) = face :=
  Subsingleton.elim _ _

end ConstantFaceTransport

namespace ResidualTransport

/-- Transport the actual two-prime residual.  The coordinates are preserved
definitionally. -/
def map (equivalence : M ≃ₗ[R] N)
    (residual : RankVaryingResidualAt R M) :
    RankVaryingResidualAt R N where
  left := residual.left
  right := residual.right
  rank_ne := by
    intro equalRank
    exact residual.rank_ne
      ((localRank_apply equivalence residual.left).trans
        (equalRank.trans
          (localRank_apply equivalence residual.right).symm))

@[simp] theorem map_left (residual : RankVaryingResidualAt R M)
    (equivalence : M ≃ₗ[R] N) :
    (map equivalence residual).left = residual.left :=
  rfl

@[simp] theorem map_right (residual : RankVaryingResidualAt R M)
    (equivalence : M ≃ₗ[R] N) :
    (map equivalence residual).right = residual.right :=
  rfl

@[simp] theorem map_refl (residual : RankVaryingResidualAt R M) :
    map (LinearEquiv.refl R M) residual = residual := by
  cases residual
  rfl

theorem map_trans (residual : RankVaryingResidualAt R M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    map second (map first residual) = map (first.trans second) residual := by
  cases residual
  rfl

@[simp] theorem map_symm_map (residual : RankVaryingResidualAt R M)
    (equivalence : M ≃ₗ[R] N) :
    map equivalence.symm (map equivalence residual) = residual := by
  cases residual
  rfl

/-- The disjoint-clopen-strata law transports with the same coordinates. -/
theorem map_rankStrata_disjoint
    (residual : RankVaryingResidualAt R M)
    (equivalence : M ≃ₗ[R] N)
    (law : Disjoint
      (rankStratum R M (localRank R M residual.left))
      (rankStratum R M (localRank R M residual.right))) :
    Disjoint
      (rankStratum R N (localRank R N (map equivalence residual).left))
      (rankStratum R N (localRank R N (map equivalence residual).right)) := by
  simpa only [map_left, map_right,
    ← localRank_apply equivalence residual.left,
    ← localRank_apply equivalence residual.right,
    ← rankStratum_eq equivalence] using law

/-- The two residual primes remain in different connected components. -/
theorem map_right_not_mem_connectedComponent
    [Module.Finite R M] [Module.Projective R M]
    (residual : RankVaryingResidualAt R M)
    (equivalence : M ≃ₗ[R] N)
    (law : residual.right ∉ connectedComponent residual.left) :
    (map equivalence residual).right ∉
      connectedComponent (map equivalence residual).left := by
  simpa only [map_left, map_right] using law

end ResidualTransport

namespace OutcomeTransport

/-- Transport either dependent rank branch without reclassifying it. -/
def map (equivalence : M ≃ₗ[R] N) :
    BoundedRankOutcomeAt R M → BoundedRankOutcomeAt R N
  | .constant face => .constant (ConstantFaceTransport.map equivalence face)
  | .varying residual => .varying (ResidualTransport.map equivalence residual)

@[simp] theorem map_refl (outcome : BoundedRankOutcomeAt R M) :
    map (LinearEquiv.refl R M) outcome = outcome := by
  cases outcome <;> simp [map]

theorem map_trans (outcome : BoundedRankOutcomeAt R M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    map second (map first outcome) = map (first.trans second) outcome := by
  cases outcome <;> simp [map, ResidualTransport.map_trans]

@[simp] theorem map_symm_map (outcome : BoundedRankOutcomeAt R M)
    (equivalence : M ≃ₗ[R] N) :
    map equivalence.symm (map equivalence outcome) = outcome := by
  rw [map_trans]
  simp

end OutcomeTransport

end


end SourceGeneratedScalarRankProfileEquivalenceNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
