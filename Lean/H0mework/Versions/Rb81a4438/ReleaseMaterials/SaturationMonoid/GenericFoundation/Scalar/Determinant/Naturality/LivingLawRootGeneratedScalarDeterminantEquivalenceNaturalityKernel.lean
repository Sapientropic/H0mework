import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarConstantRankDeterminantKernel

/-!
# Scalar determinant equivalence naturality

An actual linear equivalence transports a finite-projective constant-rank
readout, its complete stalk-rank law, and every fixed exterior power.  The
top exterior comparison is therefore generated without choosing a basis,
frame, or determinant trivialization.  Identity, composition, and pure-wedge
readback are literal laws of the same construction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarDeterminantEquivalenceNaturality

open SourceGeneratedScalarConstantRankDeterminant

noncomputable section

universe r m n p

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]
variable {N : Type n} [AddCommGroup N] [Module R N]
variable {P : Type p} [AddCommGroup P] [Module R P]

abbrev ConstantRankReadout (X : Type*) [AddCommGroup X] [Module R X] :=
  SourceGeneratedScalarConstantRankDeterminant.Readout (R := R) (M := X)

/-! ## Complete rank-law transport -/

/-- Linear equivalence identifies the complete stalk-rank profiles. -/
theorem rankProfile_eq (equivalence : M ≃ₗ[R] N) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk (R := R) N :=
  Module.rankAtStalk_eq_of_equiv equivalence

@[simp] theorem rankProfile_eq_refl :
    rankProfile_eq (LinearEquiv.refl R M) = rfl :=
  Subsingleton.elim _ _

theorem rankProfile_eq_trans (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    rankProfile_eq (first.trans second) =
      (rankProfile_eq first).trans (rankProfile_eq second) :=
  Subsingleton.elim _ _

/-- Transport the complete constant-rank readout.  The exterior degree is
preserved literally and the target rank law is derived from the equivalence. -/
noncomputable def transportReadout
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) : ConstantRankReadout (R := R) N where
  finite := by
    letI : Module.Finite R M := readout.finite
    exact Module.Finite.equiv equivalence
  projective := by
    letI : Module.Projective R M := readout.projective
    exact Module.Projective.of_equiv' equivalence
  rank := readout.rank
  constantRank :=
    (rankProfile_eq equivalence).symm.trans readout.constantRank

@[simp] theorem transportReadout_rank
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    (transportReadout readout equivalence).rank = readout.rank :=
  rfl

theorem transportReadout_constantRank
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    Module.rankAtStalk (R := R) N =
      fun _ : PrimeSpectrum R => readout.rank :=
  (transportReadout readout equivalence).constantRank

@[simp] theorem transportReadout_refl
    (readout : ConstantRankReadout (R := R) M) :
    transportReadout readout (LinearEquiv.refl R M) = readout := by
  rfl

theorem transportReadout_trans
    (readout : ConstantRankReadout (R := R) M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    transportReadout (transportReadout readout first) second =
      transportReadout readout (first.trans second) := by
  rfl

/-! ## Frame-free exterior and determinant-line transport -/

/-- Exterior power sends a linear equivalence to a linear equivalence in
every fixed degree. -/
noncomputable def exteriorPowerEquiv (degree : ℕ)
    (equivalence : M ≃ₗ[R] N) :
    (⋀[R]^degree M) ≃ₗ[R] (⋀[R]^degree N) :=
  LinearEquiv.ofLinearMap
    (exteriorPower.map degree equivalence.toLinearMap)
    (exteriorPower.map degree equivalence.symm.toLinearMap)
    (by
      rw [← exteriorPower.map_comp]
      simp)
    (by
      rw [← exteriorPower.map_comp]
      simp)

@[simp] theorem exteriorPowerEquiv_toLinearMap (degree : ℕ)
    (equivalence : M ≃ₗ[R] N) :
    (exteriorPowerEquiv degree equivalence).toLinearMap =
      exteriorPower.map degree equivalence.toLinearMap :=
  rfl

@[simp] theorem exteriorPowerEquiv_apply_ιMulti (degree : ℕ)
    (equivalence : M ≃ₗ[R] N) (vectors : Fin degree → M) :
    exteriorPowerEquiv degree equivalence
        (exteriorPower.ιMulti R degree vectors) =
      exteriorPower.ιMulti R degree (equivalence ∘ vectors) := by
  exact exteriorPower.map_apply_ιMulti equivalence.toLinearMap vectors

@[simp] theorem exteriorPowerEquiv_symm (degree : ℕ)
    (equivalence : M ≃ₗ[R] N) :
    (exteriorPowerEquiv degree equivalence).symm =
      exteriorPowerEquiv degree equivalence.symm := by
  rfl

@[simp] theorem exteriorPowerEquiv_refl (degree : ℕ) :
    exteriorPowerEquiv degree (LinearEquiv.refl R M) =
      LinearEquiv.refl R (⋀[R]^degree M) := by
  apply LinearEquiv.ext
  intro value
  change exteriorPower.map degree (LinearMap.id (R := R) (M := M)) value = value
  rw [exteriorPower.map_id]
  rfl

theorem exteriorPowerEquiv_trans (degree : ℕ)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    exteriorPowerEquiv degree (first.trans second) =
      (exteriorPowerEquiv degree first).trans
        (exteriorPowerEquiv degree second) := by
  apply LinearEquiv.ext
  intro value
  change exteriorPower.map degree
      (second.toLinearMap ∘ₗ first.toLinearMap) value =
    exteriorPower.map degree second.toLinearMap
      (exteriorPower.map degree first.toLinearMap value)
  rw [exteriorPower.map_comp]
  rfl

/-- The top exterior line is transported in the source-generated degree. -/
noncomputable def determinantLineEquiv
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N) :
    readout.determinantLine ≃ₗ[R]
      (transportReadout readout equivalence).determinantLine :=
  exteriorPowerEquiv readout.rank equivalence

@[simp] theorem determinantLineEquiv_apply_ιMulti
    (readout : ConstantRankReadout (R := R) M)
    (equivalence : M ≃ₗ[R] N)
    (vectors : Fin readout.rank → M) :
    determinantLineEquiv readout equivalence
        (exteriorPower.ιMulti R readout.rank vectors) =
      exteriorPower.ιMulti R readout.rank (equivalence ∘ vectors) := by
  exact exteriorPowerEquiv_apply_ιMulti readout.rank equivalence vectors

@[simp] theorem determinantLineEquiv_refl
    (readout : ConstantRankReadout (R := R) M) :
    determinantLineEquiv readout (LinearEquiv.refl R M) =
      LinearEquiv.refl R readout.determinantLine :=
  exteriorPowerEquiv_refl readout.rank

theorem determinantLineEquiv_trans
    (readout : ConstantRankReadout (R := R) M)
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P) :
    determinantLineEquiv readout (first.trans second) =
      (determinantLineEquiv readout first).trans
        (determinantLineEquiv (transportReadout readout first) second) :=
  exteriorPowerEquiv_trans readout.rank first second

end

end SourceGeneratedScalarDeterminantEquivalenceNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
