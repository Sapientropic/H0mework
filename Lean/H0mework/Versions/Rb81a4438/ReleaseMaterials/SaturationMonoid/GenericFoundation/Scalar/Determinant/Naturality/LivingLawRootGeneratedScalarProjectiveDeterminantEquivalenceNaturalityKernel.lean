import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.LivingLawRootGeneratedScalarProjectiveDeterminantDispositionKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.Naturality.LivingLawRootGeneratedScalarPicardEquivalenceNaturalityKernel
import H0mework.Versions.Rb81a4438.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Determinant.Naturality.LivingLawRootGeneratedScalarRankProfileEquivalenceNaturalityKernel

/-!
# Projective determinant disposition equivalence naturality

The complete finite-projective determinant disposition is transported along
an actual linear equivalence.  Constant-rank data carries its determinant
line and Picard disposition; rank-varying data carries the same two actual
prime coordinates.  Automatic settlement has an equivalence-invariant branch
kind, while the typed transporter preserves all dependent payloads.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedScalarProjectiveDeterminantEquivalenceNaturality

open SourceGeneratedScalarRankComponentDisposition
open SourceGeneratedScalarProjectiveDeterminantDisposition
open SourceGeneratedScalarDeterminantEquivalenceNaturality
open SourceGeneratedScalarPicardEquivalenceNaturality
open SourceGeneratedScalarRankProfileEquivalenceNaturality

noncomputable section

universe r m n p

variable {R : Type r} [CommRing R]
variable {M : Type m} [AddCommGroup M] [Module R M]
variable {N : Type n} [AddCommGroup N] [Module R N]
variable {P : Type p} [AddCommGroup P] [Module R P]

/-- Connected-component containment is invariant because the base spectrum
is fixed and corresponding rank strata are equal. -/
theorem componentLaw_iff (equivalence : M ≃ₗ[R] N)
    (prime : PrimeSpectrum R) :
    connectedComponent prime ⊆
        rankStratum R M (localRank R M prime) ↔
      connectedComponent prime ⊆
        rankStratum R N (localRank R N prime) := by
  rw [SourceGeneratedScalarRankProfileEquivalenceNaturality.localRank_apply
    equivalence prime,
    SourceGeneratedScalarRankProfileEquivalenceNaturality.rankStratum_eq
      equivalence]

section FiniteProjective

variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]

/-- Transport topology, strata, component law, and the dependent rank
outcome without rerunning the classifier. -/
def mapRankComponentDisposition (equivalence : M ≃ₗ[R] N)
    (disposition : FiniteProjectiveRankComponentDispositionAt
      (R := R) (M := M)) :
    FiniteProjectiveRankComponentDispositionAt (R := R) (M := N) where
  rankLocallyConstant := by
    rw [← SourceGeneratedScalarRankProfileEquivalenceNaturality.localRank_profile
      equivalence]
    exact disposition.rankLocallyConstant
  rankRangeFinite := by
    rw [← SourceGeneratedScalarRankProfileEquivalenceNaturality.localRank_profile
      equivalence]
    exact disposition.rankRangeFinite
  rankStrataClopen degree := by
    rw [← SourceGeneratedScalarRankProfileEquivalenceNaturality.rankStratum_eq
      equivalence degree]
    exact disposition.rankStrataClopen degree
  componentLaw prime :=
    (componentLaw_iff equivalence prime).mp
      (disposition.componentLaw prime)
  outcome := OutcomeTransport.map equivalence disposition.outcome

@[simp] theorem mapRankComponentDisposition_refl
    (disposition : FiniteProjectiveRankComponentDispositionAt
      (R := R) (M := M)) :
    mapRankComponentDisposition (LinearEquiv.refl R M) disposition =
      disposition := by
  cases disposition with
  | mk rankLocallyConstant rankRangeFinite rankStrataClopen componentLaw outcome =>
      cases outcome <;> rfl

end FiniteProjective

section FiniteProjectiveComposition

variable [Module.Finite R M] [Module.Projective R M]
variable [Module.Finite R N] [Module.Projective R N]
variable [Module.Finite R P] [Module.Projective R P]

theorem mapRankComponentDisposition_trans
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P)
    (disposition : FiniteProjectiveRankComponentDispositionAt
      (R := R) (M := M)) :
    mapRankComponentDisposition second
        (mapRankComponentDisposition first disposition) =
      mapRankComponentDisposition (first.trans second) disposition := by
  cases disposition with
  | mk rankLocallyConstant rankRangeFinite rankStrataClopen componentLaw outcome =>
      cases outcome <;> rfl

end FiniteProjectiveComposition

/-! ## Complete dependent disposition transport -/

/-- Transport the full determinant disposition.  No constructor payload is
discarded and no frame is selected. -/
noncomputable def transportDisposition (equivalence : M ≃ₗ[R] N) :
    Disposition (R := R) (M := M) → Disposition (R := R) (M := N)
  | .constant readout picard =>
      .constant (transportReadout readout equivalence)
        (transportPicardDisposition readout equivalence picard)
  | .rankVarying residual =>
      .rankVarying (ResidualTransport.map equivalence residual)

/-- Full dependent-disposition transport is unital.  `HEq` is the exact
statement because the constant constructor is indexed by the transported
readout. -/
theorem transportDisposition_refl_heq
    (disposition : Disposition (R := R) (M := M)) :
    HEq (transportDisposition (LinearEquiv.refl R M) disposition)
      disposition := by
  cases disposition with
  | constant readout picard =>
      simp only [transportDisposition]
      have readoutEq := transportReadout_refl readout
      cases readoutEq
      exact heq_of_eq (congrArg (fun value =>
        Disposition.constant readout value) (Subsingleton.elim _ _))
  | rankVarying residual =>
      simp [transportDisposition]

/-- Full dependent-disposition transport composes. -/
theorem transportDisposition_trans_heq
    (first : M ≃ₗ[R] N) (second : N ≃ₗ[R] P)
    (disposition : Disposition (R := R) (M := M)) :
    HEq
      (transportDisposition second (transportDisposition first disposition))
      (transportDisposition (first.trans second) disposition) := by
  cases disposition with
  | constant readout picard =>
      simp only [transportDisposition]
      have readoutEq := transportReadout_trans readout first second
      cases readoutEq
      exact heq_of_eq (congrArg (fun value =>
        Disposition.constant
          (transportReadout readout (first.trans second)) value)
        (Subsingleton.elim _ _))
  | rankVarying residual =>
      simp [transportDisposition, ResidualTransport.map_trans]

/-- The only intentionally forgotten datum in the coarse classifier. -/
inductive BranchKind where
  | constant
  | rankVarying
  deriving DecidableEq

def outcomeBranchKind : BoundedRankOutcomeAt R M → BranchKind
  | .constant _ => .constant
  | .varying _ => .rankVarying

def dispositionBranchKind : Disposition (R := R) (M := M) → BranchKind
  | .constant _ _ => .constant
  | .rankVarying _ => .rankVarying

@[simp] theorem dispositionBranchKind_transport
    (equivalence : M ≃ₗ[R] N)
    (disposition : Disposition (R := R) (M := M)) :
    dispositionBranchKind (transportDisposition equivalence disposition) =
      dispositionBranchKind disposition := by
  cases disposition <;> rfl

/-- Equivalent carriers cannot make the exhaustive rank classifier choose
opposite mouths. -/
theorem outcome_branchKind_eq_of_equiv (equivalence : M ≃ₗ[R] N)
    (source : BoundedRankOutcomeAt R M)
    (target : BoundedRankOutcomeAt R N) :
    outcomeBranchKind source = outcomeBranchKind target := by
  cases source with
  | constant sourceFace =>
      cases target with
      | constant targetFace => rfl
      | varying targetResidual =>
          exfalso
          let sourceResidual :=
            ResidualTransport.map equivalence.symm targetResidual
          exact sourceResidual.rank_ne
            (sourceFace.rank_eq sourceResidual.left sourceResidual.right)
  | varying sourceResidual =>
      cases target with
      | constant targetFace =>
          exfalso
          let targetResidual :=
            ResidualTransport.map equivalence sourceResidual
          exact targetResidual.rank_ne
            (targetFace.rank_eq targetResidual.left targetResidual.right)
      | varying targetResidual => rfl

theorem classify_branchKind_eq (equivalence : M ≃ₗ[R] N) :
    outcomeBranchKind (classify (R := R) (M := M)) =
      outcomeBranchKind (classify (R := R) (M := N)) :=
  outcome_branchKind_eq_of_equiv equivalence _ _

/-- Automatic determinant settlement has invariant branch kind.  Its full
dependent payload is available through `transportDisposition`. -/
theorem settle_branchKind_eq_of_equiv (equivalence : M ≃ₗ[R] N)
    (finiteM : Module.Finite R M) (projectiveM : Module.Projective R M)
    (finiteN : Module.Finite R N) (projectiveN : Module.Projective R N) :
    dispositionBranchKind (settle finiteM projectiveM) =
      dispositionBranchKind (settle finiteN projectiveN) := by
  generalize sourceEquality : settle finiteM projectiveM = source
  cases source with
  | constant readout picard =>
      have targetConstantRank : Module.rankAtStalk N =
          fun _ : PrimeSpectrum R => readout.rank :=
        (Module.rankAtStalk_eq_of_equiv equivalence).symm.trans
          readout.constantRank
      obtain ⟨targetReadout, targetPicard, targetEquality⟩ :=
        settle_constant_of_constantRank finiteN projectiveN readout.rank
          targetConstantRank
      rw [targetEquality]
      rfl
  | rankVarying residual =>
      obtain ⟨targetResidual, targetEquality⟩ :=
        settle_rankVarying_of_residual finiteN projectiveN
          (ResidualTransport.map equivalence residual)
      rw [targetEquality]
      rfl

end

end SourceGeneratedScalarProjectiveDeterminantEquivalenceNaturality
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
