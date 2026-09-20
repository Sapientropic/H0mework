import H0mework.Realization.Perfectification.IntegralPair
import H0mework.Realization.Determinant.GradedIntegralLine

/-!
# Bounded observation disposition of the exact perfect envelope

The canonical exact envelope is perfect in its source-generated dual-image
category without a finiteness premise.  A particular observation language
`P∞ → O` is then classified independently.  A bijective finite-free chart
generates its integral determinant line and intrinsic unit torsor; every
other case retains the exact observation, finite-nonfree, or nonfinite
representation residual.

No `Finite`, `Free`, perfectness, determinant frame, or branch selector is an
input to `settle`.  Those propositions are tested internally and stored only
in the resulting branch.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace ExactPerfectEnvelopeBoundedDisposition

open SourceGeneratedPerfectification
open SourceGeneratedCanonicalPerfectPair
open SourceGeneratedDualEvaluation
open GradedIntegralDeterminantLine

noncomputable section

universe c d o

variable {C : Type c} {D : Type d} {O : Type o}
variable [AddCommGroup C] [AddCommGroup D] [AddCommGroup O]
variable (evaluation : C →ₗ[ℤ] Module.Dual ℤ D)

/-- Basis-free determinant and unit readout generated after a bounded chart
has been classified as finite-free. -/
structure GeneratedDeterminantReadout : Type (o + 1) where
  private mk ::
  free : Module.Free ℤ O
  finite : Module.Finite ℤ O

namespace GeneratedDeterminantReadout

def generate (free : Module.Free ℤ O) (finite : Module.Finite ℤ O) :
    GeneratedDeterminantReadout (O := O) :=
  ⟨free, finite⟩

abbrev determinantLine (readout : GeneratedDeterminantReadout (O := O)) :=
  let _ : Module.Free ℤ O := readout.free
  let _ : Module.Finite ℤ O := readout.finite
  GradedIntegralDeterminantLine.IntegralTopExteriorLine O

theorem determinantLine_finrank
    (readout : GeneratedDeterminantReadout (O := O)) :
    Module.finrank ℤ readout.determinantLine = 1 := by
  letI : Module.Free ℤ O := readout.free
  letI : Module.Finite ℤ O := readout.finite
  exact GradedIntegralDeterminantLine.integralTopExteriorLine_finrank O

noncomputable def unitTorsor
    (readout : GeneratedDeterminantReadout (O := O)) :
    GradedIntegralDeterminantLine.CanonicalIntegralUnitTorsor
      readout.determinantLine := by
  letI : Module.Free ℤ O := readout.free
  letI : Module.Finite ℤ O := readout.finite
  exact GradedIntegralDeterminantLine.canonicalIntegralUnitTorsor
    readout.determinantLine_finrank

end GeneratedDeterminantReadout

inductive Disposition
    (observation : Carrier evaluation →ₗ[ℤ] O) :
    Type (max c d o + 2) where
  | determinantEligible
      (equivalence : Carrier evaluation ≃ₗ[ℤ] O)
      (readout : GeneratedDeterminantReadout (O := O))
  | finiteNonfree
      (equivalence : Carrier evaluation ≃ₗ[ℤ] O)
      (finite : Module.Finite ℤ O)
      (notFree : ¬ Module.Free ℤ O)
  | representationResidual
      (equivalence : Carrier evaluation ≃ₗ[ℤ] O)
      (notFinite : ¬ Module.Finite ℤ O)
  | observationResidual
      (outcome : EvaluationDispositionOutcome observation)

/-- Total bounded-language classifier.  The exact envelope itself remains
perfect in every branch. -/
noncomputable def settle
    (observation : Carrier evaluation →ₗ[ℤ] O) :
    Disposition evaluation observation := by
  classical
  exact match SourceGeneratedPerfectification.settleFiniteObservation observation with
    | .bounded equivalence =>
        if finite : Module.Finite ℤ O then
          if free : Module.Free ℤ O then
            .determinantEligible equivalence
              (GeneratedDeterminantReadout.generate free finite)
          else .finiteNonfree equivalence finite free
        else .representationResidual equivalence finite
    | .residual outcome => .observationResidual outcome

theorem disposition_total
    (observation : Carrier evaluation →ₗ[ℤ] O) :
    Nonempty (Disposition evaluation observation) :=
  ⟨settle evaluation observation⟩

theorem settle_eq_determinantEligible
    (observation : Carrier evaluation →ₗ[ℤ] O)
    (equivalence : Carrier evaluation ≃ₗ[ℤ] O)
    (observationOutcome :
      SourceGeneratedPerfectification.settleFiniteObservation observation =
        .bounded equivalence)
    (free : Module.Free ℤ O)
    (finite : Module.Finite ℤ O) :
    settle evaluation observation =
      .determinantEligible equivalence
        (GeneratedDeterminantReadout.generate free finite) := by
  rw [settle, observationOutcome]
  simp [free, finite]

theorem settle_eq_representationResidual
    (observation : Carrier evaluation →ₗ[ℤ] O)
    (equivalence : Carrier evaluation ≃ₗ[ℤ] O)
    (observationOutcome :
      SourceGeneratedPerfectification.settleFiniteObservation observation =
        .bounded equivalence)
    (notFinite : ¬ Module.Finite ℤ O) :
    settle evaluation observation =
      .representationResidual equivalence notFinite := by
  rw [settle, observationOutcome]
  simp [notFinite]

theorem settle_eq_observationResidual
    (observation : Carrier evaluation →ₗ[ℤ] O)
    (outcome : EvaluationDispositionOutcome observation)
    (observationOutcome :
      SourceGeneratedPerfectification.settleFiniteObservation observation =
        .residual outcome) :
    settle evaluation observation = .observationResidual outcome := by
  rw [settle, observationOutcome]

end
end ExactPerfectEnvelopeBoundedDisposition
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
