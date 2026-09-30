import H0mework.Realization.Perfectification.ScalarEnvelope
import H0mework.Arithmetic.Mellin.ProperMellinL1

/-!
# Proper Mellin scalar exact envelope

The actual weighted `L¹` Mellin integral is retained as a complex-linear
evaluation.  The scalar-polymorphic generic producer therefore admits this
analytic carrier without forgetting it to an integral module.  A generated
zero relation lands in the canonical kernel, while the normalized low
correction proves that the evaluation and its exact envelope are nontrivial.

This file does not supply the selected/reversal partner incidence and does
not assert radial-defect vanishing.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ProperMellinScalarEnvelope

open Complex MeasureTheory
open QRich
open SourceGeneratedScalarPerfectification
open SourceGeneratedScalarExactEnvelope

noncomputable section

/-- The actual continuous Mellin integral, curried as a complex-linear dual
evaluation.  No coefficient-forgetting adapter occurs here. -/
def evaluation : PositiveMellinL1 →ₗ[ℂ] Module.Dual ℂ ℂ :=
  (LinearMap.mul ℂ ℂ).comp positiveMellinL1Integral.toLinearMap

@[simp] theorem evaluation_apply_one (value : PositiveMellinL1) :
    evaluation value 1 = positiveMellinL1Integral value := by
  simp [evaluation]

abbrev Carrier :=
  SourceGeneratedScalarPerfectification.PerfectificationCarrier evaluation

abbrev GeneratedDual :=
  SourceGeneratedScalarExactEnvelope.GeneratedDual evaluation

def exactEnvelope :
    SourceGeneratedScalarExactEnvelope.UniversalPerfectEnvelope evaluation :=
  SourceGeneratedScalarExactEnvelope.sourceGeneratedPerfectification evaluation

theorem exactEnvelope_total :
    Nonempty
      (SourceGeneratedScalarExactEnvelope.UniversalPerfectEnvelope evaluation) :=
  SourceGeneratedScalarExactEnvelope.universalPerfectEnvelope_total evaluation

/-- The source-generated zero relation is a literal kernel coordinate of the
actual proper-`L¹` evaluation. -/
theorem selectedElement_mem_kernel
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    generatedZeroSelectedMellinL1Element observation nontrivial ∈
      LinearMap.ker evaluation := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro scalar
  simp [evaluation,
    generatedZeroSelectedMellinL1Element_integral_zero
      observation nontrivial]

theorem selectedElement_maps_to_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    canonicalMap evaluation
        (generatedZeroSelectedMellinL1Element observation nontrivial) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).2
    (selectedElement_mem_kernel observation nontrivial)

/-- A source-owned normalized low element reads `1`; hence the complex
evaluation admitted above is not an empty or zero envelope. -/
theorem scaledLow_evaluation_one
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    evaluation
        ((observation.coordinate / 2 : ℂ) •
          generatedZeroSelectedNormalizedLowMellinL1Element
            observation nontrivial) 1 = 1 := by
  rw [evaluation_apply_one]
  exact
    generatedZeroSelectedNormalizedLowMellinL1Element_scaled_integral_one
      observation nontrivial

theorem evaluation_ne_zero
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    evaluation ≠ 0 := by
  intro evaluationZero
  have evaluated := congrArg
    (fun actualEvaluation =>
      actualEvaluation
        ((observation.coordinate / 2 : ℂ) •
          generatedZeroSelectedNormalizedLowMellinL1Element
            observation nontrivial) 1)
    evaluationZero
  rw [scaledLow_evaluation_one observation nontrivial] at evaluated
  simp at evaluated

theorem generatedDual_nontrivial
    {owner : GlobalGermOwner}
    (observation : GeneratedRiemannZeroObservationAt owner)
    (nontrivial :
      ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1)) :
    Nontrivial GeneratedDual := by
  rw [nontrivial_iff]
  let low : PositiveMellinL1 :=
    (observation.coordinate / 2 : ℂ) •
      generatedZeroSelectedNormalizedLowMellinL1Element
        observation nontrivial
  let generated : GeneratedDual :=
    SourceGeneratedScalarExactEnvelope.generatedDualMap evaluation
      (canonicalMap evaluation low)
  refine ⟨0, generated, ?_⟩
  intro equality
  have sourceReadback := LinearMap.congr_fun
    (SourceGeneratedScalarExactEnvelope.source_evaluation_readback evaluation)
    low
  have atOne := congrArg (fun functional => functional 1) sourceReadback
  change
    SourceGeneratedScalarExactEnvelope.dualInclusion evaluation generated 1 =
      evaluation low 1 at atOne
  rw [← equality] at atOne
  change 0 = evaluation low 1 at atOne
  rw [scaledLow_evaluation_one observation nontrivial] at atOne
  exact zero_ne_one atOne

end
end ProperMellinScalarEnvelope
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
