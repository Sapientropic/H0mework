import H0mework.Realization.Perfectification.ScalarEnvelope
import H0mework.Realization.Feature.GramPerfectification

/-!
# Exact-envelope feature continuation

The feature face is a dependent continuation of the existing scalar exact
envelope.  Its source carrier is exactly `P∞`; an actual feature on `P∞`
generates a further Gram-radical quotient and positive readout.  No parallel
perfectification or comparison carrier is introduced.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace SourceGeneratedComplexFeaturePerfectification

open SourceGeneratedScalarPerfectification

noncomputable section

universe c d h

variable {C : Type c} [AddCommGroup C] [Module ℂ C]
variable {D : Type d} [AddCommGroup D] [Module ℂ D]
variable {H : Type h} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (evaluation : C →ₗ[ℂ] Module.Dual ℂ D)

/-- The already generated scalar exact-envelope carrier. -/
abbrev ExactEnvelopeCarrier :=
  SourceGeneratedScalarExactEnvelope.Carrier evaluation

variable (feature : ExactEnvelopeCarrier evaluation →ₗ[ℂ] H)

/-- The dependent feature quotient of the existing exact envelope. -/
abbrev ExactEnvelopeFeatureCarrier := Carrier feature

/-- The original source enters `P∞` and then its dependent feature quotient. -/
def exactEnvelopeFeatureSourceMap :
    C →ₗ[ℂ] ExactEnvelopeFeatureCarrier evaluation feature :=
  (canonicalMap feature).comp
    (SourceGeneratedScalarPerfectification.canonicalMap evaluation)

/-- Faithful feature readback is the original feature evaluated on the
existing exact-envelope source image. -/
theorem faithfulFeature_comp_exactEnvelopeFeatureSourceMap :
    (faithfulFeature feature).comp
        (exactEnvelopeFeatureSourceMap evaluation feature) =
      feature.comp
        (SourceGeneratedScalarPerfectification.canonicalMap evaluation) := by
  rw [exactEnvelopeFeatureSourceMap, ← LinearMap.comp_assoc,
    faithfulFeature_comp_canonicalMap]

@[simp]
theorem faithfulFeature_exactEnvelopeFeatureSourceMap_apply
    (sourceValue : C) :
    faithfulFeature feature
        (exactEnvelopeFeatureSourceMap evaluation feature sourceValue) =
      feature
        (SourceGeneratedScalarPerfectification.canonicalMap
          evaluation sourceValue) := by
  exact LinearMap.congr_fun
    (faithfulFeature_comp_exactEnvelopeFeatureSourceMap evaluation feature)
    sourceValue

/-- Energy zero is exactly feature invisibility on the already generated
`P∞` source image. -/
theorem exactEnvelopeFeature_energy_zero_iff
    (sourceValue : C) :
    positiveEnergyReadout feature
        (exactEnvelopeFeatureSourceMap evaluation feature sourceValue) = 0 ↔
      feature
        (SourceGeneratedScalarPerfectification.canonicalMap
          evaluation sourceValue) = 0 := by
  rw [positiveEnergyReadout_eq_zero_iff]
  constructor
  · intro quotientZero
    have readback := congrArg (faithfulFeature feature) quotientZero
    simpa using readback
  · intro featureZero
    apply faithfulFeature_injective feature
    rw [map_zero]
    simpa using featureZero

end

end SourceGeneratedComplexFeaturePerfectification
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
