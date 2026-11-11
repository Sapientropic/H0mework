import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.Contact
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.Source

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKSourceFiniteUpdate
open Complex MeasureTheory BurnolPhysicalState
open OriginalRieszFiniteSource OriginalRieszFiniteColumns
open OriginalKSourceResolventReconstruction OriginalKSourceGramAction OriginalKFixedBoundarySourceFibre
open scoped InnerProductSpace
noncomputable section

/-- Only the original f0 forward/backward primitives remain unevaluated. -/
def contactSourcePrimitive (c : BurnolCompletedMellinCoordinate) (h : ℝ) : Fin 2 → BurnolL2 :=
  ![nativeIntegral (sourceRate c) (regularForcing c 0) h,
    fourierL2 (backwardIntegral (sourceRate c) (regularForcing c 0) h) +
      (2 * sourceRate c) • contactEndpointSource c h]

private theorem contact_source_primitive_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    contactSourcePrimitive c h i = sourcePrimitive c h i := by
  fin_cases i
  · rfl
  · change fourierL2 (backwardIntegral (sourceRate c) (regularForcing c 0) h) +
      (2 * sourceRate c) • contactEndpointSource c h = secondPrimitiveSource c h
    rw [secondPrimitiveSource, contact_primitive_endpoint]

def contactSourceOrbit (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  Complex.exp (-sourceRate c * (h : ℂ)) • regularColumns c i +
    contactSourcePrimitive c h i + burnolMultiplicativeDilation h (jumpColumns i)

/-- Both signed FC integrals are replaced by the actual compact power endpoints. -/
def contactSourceBoundaryColumn (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) : BurnolL2 :=
  pairedMellinTranslationCharacter c.value h • (regularColumns c i + jumpColumns i) -
    (1/2 : ℂ) • (contactSourceOrbit c h i + contactSourceOrbit c (-h) i)

theorem contact_source_column_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i : Fin 2) :
    contactSourceBoundaryColumn c h i = sourceFiniteBoundaryColumn c h i := by
  simp only [contactSourceBoundaryColumn, contactSourceOrbit, contact_source_primitive_actual,
    sourceFiniteBoundaryColumn, sourceFiniteOrbit]

def contactSourceBoundary (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  ∑ i : Fin 2, sourceCoefficients c i • contactSourceBoundaryColumn c h i

theorem contact_source_word_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    contactSourceBoundary c h = sourceFiniteBoundary c h := by
  simp only [contactSourceBoundary, contact_source_column_actual, sourceFiniteBoundary]

def contactSourceGram (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i j : Fin 2) : ℂ :=
  -inner ℂ (regularColumns c i + jumpColumns i) (contactSourceBoundaryColumn c h j)

theorem contact_source_Gram_actual (c : BurnolCompletedMellinCoordinate) (h : ℝ) (i j : Fin 2) :
    sourceFiniteGram c h i j = contactSourceGram c h i j := by
  rw [source_finite_Gram_action, contactSourceGram, contact_source_column_actual]
  rfl

/-- The original physical boundary consumes the endpoint-resolved whole source word. -/
theorem original_boundary_contact_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) :
    (burnolZeroPairedFixedAnnulusBoundary c zero h : BurnolL2) =
      (burnolEvenAmbientProjection (contactSourceBoundary c h) : BurnolL2) := by
  rw [contact_source_word_actual]
  exact original_boundary_forcing_orbit c zero h

/-- Every original diagonal and cross entry uses the resolved source endpoints. -/
theorem original_fixedResidual_contact_Gram (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    burnolPaFixedShiftResidual c zero =
      ∑ i : Fin 2, ∑ j : Fin 2, star (sourceCoefficients c i) * sourceCoefficients c j *
        contactSourceGram c (Real.log stageZeroSonineQ) i j := by
  rw [original_fixedResidual_source_Gram]
  simp only [contact_source_Gram_actual]

/-- The actual residual reads the same complete word, with no FC primitive left as an input. -/
theorem original_fixedResidual_contact_source (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    burnolPaFixedShiftResidual c zero =
      -inner ℂ (generatedK c) (contactSourceBoundary c (Real.log stageZeroSonineQ)) := by
  rw [original_fixedResidual_contact_Gram]
  have kernel : generatedK c =
      ∑ i : Fin 2, sourceCoefficients c i • (regularColumns c i + jumpColumns i) := by
    rw [Fin.sum_univ_two, ←sourceColumns_from_regular_resolvent c 0,
      ←sourceColumns_from_regular_resolvent c 1]
    rfl
  rw [kernel]
  unfold contactSourceBoundary contactSourceGram
  simp only [Fin.sum_univ_two, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, starRingEnd_apply]
  ring

end
end OriginalKSourceFiniteUpdate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
