import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.RecipeInverse
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCrossAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.PaCoefficientSourceGramConsumer

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceJointContact.PaCoefficientPrice
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.KappaConductor
open OriginalKDirectRCofinalOutsideVolterraSource
open PaCoefficientSourceGram PaCoefficientSourceGramConsumer
open scoped InnerProductSpace Topology BigOperators
open private annulus_pair from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.KSourceEnergy
local instance : DecidableEq Index := Classical.decEq _
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "A" => sourceAnnulusCut
local notation "V" => sourceVolterraResolvent

/-- The bill uses the original recipe source and its generated Gram coefficients. -/
def generatorBill (c : BurnolCompletedMellinCoordinate) (i : Index) : ℂ :=
  inner ℂ (A (originalDualLogValue c)) (sigmaGenerator i)
def finiteGammaBill (c : BurnolCompletedMellinCoordinate) (F : Finset Index) : ℂ :=
  ∑ i : ↥F, finiteCoefficients c F i * generatorBill c i.1

theorem actual_generator_Gamma_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (i : Index) :
    inner ℂ (actualGammaKernel c) (burnolCompactCoPoissonGenerator i : BurnolL2) =
      generatorBill c i := by
  have paid := PaCrossAction.actual_original_Gamma_Pa_cross_source c zero
    ((RecipeInverse.inverseSource c (recipe i)).1.toLp 2 volume)
    (RecipeInverse.compact_source_even _)
  rw [RecipeInverse.sourceVolterraPhysical_inverse] at paid
  have cut := annulus_pair (A (originalDualLogValue c))
    (V c (A ((RecipeInverse.inverseSource c (recipe i)).1.toLp 2 volume)))
  rw [sourceAnnulusCut_idempotent] at cut
  rw [cut, RecipeInverse.compact_source_supported] at paid
  change inner ℂ (actualGammaKernel c) (burnolCompactAdditivePhysicalState (recipe i) : BurnolL2) =
    inner ℂ (A (originalDualLogValue c))
      (sourceVolterraWindow c ((RecipeInverse.inverseSource c (recipe i)).1.toLp 2 volume)) at paid
  rw [RecipeInverse.sourceVolterraWindow_inverse] at paid
  simpa only [generator_recipe, generatorBill, sigmaGenerator] using paid

private theorem finite_physical_read (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    Hilbert.hilbertAmbientRealizationCLM burnolCompactCoPoissonLanding (finiteHilbert c F) =
      physicalSynthesis F (finiteCoefficients c F) := by
  change SourceGeneratedComplexFeaturePerfectification.hilbertAmbientRealization
    burnolCompactCoPoissonLanding (finiteHilbert c F) = _
  rw [finiteHilbert, FG.source_effect_eq]
  exact Hilbert.hilbertAmbientRealization_source_readback burnolCompactCoPoissonLanding _

theorem finite_Gamma_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (F : Finset Index) :
    inner ℂ (actualGammaKernel c)
      (Hilbert.hilbertAmbientRealizationCLM burnolCompactCoPoissonLanding (finiteHilbert c F) : BurnolL2) =
        finiteGammaBill c F := by
  rw [finite_physical_read, physical_synthesis_read]
  simp only [Submodule.coe_sum, Submodule.coe_smul, inner_sum, inner_smul_right,
    actual_generator_Gamma_price c zero, finiteGammaBill]

theorem finite_Gamma_source_bill (c : BurnolCompletedMellinCoordinate) (F : Finset Index) :
    finiteGammaBill c F = inner ℂ (A (originalDualLogValue c)) (finiteSource c F) := by
  rw [finite_source_read, inner_sum]
  simp only [inner_smul_right, finiteGammaBill, generatorBill]

theorem finite_Gamma_bill_tendsto (c : BurnolCompletedMellinCoordinate) :
    Tendsto (finiteGammaBill c) atTop
      (𝓝 (inner ℂ (A (originalDualLogValue c)) (sourceValue c))) := by
  have paid := (tendsto_const_nhds (x := A (originalDualLogValue c))).inner (𝕜 := ℂ)
    (finite_source_tendsto c)
  exact paid.congr' (Eventually.of_forall (fun F => (finite_Gamma_source_bill c F).symm))

/-- The full infinite Pa price is computed by the original cofinal source inventory. -/
theorem actual_pa_coefficient_Gamma_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    inner ℂ (actualGammaKernel c) (paCoefficientSource c : BurnolL2) =
      inner ℂ (A (originalDualLogValue c)) (sourceValue c) := by
  have net := finite_hilbert_tendsto c
  have limit := net.limUnder_eq
  change completedSource c = _ at limit
  rw [← limit] at net
  have physical := ((Hilbert.hilbertAmbientRealizationCLM burnolCompactCoPoissonLanding).continuous.tendsto
    (completedSource c)).comp net
  have completed_read :
      Hilbert.hilbertAmbientRealizationCLM burnolCompactCoPoissonLanding (completedSource c) =
        paCoefficientSource c := actual_pa_coefficient_source c
  rw [completed_read] at physical
  have physicalL2 := (continuous_subtype_val.tendsto (paCoefficientSource c)).comp physical
  have price := (tendsto_const_nhds (x := actualGammaKernel c)).inner (𝕜 := ℂ) physicalL2
  have generated : Tendsto (finiteGammaBill c) atTop
      (𝓝 (inner ℂ (actualGammaKernel c) (paCoefficientSource c : BurnolL2))) :=
    price.congr' (Eventually.of_forall (finite_Gamma_price c zero))
  exact tendsto_nhds_unique generated (finite_Gamma_bill_tendsto c)

end OriginalRSourceJointContact.PaCoefficientPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
