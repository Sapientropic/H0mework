import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCovector
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCoefficientCrossPrice

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceJointContact.PaCompressionPrice
open Complex BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalGamma.Source.KGamma OriginalGamma.Source.KappaConductor
open OriginalGamma.Source.RelativeConductorGapReadback
open OriginalKCrossParameterRAdjointSource OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
local notation "Pa" => PaNativePortSource.Pa
local notation "F" => fourierL2
local notation "EF" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
local instance : CompleteSpace BurnolPaAmbientCarrier :=
  IsComplete.completeSpace_coe (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete

private theorem E_mem (value : BurnolL2) :
    OriginalKCombCofinalPaAction.E value ∈ Pa := Submodule.starProjection_apply_mem _ _
private def paFace (value : BurnolL2) : ↥Pa :=
  ⟨OriginalKCombCofinalPaAction.E value,E_mem value⟩

private theorem fourier_mem (p : BurnolPaAmbientCarrier) (inside : p ∈ Pa) : EF p ∈ Pa := by
  have generated : EF p ∈ burnolCompactCoPoissonClosedRange.mapEquiv (evenFaceFourierEquiv burnolUnscaledCommonGapRadius).toContinuousLinearEquiv :=
    Submodule.mem_map.mpr ⟨p,inside,rfl⟩
  rw [burnolCompactCoPoissonClosedRange_fourier_invariant] at generated
  exact generated

private def inverseFourierPaFace (value : BurnolL2) : ↥Pa :=
  ⟨EF (paFace value : BurnolPaAmbientCarrier),fourier_mem _ (paFace value).property⟩

private theorem inverse_face_read (value : BurnolL2) :
    ((inverseFourierPaFace value : BurnolPaAmbientCarrier) : BurnolL2) =
      fourierL2.symm ((paFace value : BurnolPaAmbientCarrier) : BurnolL2) := by
  apply fourierL2.injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  change F (F ((paFace value : BurnolPaAmbientCarrier) : BurnolL2)) = _
  rw [fourierL2_fourierL2]
  exact mem_evenL2ClosedFace_iff.mp (paFace value : BurnolPaAmbientCarrier).property.2

def sourcePaRead (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  inner ℂ (sourceAnnulusCut (originalDualLogValue c)) (PaNativePortSource.sourceMap (paFace value))
def sourceInverseFourierPaRead (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  inner ℂ (sourceAnnulusCut (originalDualLogValue c))
    (PaNativePortSource.sourceMap (inverseFourierPaFace value))
def compressionSourceBill (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : ℂ :=
  jQuarterAmplitude c * star (sourcePaRead c value) -
    hQuarterAmplitude c * star (sourceInverseFourierPaRead c value)

private theorem E_selfAdjoint (left right : BurnolL2) :
    inner ℂ left (OriginalKCombCofinalPaAction.E right : BurnolL2) =
      inner ℂ (OriginalKCombCofinalPaAction.E left : BurnolL2) right := by
  have first := OriginalKCombCofinalPaAction.wholePa_normal_read right
    (OriginalKCombCofinalPaAction.E left) (E_mem left)
  have second := OriginalKCombCofinalPaAction.wholePa_normal_read left
    (OriginalKCombCofinalPaAction.E right) (E_mem right)
  calc
    _ = star (inner ℂ (OriginalKCombCofinalPaAction.E right : BurnolL2) left) :=
      (inner_conj_symm _ _).symm
    _ = star (inner ℂ (OriginalKCombCofinalPaAction.E right)
        (OriginalKCombCofinalPaAction.E left)) := congrArg star second.symm
    _ = inner ℂ (OriginalKCombCofinalPaAction.E left) (OriginalKCombCofinalPaAction.E right) :=
      inner_conj_symm _ _
    _ = _ := first

theorem actual_gammaCombo_Pa_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (value : BurnolL2) :
    inner ℂ value (OriginalKCombCofinalPaAction.E (gammaCombo c) : BurnolL2) =
      compressionSourceBill c value := by
  have paid := PaCovector.actual_Gamma_Pa_source_covector c zero (paFace value)
  have inversePaid := PaCovector.actual_Gamma_Pa_source_covector c zero (inverseFourierPaFace value)
  have direct : inner ℂ (OriginalKCombCofinalPaAction.E value : BurnolL2) (actualGammaKernel c) =
      star (sourcePaRead c value) :=
    (inner_conj_symm _ _).symm.trans (congrArg star paid)
  have inverse : inner ℂ (fourierL2.symm (OriginalKCombCofinalPaAction.E value : BurnolL2))
      (actualGammaKernel c) = star (sourceInverseFourierPaRead c value) := by
    change inner ℂ (fourierL2.symm ((paFace value : BurnolPaAmbientCarrier) : BurnolL2))
      (actualGammaKernel c) = _
    rw [← inverse_face_read value]
    exact (inner_conj_symm _ _).symm.trans (congrArg star inversePaid)
  have moved := fourierL2.inner_map_map (fourierL2.symm (OriginalKCombCofinalPaAction.E value : BurnolL2))
    (actualGammaKernel c)
  rw [LinearIsometryEquiv.apply_symm_apply] at moved
  rw [E_selfAdjoint,gammaCombo,inner_sub_right,inner_smul_right,inner_smul_right,direct,moved,inverse]
  rfl

/-- Only the Pa part is paid by the recovered covector; the ambient exterior is retained literally. -/
theorem actual_compression_source_price
    (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (value : BurnolL2) :
    inner ℂ value (gammaCombo c-(OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2)) =
      compressionSourceBill c value +
        inner ℂ value (gammaCombo c-(burnolEvenAmbientProjection (gammaCombo c) : BurnolL2)) := by
  have split := burnolCompactCoPoissonClosedRange.toSubmodule.starProjection_add_starProjection_orthogonal
    (burnolEvenAmbientProjection (gammaCombo c))
  have actual := congrArg (fun v : BurnolPaAmbientCarrier => (v : BurnolL2)) split
  change (OriginalKCombCofinalPaAction.E (gammaCombo c) : BurnolL2)+
    (OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2) =
      (burnolEvenAmbientProjection (gammaCombo c) : BurnolL2) at actual
  have inventory : gammaCombo c-(OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2) =
      (OriginalKCombCofinalPaAction.E (gammaCombo c) : BurnolL2)+
        (gammaCombo c-(burnolEvenAmbientProjection (gammaCombo c) : BurnolL2)) := by
    linear_combination (norm := module) -actual
  rw [inventory,inner_add_right,actual_gammaCombo_Pa_price c zero]

variable (observation : GeneratedRiemannZeroObservation)
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "K" => burnolCompletedMellinRieszVector

/-- The original m cross price consumes the entire Pa covector, with both exterior responsibilities intact. -/
theorem actual_complete_cross_price_source :
    inner ℂ (actualGammaKernel c) (sourceQ observation half) -
      inner ℂ (((burnolDirectRightResolventCLM c)^m) (K c : BurnolL2))
        (OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2) =
    -(OriginalKFiniteOrderRelease.UnitPowerSource.paPowerCoefficient observation half *
        inner ℂ (sourceAnnulusCut (originalDualLogValue c)) (PaCoefficientSourceGram.sourceValue c)) -
      ∑ j ∈ Finset.range m, sourceCoefficient c m j *
        inner ℂ (actualGammaKernel c) (logOutsideColumn c j) +
      (compressionSourceBill c (((burnolDirectRightResolventCLM c)^m) (K c : BurnolL2)) +
        inner ℂ (((burnolDirectRightResolventCLM c)^m) (K c : BurnolL2))
          (gammaCombo c-(burnolEvenAmbientProjection (gammaCombo c) : BurnolL2))) := by
  have paid := PaCoefficientCrossPrice.actual_complete_cross_price_source observation half
  rw [actual_compression_source_price c observation.mathlibZero] at paid
  exact paid

end OriginalRSourceJointContact.PaCompressionPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
