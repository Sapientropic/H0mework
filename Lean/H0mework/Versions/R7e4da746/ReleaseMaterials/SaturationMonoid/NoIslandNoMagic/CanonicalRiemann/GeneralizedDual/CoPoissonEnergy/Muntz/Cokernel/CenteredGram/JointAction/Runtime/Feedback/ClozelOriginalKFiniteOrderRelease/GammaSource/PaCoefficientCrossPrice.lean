import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PaCoefficientPrice
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.CrossPrice

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalRSourceJointContact.PaCoefficientCrossPrice
open Complex BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalGamma.Source.KGamma OriginalGamma.Source.RelativeConductorGapReadback
open OriginalGamma.Source.KappaConductor
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open OriginalKDirectRCofinalOutsideVolterraSource
open scoped InnerProductSpace
variable (observation : GeneratedRiemannZeroObservation)
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "K" => burnolCompletedMellinRieszVector

/-- The original Xi-order Pa foot pays its actual source price in the right slot. -/
theorem actual_original_m_Pa_Gamma_price :
    inner ℂ (actualGammaKernel c)
      (OriginalKFiniteOrderRelease.UnitPowerSource.paPowerField observation half : BurnolL2) =
    OriginalKFiniteOrderRelease.UnitPowerSource.paPowerCoefficient observation half *
      inner ℂ (sourceAnnulusCut (originalDualLogValue c)) (PaCoefficientSourceGram.sourceValue c) := by
  change inner ℂ (actualGammaKernel c)
    (OriginalKFiniteOrderRelease.UnitPowerSource.paPowerCoefficient observation half •
      (paCoefficientSource c : BurnolL2)) = _
  rw [inner_smul_right, PaCoefficientPrice.actual_pa_coefficient_Gamma_price c observation.mathlibZero]

/-- The complete original cross price now consumes the cofinal Pa bill; every outside and Q fee remains. -/
theorem actual_complete_cross_price_source :
    inner ℂ (actualGammaKernel c) (sourceQ observation half) -
      inner ℂ (((burnolDirectRightResolventCLM c)^m) (K c : BurnolL2))
        (OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2) =
    -(OriginalKFiniteOrderRelease.UnitPowerSource.paPowerCoefficient observation half *
        inner ℂ (sourceAnnulusCut (originalDualLogValue c)) (PaCoefficientSourceGram.sourceValue c)) -
      ∑ j ∈ Finset.range m, sourceCoefficient c m j *
        inner ℂ (actualGammaKernel c) (logOutsideColumn c j) +
      inner ℂ (((burnolDirectRightResolventCLM c)^m) (K c : BurnolL2))
        (gammaCombo c - (OriginalKCombCofinalPaAction.Q (gammaCombo c) : BurnolL2)) := by
  have paid := OriginalRSourceJointContact.actual_complete_cross_price observation half
  rw [actual_original_m_Pa_Gamma_price] at paid
  exact paid

end OriginalRSourceJointContact.PaCoefficientCrossPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
