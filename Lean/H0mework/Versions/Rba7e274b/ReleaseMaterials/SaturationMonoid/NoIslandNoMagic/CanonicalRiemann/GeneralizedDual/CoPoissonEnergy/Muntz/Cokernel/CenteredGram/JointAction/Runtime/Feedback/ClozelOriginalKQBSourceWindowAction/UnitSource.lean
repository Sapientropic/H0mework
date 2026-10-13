import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNonPaSourceWardAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPhysicalWindowSourceAction.GeneratedPrice
import H0mework.Versions.V2.Arithmetic.RemainderSource.RemainderMean
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
open Complex MeasureTheory Set Filter BurnolPhysicalState
open scoped InnerProductSpace Topology BigOperators
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance qbUnitSourceComplete : CompleteSpace BurnolPaAmbientCarrier := by
  apply IsComplete.completeSpace_coe
  exact (evenBurnolClosedFace burnolUnscaledCommonGapRadius).isClosed.isComplete
local notation "P" => burnolEvenAmbientProjection
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "Q" => OriginalKFullSourceRResponse.Paid.Q
local notation "F" => evenFaceFourierEquiv burnolUnscaledCommonGapRadius
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
open OriginalKWholePaSourceRankAction
def sourceMeanReader (t : ℝ) : BurnolL2 →L[ℂ] ℂ :=
  FiniteMobiusResolventFlux.actualMean.comp
    (burnolMultiplicativeDilation t).toLinearIsometry.toContinuousLinearMap

def unitPrimitiveMeanProgramme (coordinate : BurnolCompletedMellinCoordinate)
    (direction : BurnolL2 →L[ℂ] BurnolL2) (t : ℝ) : ℂ :=
  sourceMeanReader t (direction
    (burnolUnitPowerWeight coordinate (1/4:ℝ) •
      burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 (1/4:ℝ))) -
    ∫ u : ℝ in Ioc 0 (1/4:ℝ),
      sourceMeanReader t (direction
        (burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 u))

/-- Actual unit source vector integration precedes the position/Fourier mean reader; source integrability is already paid. -/
theorem original_unit_source_mean_programme (coordinate : BurnolCompletedMellinCoordinate)
    (direction : BurnolL2 →L[ℂ] BurnolL2) (t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (direction (burnolUnitTailResponse coordinate 4))) =
      unitPrimitiveMeanProgramme coordinate direction t := by
  let read := (sourceMeanReader t).comp direction
  have integrable := burnolUnitTailSlope_integrable coordinate burnolUnitCountingPrimitiveL2 (1/4:ℝ)
  have effect := read.integral_comp_comm integrable
  change (∫ u : ℝ in Ioc 0 (1/4:ℝ), read
    (burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 u)) =
      read (∫ u : ℝ in Ioc 0 (1/4:ℝ),
        burnolUnitTailSlope coordinate u • burnolSourceScalePrimitive burnolUnitCountingPrimitiveL2 u) at effect
  change read (burnolUnitTailResponse coordinate 4) = _
  unfold burnolUnitTailResponse burnolUnitTailPrimitiveValue
  norm_num only [show (4:ℝ)⁻¹=1/4 by norm_num]
  rw [map_sub,←effect]
  rfl

def actualUnitTailMeanProgramme (t : ℝ) : ℂ :=
  unitPrimitiveMeanProgramme (actualWholePaDivisionCoordinate observation nontrivial half)
    (ContinuousLinearMap.id ℂ BurnolL2) t

def actualUnitFourierWholeMeanProgramme (t : ℝ) : ℂ :=
  actualUnitTailMeanProgramme observation nontrivial half t +
    unitPrimitiveMeanProgramme (actualWholePaDivisionCoordinate observation nontrivial half)
      fourierL2.toLinearIsometry.toContinuousLinearMap t

theorem actual_unit_tail_mean_source (t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf : BurnolL2)) =
      actualUnitTailMeanProgramme observation nontrivial half t :=
  original_unit_source_mean_programme _ (ContinuousLinearMap.id ℂ BurnolL2) t

theorem actual_unit_fourier_whole_mean_source (t : ℝ) :
    FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
      (burnolZeroOwnedUnitFourierState observation nontrivial (c).rightHalf : BurnolL2)) =
      actualUnitFourierWholeMeanProgramme observation nontrivial half t := by
  change FiniteMobiusResolventFlux.actualMean (burnolMultiplicativeDilation t
    ((burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf : BurnolL2) +
      fourierL2 (burnolZeroOwnedUnitTailState observation nontrivial (c).rightHalf : BurnolL2))) = _
  rw [map_add,map_add,actual_unit_tail_mean_source]
  have source := original_unit_source_mean_programme
    (actualWholePaDivisionCoordinate observation nontrivial half)
    fourierL2.toLinearIsometry.toContinuousLinearMap t
  exact congrArg (fun price => actualUnitTailMeanProgramme observation nontrivial half t + price) source

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKQBSourceWindowAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
