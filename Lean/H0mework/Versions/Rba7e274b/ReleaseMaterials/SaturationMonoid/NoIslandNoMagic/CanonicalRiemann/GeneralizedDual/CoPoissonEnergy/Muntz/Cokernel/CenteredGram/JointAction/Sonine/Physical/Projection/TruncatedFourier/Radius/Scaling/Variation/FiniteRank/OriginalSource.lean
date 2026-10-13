import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.Mean
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.Operator.ClozelBurnolRechartedOperatorDerivative
import H0mework.Versions.V2.Arithmetic.RieszCanonicalRaw.RieszSingleFourierSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace FixedWindowFourierReaction
open Complex MeasureTheory Set
open scoped InnerProductSpace

def centeredOperator (r : ℝ) : H →L[ℂ] H := Q.comp ((burnolRechartedTruncatedFourierOperator r).comp Q)
def centeredSquare (r : ℝ) : H →L[ℂ] H := (centeredOperator r).comp (centeredOperator r)
def squareDifference (r q : ℝ) : H →L[ℂ] H := centeredSquare r - centeredSquare q

def originalB (coordinate : BurnolCompletedMellinCoordinate) : H :=
  quarterChart (burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2)
def originalForcing (coordinate : BurnolCompletedMellinCoordinate) : H :=
  quarterChart (burnolAmbientMeanZeroFourier (burnolAmbientCompletedMellinKernelFormula coordinate) : BurnolQuarterIntervalL2)

theorem quarter_fourier_chart (x : BurnolQuarterIntervalL2) :
    burnolRechartedTruncatedFourierOperator (1/4 : ℝ) (quarterChart x) = quarterChart (burnolTruncatedFourier x) := by
  rw [burnolRechartedTruncatedFourierOperator_of_pos (by norm_num : (0 : ℝ)<1/4)]
  unfold burnolRadiusRechartedTruncatedFourier
  simp only [ContinuousLinearMap.comp_apply]
  change quarterChart (burnolTruncatedFourier (quarterChart.symm (quarterChart x))) = _
  rw [quarterChart.symm_apply_apply]

theorem quarter_centered_chart (x : BurnolQuarterMeanZeroCarrier) :
    centeredOperator (1/4 : ℝ) (quarterChart (x : BurnolQuarterIntervalL2)) =
      quarterChart (burnolMeanZeroTruncatedFourier x : BurnolQuarterIntervalL2) := by
  unfold centeredOperator
  simp only [ContinuousLinearMap.comp_apply]
  rw [← quarter_projection_chart,show burnolQuarterMeanZeroProjection (x : BurnolQuarterIntervalL2) = x by
      exact Submodule.starProjection_eq_self_iff.mpr x.property,quarter_fourier_chart,← quarter_projection_chart]
  rfl

theorem original_source_inverse :
    ∀ coordinate : BurnolCompletedMellinCoordinate,
      originalB coordinate - centeredSquare (1/4 : ℝ) (originalB coordinate) = originalForcing coordinate := by
  intro coordinate
  have source := burnolRieszSingleFourierSource_equation coordinate
  have actual := congrArg (fun value : BurnolQuarterMeanZeroCarrier => quarterChart (value : BurnolQuarterIntervalL2)) source
  change quarterChart ((burnolRieszSingleFourierSource coordinate : BurnolQuarterIntervalL2) -
    (burnolMeanZeroTruncatedFourier (burnolMeanZeroTruncatedFourier (burnolRieszSingleFourierSource coordinate)) : BurnolQuarterIntervalL2)) = _ at actual
  rw [map_sub] at actual
  change originalB coordinate - centeredOperator (1/4 : ℝ) (centeredOperator (1/4 : ℝ) (originalB coordinate)) = _
  rw [originalB,quarter_centered_chart,quarter_centered_chart]
  exact actual

-- Finite change acts on the already generated original source; no new inverse or K is introduced.
theorem original_source_finite_drive (coordinate : BurnolCompletedMellinCoordinate) (r : ℝ) :
    originalB coordinate - centeredSquare r (originalB coordinate) =
      originalForcing coordinate - squareDifference r (1/4 : ℝ) (originalB coordinate) := by
  rw [squareDifference,sub_apply,← original_source_inverse coordinate]
  module

end FixedWindowFourierReaction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
