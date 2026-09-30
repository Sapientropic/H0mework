import H0mework.Versions.X.NavierStokes.WindowPhysics.PredictionWhole
import H0mework.Versions.X.NavierStokes.WindowPhysics.RootControl

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewRootPrediction

open Set MeasureTheory
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeUnifiedHeatAction NativeWindowRootCarrier NativeWindowRootControl

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current}

def kernel (carrier : CarrierAt initial occurrence) (query : HeatQuery) (target time : ℝ) :
    WholeRestartVelocityEndpointState :=
  heatCLM nu ⟨max (target - time) 0, le_max_right _ _⟩ (divergenceCLM (carrier.view query.1 time).snd)

def predict (carrier : CarrierAt initial occurrence) (query : HeatQuery) (target : ℝ) :
    WholeRestartVelocityEndpointState :=
  heatCLM nu ⟨max target 0, le_max_right _ _⟩ (NativeNegativeFourMomentum.embed (carrier.view query.1 0).fst) +
    ∫ time in (0 : ℝ)..target, kernel carrier query target time

theorem kernel_generated (carrier : CarrierAt initial occurrence) (query : HeatQuery) (target time : ℝ) :
    kernel carrier query target time = NativeViewPrediction.heatForcing initial query.1
      (clockAt initial current + target) (clockAt initial current + time) := by
  unfold kernel NativeViewPrediction.heatForcing NativeViewPrediction.forcing
  rw [CarrierAt.view_generated]
  simp only [add_sub_add_left_eq_sub]

theorem predict_generated (carrier : CarrierAt initial occurrence) (query : HeatQuery) (target : ℝ) :
    predict carrier query target = NativeViewPrediction.prediction initial query.1
      (clockAt initial current) (clockAt initial current + target) := by
  have shifted := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := target)
    (NativeViewPrediction.heatForcing initial query.1 (clockAt initial current + target)) (clockAt initial current)
  simp only [add_zero] at shifted
  unfold predict NativeViewPrediction.prediction
  rw [CarrierAt.view_generated, add_zero, NativeWindowHeatEvolution.state_embedded, ← shifted]
  simp only [add_sub_cancel_left]
  congr 1
  exact intervalIntegral.integral_congr fun time _ => kernel_generated carrier query target time

theorem prediction_recovers_velocity (carrier : CarrierAt initial occurrence) (query : HeatQuery)
    (target : ℝ) (nonnegative : 0 ≤ target) :
    predict carrier query target = NativeNegativeFourMomentum.embed (carrier.view query.1 target).fst := by
  rw [predict_generated, CarrierAt.view_generated]
  exact (NativeViewPrediction.prediction_physical initial query.1 _ _
    (by linarith [clockAt_nonnegative initial current]) (by linarith)).symm

theorem predicted_velocity_unique (carrier : CarrierAt initial occurrence) (query : HeatQuery)
    (target : ℝ) (nonnegative : 0 ≤ target) (value : WholeRestartVelocityEndpointState)
    (predicted : NativeNegativeFourMomentum.embed value = predict carrier query target) :
    value = (carrier.view query.1 target).fst := by
  apply NativeNegativeFourMomentum.embed_injective
  exact predicted.trans (prediction_recovers_velocity carrier query target nonnegative)

theorem authority_prediction (initial : GeneratedWholeRestartCurrent nu)
    (visit : SourceNativeTemporalVisitAt (nativeTemporalRoot initial)) (query : HeatQuery)
    (target : ℝ) (nonnegative : 0 ≤ target) :
    predict (authorityCarrier initial visit query) query target =
      NativeNegativeFourMomentum.embed ((authorityCarrier initial visit query).view query.1 target).fst :=
  prediction_recovers_velocity (authorityCarrier initial visit query) query target nonnegative

theorem finite_next_prediction (initial : GeneratedWholeRestartCurrent nu) (index : ℕ) (query : HeatQuery) :
    predict (generatedCarrier initial (nativeTemporalEmitted initial (.finite index))) query
      (run initial index).contact.time.1 =
      NativeNegativeFourMomentum.embed
        ((generatedCarrier initial (nativeTemporalEmitted initial (.finite (index + 1)))).view query.1 0).fst := by
  rw [prediction_recovers_velocity _ query _ (run initial index).contact.time.2.1]
  rw [finite_next_view]
  simp only [add_zero]

end
end SaturationMonoid.NavierStokes.NativeViewRootPrediction
