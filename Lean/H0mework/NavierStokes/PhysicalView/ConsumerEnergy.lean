import H0mework.NavierStokes.PhysicalView.ConsumerObservation
import H0mework.NavierStokes.SourceEnergy.Work

set_option autoImplicit false
open scoped Topology ENNReal NNReal

namespace SaturationMonoid.NavierStokes.NativeViewObservedEnergy

open Set MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativeWindowRootCarrier NativeViewObservation NativeWordStressEnergy NativeEndpointVelocityCarrier

noncomputable section

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu} {current : NativeTemporalCurrent initial}
    {occurrence : Occurrence initial current}

def total (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) : ℝ :=
  kineticRead (measure carrier query time).snd / 2

def resolved (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) : ℝ :=
  ‖NativePhysicalFourier.realField (wholeVelocity (measure carrier query time).fst)‖ ^ 2 / 2

def unresolved (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) : ℝ :=
  kineticRead (NativeCompleteHeatTransport.residualValue (measure carrier query time)) / 2

theorem resolved_source (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    resolved carrier query time = NativeViewEnergyContent.resolved initial query.1 (clockAt initial current + time) := by
  rw [resolved, measure_view, CarrierAt.view_generated, NativeViewEnergyContent.resolved_physical]

theorem split (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    total carrier query time = resolved carrier query time + unresolved carrier query time ∧
      0 ≤ unresolved carrier query time := by
  rw [resolved_source]
  simp only [total, unresolved, measure_view, CarrierAt.view_generated]
  exact ⟨NativeViewEnergyContent.split initial query.1 _, NativeViewEnergyContent.unresolved_nonnegative initial query.1 _⟩

theorem budget (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    resolved carrier query time ≤ total carrier query time ∧
      total carrier query time ≤ ‖kineticRead‖ * NativeUnifiedCompleteSource.budget initial / 2 := by
  rw [resolved_source]
  simp only [total, measure_view, CarrierAt.view_generated]
  exact ⟨NativeViewEnergyContent.resolved_le_total initial query.1 _, NativeViewEnergyContent.total_bound initial query.1 _⟩

def work (_carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) : ℝ :=
  NativeViewEnergyWork.residualWork initial query.1 (clockAt initial current + time)

def dissipation (_carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) : ℝ :=
  NativeViewEnergyWork.dissipation initial query.1 (clockAt initial current + time)

theorem dissipation_nonnegative (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    0 ≤ dissipation carrier query time := NativeViewEnergyWork.dissipation_nonnegative initial query.1 _

theorem work_measured (carrier : CarrierAt initial occurrence) (query : HeatQuery) (time : ℝ) :
    work carrier query time = ∑' wave : ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector,
      inner ℝ (NativeCompleteStressAction.euclideanCLM
        (NativeTimeJetCarrier.projectedDivergenceCLM wave.1
          (NativeCompleteStressCarrier.read (NativeCompleteHeatTransport.residualValue (measure carrier query time)) wave.1)))
        ((measure carrier query time).fst wave) := by
  simp only [work, measure_view, CarrierAt.view_generated, NativeViewEnergyWork.residualWork,
    NativeViewEnergyWork.residualRow]

theorem energy_hasDerivAt (carrier : CarrierAt initial occurrence) (query : HeatQuery)
    (time : ℝ) (nonnegative : 0 ≤ time) :
    HasDerivAt (resolved carrier query) (work carrier query time - nu.coeff * dissipation carrier query time) time := by
  have actual := (NativeViewEnergyWork.energy_hasDerivAt initial query.1 query.2
    (clockAt initial current + time) (by linarith [clockAt_nonnegative initial current])).scomp time
      ((hasDerivAt_id time).const_add (clockAt initial current))
  have same : resolved carrier query = fun sample =>
      NativeViewEnergyContent.resolved initial query.1 (clockAt initial current + sample) :=
    funext (resolved_source carrier query)
  rw [same]
  simpa only [Function.comp_def, one_smul, work, dissipation] using! actual

theorem energy_integral (carrier : CarrierAt initial occurrence) (query : HeatQuery)
    (first last : ℝ) (first_nonnegative : 0 ≤ first) (last_nonnegative : 0 ≤ last) :
    resolved carrier query last - resolved carrier query first =
      ∫ time in first..last, work carrier query time - nu.coeff * dissipation carrier query time := by
  have actual := NativeViewEnergyWork.energy_integral initial query.1 query.2
    (clockAt initial current + first) (clockAt initial current + last)
    (by linarith [clockAt_nonnegative initial current]) (by linarith [clockAt_nonnegative initial current])
  have shifted := intervalIntegral.integral_comp_add_left (a := first) (b := last)
    (fun time => NativeViewEnergyWork.residualWork initial query.1 time -
      nu.coeff * NativeViewEnergyWork.dissipation initial query.1 time) (clockAt initial current)
  rw [resolved_source, resolved_source]
  exact actual.trans shifted.symm

end
end SaturationMonoid.NavierStokes.NativeViewObservedEnergy
