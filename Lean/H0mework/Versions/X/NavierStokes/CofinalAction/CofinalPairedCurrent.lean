import H0mework.Versions.X.NavierStokes.PairedAction.PairedCurrentFourier
import H0mework.Versions.X.NavierStokes.CofinalAction.CofinalMomentum

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeCofinalPairedCurrent

open Set Filter UnitAddTorus MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientWholeVelocityPairDiagonalBudget
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open NativePairedCurrentFourier NativeStressSource NativeCofinalStress NativeCofinalStressDefect
open NativeCofinalMomentumAction NativeEndpointVelocityCarrier

noncomputable section

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

variable {nu : Viscosity} {initial : GeneratedWholeRestartCurrent nu}

def contactVelocity (initial : GeneratedWholeRestartCurrent nu) (stage : ℕ) : ComplexVorticityHilbertState :=
  wholeBiotSavartVelocityState (run initial stage).contact.physicalState

theorem contact_reality (initial : GeneratedWholeRestartCurrent nu) (stage : ℕ) :
    FiniteStateFourierReality (contactVelocity initial stage) :=
  NativePhysicalSource.velocity_reality _ (wholeRestartPhysicalReality (run initial stage).contact)

def actual (initial : GeneratedWholeRestartCurrent nu) (stage : ℕ) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  mFourierCoeff (fun point => (field (contactVelocity initial stage) direction point : ℂ)) wave

def inherited (receipt : CofinalStressAt initial) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  coefficient (endpointVelocity initial) receipt.stress direction wave

theorem coefficient_continuous (direction : Fin 4) (wave : IntegerWavevector) :
    Continuous (fun pair : NativeFluidVorticityTangent × NativeFluidStressFourierState =>
      coefficient pair.1 pair.2 direction wave) := by
  refine Fin.cases ?_ (fun spatial => ?_) direction
  · dsimp only [coefficient, Fin.cases_zero, trace]
    fun_prop
  · dsimp only [coefficient, Fin.cases_succ]
    fun_prop

theorem inherited_tendsto (receipt : CofinalStressAt initial) (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun index => actual initial (receipt.stage index) direction wave) atTop (𝓝 (inherited receipt direction wave)) := by
  have joint := (velocity_tendsto receipt).prodMk_nhds receipt.stress_tendsto
  have source := (coefficient_continuous direction wave).tendsto ((fun wave => endpointVelocity initial wave), receipt.stress) |>.comp joint
  apply source.congr'
  exact Eventually.of_forall fun index => (current_fourier (contactVelocity initial (receipt.stage index))
    (contact_reality initial (receipt.stage index)) direction wave).symm

theorem endpoint_reality (initial : GeneratedWholeRestartCurrent nu) : FiniteStateFourierReality (endpointVelocity initial) :=
  wholeVelocity_reality _ (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint_reality

theorem inherited_spatial (receipt : CofinalStressAt initial) (direction : Fin 3) (wave : IntegerWavevector) :
    inherited receipt direction.succ wave = mFourierCoeff
      (fun point => (field (endpointVelocity initial) direction.succ point : ℂ)) wave := by
  rw [current_fourier _ (endpoint_reality initial)]
  rfl

theorem inherited_temporal_defect (receipt : CofinalStressAt initial) (wave : IntegerWavevector) :
    inherited receipt 0 wave - mFourierCoeff (fun point => (field (endpointVelocity initial) 0 point : ℂ)) wave =
      -trace (stressDefect receipt) wave / 8 := by
  rw [current_fourier _ (endpoint_reality initial)]
  change (baseline wave - trace receipt.stress wave / 8) -
    (baseline wave - trace (quadraticFlux (endpointVelocity initial)) wave / 8) =
      -trace (receipt.stress - quadraticFlux (endpointVelocity initial)) wave / 8
  simp only [trace, Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem inherited_temporal_mean (receipt : CofinalStressAt initial) :
    (inherited receipt 0 0).re = 2 + wholeRestartKineticMassLimit initial / 8 := by
  change (baseline 0 - trace receipt.stress 0 / 8).re = _
  rw [baseline_zero]
  simp only [Complex.sub_re, Complex.div_ofNat_re, trace, Complex.re_sum]
  rw [NativeStressKineticTrace.cofinal_zero_trace_eq_neg_massLimit receipt]
  norm_num
  ring

theorem inherited_temporal_mean_defect (receipt : CofinalStressAt initial) :
    (inherited receipt 0 0 - mFourierCoeff (fun point => (field (endpointVelocity initial) 0 point : ℂ)) 0).re =
      wholeRestartKineticWeakEndpointDefect initial
        (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).kineticEndpoint / 8 := by
  rw [inherited_temporal_defect]
  simp only [Complex.div_ofNat_re, Complex.neg_re, trace, Complex.re_sum]
  rw [stressDefect_zero_trace receipt]

def source (initial : GeneratedWholeRestartCurrent nu) : Fin 4 → IntegerWavevector → ℂ :=
  inherited (sourceGeneratedCofinalStress initial)

theorem source_current_tendsto (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) (wave : IntegerWavevector) :
    Tendsto (fun index => actual initial ((sourceGeneratedCofinalStress initial).stage index) direction wave)
      atTop (𝓝 (source initial direction wave)) := inherited_tendsto _ direction wave

end
end SaturationMonoid.NavierStokes.NativeCofinalPairedCurrent
