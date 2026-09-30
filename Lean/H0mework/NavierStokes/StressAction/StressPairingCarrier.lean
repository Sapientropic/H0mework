import H0mework.NavierStokes.SourceAction.PositiveKernelCarrier
import Mathlib.Analysis.InnerProductSpace.ProdL2
import H0mework.NavierStokes.CofinalReadout.Positivity
import H0mework.NavierStokes.CofinalAction.CofinalPairedCurrent

set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace SaturationMonoid.NavierStokes.NativeStressPairingCarrier

open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open NativeCofinalStress NativeCofinalStressDefect NativeCofinalFluxPairing
open NativePhysicalFourier NativeEndpointVelocityCarrier NativeStressSource
open NativeCofinalStressPositivity (Index shiftedComponent shiftedComponent_inner gram_posSemidef)

noncomputable section

variable {nu : Viscosity}

def covariance (mean : WholeRestartVelocityEndpointState) (stress : NativeFluidStressFourierState) : Matrix Index Index ℂ :=
  fun left right => -(stress (left.1 - right.1) left.2 right.2 - quadraticFlux (wholeVelocity mean) (left.1 - right.1) left.2 right.2)

structure Data where
  mean : WholeRestartVelocityEndpointState
  reality : WholeRestartVelocityEndpointReality mean
  stress : NativeFluidStressFourierState
  positive : (covariance mean stress).PosSemidef

def kernel (data : Data) : NativePositiveKernelCarrier.Kernel Index := ⟨covariance data.mean data.stress, data.positive⟩

abbrev Space (data : Data) := WithLp 2 (ScalarSequence × NativePositiveKernelCarrier.Space (kernel data))

def background (data : Data) (wave : IntegerWavevector) : Space data := WithLp.toLp 2 (lp.single 2 wave (1 : ℂ), 0)

def component (data : Data) (index : Index) : Space data :=
  WithLp.toLp 2 (shiftedComponent data.mean index, NativePositiveKernelCarrier.vector (kernel data) index)

theorem background_component (data : Data) (wave : IntegerWavevector) (index : Index) :
    inner ℂ (background data wave) (component data index) = wholeVelocity data.mean (wave - index.1) index.2 := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (lp.single 2 wave (1 : ℂ)) (shiftedComponent data.mean index) + inner ℂ 0 _ = _
  rw [inner_zero_left, add_zero, lp.inner_single_left]
  simp [RCLike.inner_apply, shiftedComponent]

theorem component_inner (data : Data) (left right : Index) :
    inner ℂ (component data left) (component data right) = -data.stress (left.1 - right.1) left.2 right.2 := by
  rw [WithLp.prod_inner_apply]
  change inner ℂ (shiftedComponent data.mean left) (shiftedComponent data.mean right) +
    inner ℂ (NativePositiveKernelCarrier.vector (kernel data) left) (NativePositiveKernelCarrier.vector (kernel data) right) = _
  rw [shiftedComponent_inner data.mean data.reality, NativePositiveKernelCarrier.vector_inner]
  change -quadraticFlux (wholeVelocity data.mean) (left.1 - right.1) left.2 right.2 +
    -(data.stress (left.1 - right.1) left.2 right.2 - quadraticFlux (wholeVelocity data.mean) (left.1 - right.1) left.2 right.2) = _
  ring

def pairedCurrent (data : Data) (direction : Fin 4) (wave : IntegerWavevector) : ℂ :=
  Fin.cases
    (NativePairedCurrentFourier.baseline wave + (∑ coordinate : Coordinate,
      inner ℂ (component data (wave, coordinate)) (component data (0, coordinate))) / 8)
    (fun coordinate => inner ℂ (background data wave) (component data (0, coordinate))) direction

theorem pairedCurrent_eq (data : Data) (direction : Fin 4) (wave : IntegerWavevector) :
    pairedCurrent data direction wave = NativePairedCurrentFourier.coefficient (wholeVelocity data.mean) data.stress direction wave := by
  refine Fin.cases ?_ (fun coordinate => ?_) direction
  · simp only [pairedCurrent, NativePairedCurrentFourier.coefficient, Fin.cases_zero, component_inner, sub_zero]
    change NativePairedCurrentFourier.baseline wave + (∑ coordinate : Coordinate, -data.stress wave coordinate coordinate) / 8 = _
    rw [Finset.sum_neg_distrib, neg_div]
    rfl
  · simp only [pairedCurrent, NativePairedCurrentFourier.coefficient, Fin.cases_succ, background_component, sub_zero]

theorem component_energy (data : Data) :
    (∑ coordinate : Coordinate, ‖component data (0, coordinate)‖ ^ 2) = -(∑ coordinate : Coordinate, (data.stress 0 coordinate coordinate).re) := by
  simp only [norm_sq_eq_re_inner (𝕜 := ℂ), component_inner, sub_self]
  change (∑ coordinate : Coordinate, -(data.stress 0 coordinate coordinate).re) = _
  simp only [Finset.sum_neg_distrib]

def cofinal (initial : GeneratedWholeRestartCurrent nu) : Data where
  mean := (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint
  reality := (sourceGeneratedWholeRestartCanonicalWeakCofinalReceipt initial).velocityEndpoint_reality
  stress := (sourceGeneratedCofinalStress initial).stress
  positive := NativeCofinalStressPositivity.covariance_posSemidef (sourceGeneratedCofinalStress initial)

theorem cofinal_current (initial : GeneratedWholeRestartCurrent nu) (direction : Fin 4) (wave : IntegerWavevector) :
    pairedCurrent (cofinal initial) direction wave = NativeCofinalPairedCurrent.source initial direction wave :=
  pairedCurrent_eq _ direction wave

theorem cofinal_energy (initial : GeneratedWholeRestartCurrent nu) :
    (∑ coordinate : Coordinate, ‖component (cofinal initial) (0, coordinate)‖ ^ 2) =
      wholeRestartKineticMassLimit initial := by
  rw [component_energy]
  change -(∑ coordinate : Coordinate, ((sourceGeneratedCofinalStress initial).stress 0 coordinate coordinate).re) = _
  rw [NativeStressKineticTrace.cofinal_zero_trace_eq_neg_massLimit, neg_neg]

end
end SaturationMonoid.NavierStokes.NativeStressPairingCarrier
