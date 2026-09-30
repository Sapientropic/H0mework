import H0mework.Versions.X.NavierStokes.WindowEnergyHighTransport.Work
import H0mework.Versions.X.NavierStokes.WindowEnergyPreparation.Energy

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHighTransportForcing
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativePhysicalFourier NativeCompleteStressAction NativeForwardWindowPairingReadout
open NativeWindowCrossHistoryAction NativeWindowHighTransportGreen
open NativeWindowStressHeatSource (physical)
open NativeWindowLowAdvectorHistory (read_memLp)
noncomputable section
variable {nu : Viscosity}

def highAdvection (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (time : ℝ) : Vector := advection (drift seed F A time) (gradient seed F time)

/-- Both legs remain the original projected action and the same high advector. -/
def remainingAction (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (time : ℝ) : Vector := fun i =>
  NativeWindowStressPreparationAction.actionRead F i (NativeUnifiedCompleteSource.source seed time)+
    highAdvection seed F A time i

def highPair (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  highAdvection seed F A time output*velocity seed F time input+
    velocity seed F time output*highAdvection seed F A time input

def remainingPair (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  -(remainingAction seed F A time output*velocity seed F time input+
    velocity seed F time output*remainingAction seed F A time input)

theorem pair_split (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (output input : Coordinate) (time : ℝ) :
    -NativeWindowStressPreparationAction.nonlinearPair seed F output input time =
      highPair seed F A output input time+remainingPair seed F A output input time := by
  ext point
  simp only [NativeWindowStressPreparationAction.nonlinearPair,highPair,remainingPair,remainingAction,
    velocity,ContinuousMap.add_apply,ContinuousMap.neg_apply,ContinuousMap.mul_apply]
  ring

private theorem triple_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (a b c : FullSpace →L[ℝ] C(Torus,ℝ)) : Integrable (fun shift =>
      a (NativeUnifiedCompleteSource.source seed (time-shift))*b (NativeUnifiedCompleteSource.source seed (time-shift))*
        c (NativeUnifiedCompleteSource.source seed (time-shift))) averageMeasure := by
  have paid := (read_memLp seed time c).mul (r := ∞)
    ((read_memLp seed time b).mul (r := ∞) (read_memLp seed time a))
  simpa only [Pi.mul_def] using paid.integrable (by norm_num : (1 : ℝ≥0∞)≤∞)

theorem highPair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F A : Finset IntegerWavevector) (output input : Coordinate) :
    Integrable (fun shift => highPair seed F A output input (time-shift)) averageMeasure := by
  have row (j : Coordinate) : Integrable (fun shift =>
      (drift seed F A (time-shift) j*gradient seed F (time-shift) j output)*velocity seed F (time-shift) input+
        (velocity seed F (time-shift) output*drift seed F A (time-shift) j)*gradient seed F (time-shift) j input)
      averageMeasure := by
    convert! Integrable.add (ε' := C(Torus,ℝ)) ?_ ?_ using 1
    · simpa only [drift,Pi.sub_apply,velocity,NativeWindowCrossHistoryAction.gradient,
        NativeWindowStressHeatTime.field_original,sub_apply] using!
        triple_integrable seed time (NativeWindowFiniteGramFourier.read F j-NativeWindowFiniteGramFourier.read A j)
          (NativeWindowStressHeatSource.jetRead F j 1 output) (NativeWindowFiniteGramFourier.read F input)
    · simpa only [drift,Pi.sub_apply,velocity,NativeWindowCrossHistoryAction.gradient,
        NativeWindowStressHeatTime.field_original,sub_apply] using!
        triple_integrable seed time (NativeWindowFiniteGramFourier.read F output)
          (NativeWindowFiniteGramFourier.read F j-NativeWindowFiniteGramFourier.read A j)
            (NativeWindowStressHeatSource.jetRead F j 1 input)
  have same : (fun shift => highPair seed F A output input (time-shift)) = fun shift =>
      ∑ j : Coordinate,((drift seed F A (time-shift) j*gradient seed F (time-shift) j output)*velocity seed F (time-shift) input+
        (velocity seed F (time-shift) output*drift seed F A (time-shift) j)*gradient seed F (time-shift) j input) := by
    funext shift
    simp only [highPair,highAdvection,advection,Finset.sum_mul,Finset.mul_sum,← Finset.sum_add_distrib,mul_assoc]
  rw [same]
  exact integrable_finsetSum (ε' := C(Torus,ℝ)) Finset.univ (fun j _ => row j)

theorem remainingPair_integrable (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F A : Finset IntegerWavevector) (output input : Coordinate) :
    Integrable (fun shift => remainingPair seed F A output input (time-shift)) averageMeasure := by
  have row : (fun shift => remainingPair seed F A output input (time-shift)) =
      fun shift => -NativeWindowStressPreparationAction.nonlinearPair seed F output input (time-shift)-
        highPair seed F A output input (time-shift) := by
    funext shift
    have actual := pair_split seed F A output input (time-shift)
    rw [actual]
    abel
  rw [row]
  convert! Integrable.sub (β := C(Torus,ℝ))
    (NativeWindowStressPreparationAction.nonlinearPair_integrable seed time F output input).neg
    (highPair_integrable seed time F A output input) using 1

def highWindow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  ∫ shift,highPair seed F A output input (time-shift) ∂averageMeasure

def remainingWindow (seed : GeneratedWholeRestartCurrent nu) (time : ℝ) (F A : Finset IntegerWavevector)
    (output input : Coordinate) : C(Torus,ℝ) :=
  ∫ shift,remainingPair seed F A output input (time-shift) ∂averageMeasure

theorem nonlinearWindow_split (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F A : Finset IntegerWavevector) (output input : Coordinate) :
    NativeWindowStressPreparationAction.nonlinearWindow seed time F output input =
      highWindow seed time F A output input+remainingWindow seed time F A output input := by
  rw [NativeWindowStressPreparationAction.nonlinearWindow,← integral_neg]
  simp only [pair_split seed F A output input]
  exact integral_add (highPair_integrable seed time F A output input)
    (remainingPair_integrable seed time F A output input)

theorem sigma_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (time : ℝ)
    (F A : Finset IntegerWavevector) (closed : ∀ k,k∈F → waveNeg k∈F) (output input : Coordinate) :
    HasDerivAt (NativeWindowStressHeatBalance.sigma seed F output input)
      (physical (NativeWindowStressHeatSource.heat seed time F output input)+
        physical (highWindow seed time F A output input)+physical (remainingWindow seed time F A output input)+
          physical (NativeWindowStressPreparationAction.correction seed time F output input)) time := by
  have generated := NativeWindowStressPreparationEnergy.sigma_hasDerivAt seed time F closed output input
  rw [nonlinearWindow_split seed time F A,map_add] at generated
  convert! generated using 1
  abel

def currentDerivative (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (j output input : Coordinate) (time : ℝ) : C(Torus,ℝ) :=
  driftJet seed F A time j j*velocity seed F time output*velocity seed F time input+
    drift seed F A time j*(gradient seed F time j output*velocity seed F time input+
      velocity seed F time output*gradient seed F time j input)

theorem current_derivative (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (j output input : Coordinate) (time : ℝ) (x : PhysicalSpace) (parameter : ℝ) :
    HasDerivAt (fun r => NativeWindowHighTransportWork.cubic seed F A j output input time
      (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j r)))
      (currentDerivative seed F A j output input time
        (NativeFullOrderSynthesis.circlePoint (NativeWindowFiniteGramSource.line x j parameter))) parameter := by
  have source := ((drift_derivative seed F A time j j x parameter).mul
    (velocity_derivative seed F time output j x parameter)).mul (velocity_derivative seed F time input j x parameter)
  convert! source using 1
  simp only [currentDerivative,ContinuousMap.mul_apply,ContinuousMap.add_apply,Pi.mul_apply]
  ring

theorem divergence_pair (seed : GeneratedWholeRestartCurrent nu) (F A : Finset IntegerWavevector)
    (time : ℝ) (nonnegative : 0≤time) (output input : Coordinate) :
    (∑ j : Coordinate,currentDerivative seed F A j output input time)=highPair seed F A output input time := by
  have trace : (∑ j : Coordinate,driftJet seed F A time j j)=0 := by
    simp only [driftJet,Pi.sub_apply,Finset.sum_sub_distrib,gradient_trace_zero seed F time nonnegative,
      gradient_trace_zero seed A time nonnegative,sub_self]
  simp only [currentDerivative,Finset.sum_add_distrib,← Finset.sum_mul,trace,zero_mul,zero_add]
  simp only [highPair,highAdvection,advection,Finset.sum_mul,Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

end
end SaturationMonoid.NavierStokes.NativeWindowHighTransportForcing
