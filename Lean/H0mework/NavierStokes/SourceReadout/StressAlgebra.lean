import H0mework.NavierStokes.Accumulation.NativeFluidMedium
import H0mework.NavierStokes.Fourier.WholeVelocityFixedOutputNonlinearRow
import H0mework.NavierStokes.PairRestart.PairDuhamelKineticTriadRedirect

/-!
# Linear momentum-flux action on the complete Fourier carrier

The original stress divergence and curl commute with absolutely summable
source pairs. The same tensor also generates its longitudinal pressure.
These are coefficient-space operations; no Sobolev operator norm is asserted.
-/

set_option autoImplicit false

open scoped BigOperators Matrix

namespace SaturationMonoid.NavierStokes.NativeStressCurlAlgebra

open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientWholeVelocityFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect

noncomputable section

/-- The actual stress divergence is complex-linear on its finite coefficient carrier. -/
def stressDivergenceCLM (wave : IntegerWavevector) :
    NativeFluidStressCoefficient →L[ℂ] ComplexCoordinateVector :=
  LinearMap.toContinuousLinearMap
    { toFun := fun tensor => nativeFluidStressDivergenceCoefficient (fun _ => tensor) wave
      map_add' := by
        intro left right
        funext coordinate
        simp [nativeFluidStressDivergenceCoefficient, Finset.sum_add_distrib, mul_add]
      map_smul' := by
        intro scalar tensor
        funext coordinate
        simp [nativeFluidStressDivergenceCoefficient, Fin.sum_univ_succ]
        ring }

@[simp] theorem stressDivergenceCLM_apply (wave : IntegerWavevector)
    (tensor : NativeFluidStressCoefficient) :
    stressDivergenceCLM wave tensor =
      nativeFluidStressDivergenceCoefficient (fun _ => tensor) wave := rfl

/-- The whole source operation has the same linear laws without a frequency cutoff. -/
def wholeStressDivergenceCLM :
    NativeFluidStressFourierState →L[ℂ] NativeFluidVorticityTangent :=
  ContinuousLinearMap.pi fun wave =>
    (stressDivergenceCLM wave).comp (ContinuousLinearMap.proj wave)

@[simp] theorem wholeStressDivergenceCLM_apply (stress : NativeFluidStressFourierState) :
    wholeStressDivergenceCLM stress = nativeFluidStressDivergenceCoefficient stress := rfl

/-- The original curl-div action, on the complete stress carrier. -/
def wholeStressActionCLM :
    NativeFluidStressFourierState →L[ℂ] NativeFluidVorticityTangent :=
  ContinuousLinearMap.pi fun wave =>
    (fourierCurlCoefficientContinuousLinearMap wave).comp
      ((stressDivergenceCLM wave).comp (ContinuousLinearMap.proj wave))

@[simp] theorem wholeStressActionCLM_apply (stress : NativeFluidStressFourierState) :
    wholeStressActionCLM stress = nativeFluidConstitutiveVorticityAction stress := rfl

theorem nativeFluidStressDivergenceCoefficient_tsum {α : Type*}
    (wave : IntegerWavevector) (row : α → NativeFluidStressCoefficient)
    (summable : Summable row) :
    nativeFluidStressDivergenceCoefficient (fun _ i j => ∑' a, row a i j) wave =
      ∑' a, nativeFluidStressDivergenceCoefficient (fun _ => row a) wave := by
  have sumEq : (fun i j => ∑' a, row a i j) = ∑' a, row a := by
    funext i j
    rw [tsum_apply summable, tsum_apply (Pi.summable.mp summable i)]
  change stressDivergenceCLM wave (fun i j => ∑' a, row a i j) = _
  rw [sumEq]
  exact (stressDivergenceCLM wave).map_tsum summable

theorem nativeFluidStressDivergenceCoefficient_projection
    (modes : Finset IntegerWavevector) (stress : NativeFluidStressFourierState)
    (wave : IntegerWavevector) :
    nativeFluidStressDivergenceCoefficient
        (fun wave => if wave ∈ modes then stress wave else 0) wave =
      if wave ∈ modes then nativeFluidStressDivergenceCoefficient stress wave else 0 := by
  change stressDivergenceCLM wave (if wave ∈ modes then stress wave else 0) = _
  split_ifs
  · rfl
  · exact (stressDivergenceCLM wave).map_zero

theorem nativeFluidConstitutiveVorticityAction_projection
    (modes : Finset IntegerWavevector) (stress : NativeFluidStressFourierState)
    (wave : IntegerWavevector) :
    nativeFluidConstitutiveVorticityAction
        (fun wave => if wave ∈ modes then stress wave else 0) wave =
      if wave ∈ modes then nativeFluidConstitutiveVorticityAction stress wave else 0 := by
  unfold nativeFluidConstitutiveVorticityAction
  rw [nativeFluidStressDivergenceCoefficient_projection]
  split_ifs <;> simp [fourierCurlCoefficient]

/-- The original Fourier curl annihilates the pressure direction, including the zero mode. -/
theorem fourierCurlCoefficient_transverseProjection
    (wave : IntegerWavevector) (vector : ComplexCoordinateVector) :
    fourierCurlCoefficient wave (transverseProjection wave vector) =
      fourierCurlCoefficient wave vector := by
  by_cases waveZero : wave = 0
  · subst wave
    simp [fourierCurlCoefficient]
  · funext coordinate
    fin_cases coordinate <;>
      simp [fourierCurlCoefficient, transverseProjection, waveZero, cross_apply] <;>
      ring

/-- Negative momentum flux has the sign of the original velocity convection row.
The transported coordinate is the first stress index. -/
theorem nativeFluidStressDivergenceCoefficient_negativeDyad
    (wave : IntegerWavevector) (advecting transported : ComplexCoordinateVector) :
    nativeFluidStressDivergenceCoefficient
        (fun _ i j => -(transported i * advecting j)) wave =
      -((Complex.I * (((2 * Real.pi : Real) : Complex))) *
          (complexWavevector wave ⬝ᵥ advecting)) • transported := by
  funext coordinate
  simp [nativeFluidStressDivergenceCoefficient, dotProduct, Fin.sum_univ_succ]
  ring

/-- A single original ordered pair already generates its stress-divergence action;
transversality moves the derivative from the input to its actual output frequency. -/
theorem nativeFluidStressDivergenceCoefficient_negativePair
    (advecting transported : ComplexVorticityHilbertState)
    (first second : IntegerWavevector)
    (transverse : complexWavevector first ⬝ᵥ advecting first = 0) :
    nativeFluidStressDivergenceCoefficient
        (fun _ i j => -(transported second i * advecting first j)) (first + second) =
      wholeStateVelocityBilinearPairContribution advecting transported (first, second) := by
  have waveAdd : complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
    funext coordinate
    simp [complexWavevector]
  rw [nativeFluidStressDivergenceCoefficient_negativeDyad, waveAdd, add_dotProduct,
    transverse, zero_add]
  rfl

/-- The pairwise action is read from the original negative momentum flux. -/
theorem nativeFluidConstitutiveVorticityAction_negativePair
    (advecting transported : ComplexVorticityHilbertState)
    (first second : IntegerWavevector)
    (transverse : complexWavevector first ⬝ᵥ advecting first = 0) :
    nativeFluidConstitutiveVorticityAction
        (fun _ i j => -(transported second i * advecting first j)) (first + second) =
      fourierCurlCoefficient (first + second)
        (wholeStateVelocityBilinearPairContribution advecting transported (first, second)) := by
  exact congrArg (fourierCurlCoefficient (first + second))
    (nativeFluidStressDivergenceCoefficient_negativePair
      advecting transported first second transverse)

/-- Whole momentum-flux divergence consumes exactly the original velocity pair sum. -/
theorem nativeFluidStressDivergenceCoefficient_quadraticConvolution
    (velocity : ComplexVorticityHilbertState) (transverse : WholeStateTransverse velocity)
    (wave : IntegerWavevector)
    (summable : ∀ output input : Coordinate,
      Summable (fun first : IntegerWavevector =>
        velocity first input * velocity (wave - first) output)) :
    nativeFluidStressDivergenceCoefficient
        (fun wave output input => -∑' first : IntegerWavevector,
          velocity first input * velocity (wave - first) output) wave =
      wholeStateVelocityNonlinearCoefficientAt velocity wave := by
  let row : IntegerWavevector → NativeFluidStressCoefficient :=
    fun first output input => -(velocity (wave - first) output * velocity first input)
  have rowSummable : Summable row := by
    apply Pi.summable.mpr
    intro output
    apply Pi.summable.mpr
    intro input
    simpa only [row, mul_comm] using (summable output input).neg
  have fluxEq : (fun output input => -∑' first : IntegerWavevector,
      velocity first input * velocity (wave - first) output) = ∑' first, row first := by
    funext output input
    rw [tsum_apply rowSummable, tsum_apply (Pi.summable.mp rowSummable output)]
    simp only [row, ← tsum_neg, mul_comm]
  change stressDivergenceCLM wave (fun output input => -∑' first : IntegerWavevector,
    velocity first input * velocity (wave - first) output) = _
  rw [fluxEq, (stressDivergenceCLM wave).map_tsum rowSummable]
  unfold wholeStateVelocityNonlinearCoefficientAt wholeStateVelocityBilinearCoefficientAt
  apply tsum_congr
  intro first
  have incidence : first + (wave - first) = wave := by abel
  have pair := nativeFluidStressDivergenceCoefficient_negativePair
    velocity velocity first (wave - first) (transverse first)
  rw [incidence] at pair
  exact pair

/-- The longitudinal pressure is a contraction of the same stress coefficient. -/
def stressPressureCoefficient (wave : IntegerWavevector)
    (tensor : NativeFluidStressCoefficient) : Complex :=
  if wave = 0 then 0 else
    (complexWavevector wave ⬝ᵥ
      (fun i => ∑ j : Coordinate, complexWavevector wave j * tensor i j)) /
      (integerWaveNormSq wave : Complex)

/-- The complete stress force splits into its original Leray force and the pressure gradient. -/
theorem nativeFluidStressDivergenceCoefficient_eq_leray_add_pressure
    (wave : IntegerWavevector) (tensor : NativeFluidStressCoefficient) :
    nativeFluidStressDivergenceCoefficient (fun _ => tensor) wave =
      transverseProjection wave
        (nativeFluidStressDivergenceCoefficient (fun _ => tensor) wave) +
      ((Complex.I * (((2 * Real.pi : Real) : Complex))) *
        stressPressureCoefficient wave tensor) • complexWavevector wave := by
  by_cases waveZero : wave = 0
  · subst wave
    funext coordinate
    simp [nativeFluidStressDivergenceCoefficient, transverseProjection,
      stressPressureCoefficient, complexWavevector]
  · have contraction :
        complexWavevector wave ⬝ᵥ
            nativeFluidStressDivergenceCoefficient (fun _ => tensor) wave =
          (Complex.I * (((2 * Real.pi : Real) : Complex))) *
            (complexWavevector wave ⬝ᵥ
              (fun i => ∑ j : Coordinate, complexWavevector wave j * tensor i j)) := by
      simp [nativeFluidStressDivergenceCoefficient, dotProduct, Fin.sum_univ_succ]
      ring
    rw [transverseProjection, if_neg waveZero, stressPressureCoefficient,
      if_neg waveZero, contraction, mul_div_assoc, sub_add_cancel]

end
end SaturationMonoid.NavierStokes.NativeStressCurlAlgebra
