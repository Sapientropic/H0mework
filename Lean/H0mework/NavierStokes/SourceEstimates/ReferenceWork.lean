import H0mework.NavierStokes.SourceEstimates.ReferencePair
import H0mework.NavierStokes.SourceEstimates.ReferenceTransport

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceWork

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow

noncomputable section

def product (error : ComplexVorticityHilbertState) (first second : IntegerWavevector) : Real :=
  vorticityRowAmplitude error (first + second) * vorticityRowAmplitude error second

private theorem product_budget (error : ComplexVorticityHilbertState) (first : IntegerWavevector) :
    Summable (product error first) ∧
      (∑' second, product error first second) ≤ wholeVorticityEuclideanMass error := by
  have shifted : Summable fun second : IntegerWavevector =>
      vorticityRowAmplitude error (first + second) ^ 2 :=
    (Equiv.addLeft first).summable_iff.mpr (summable_vorticityRowAmplitude_sq error)
  have cauchy := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two
    (fun second => vorticityRowAmplitude_nonneg error (first + second))
    (vorticityRowAmplitude_nonneg error)
    (by simpa only [Real.rpow_two] using shifted)
    (by simpa only [Real.rpow_two] using summable_vorticityRowAmplitude_sq error)
  have shiftedMass : (∑' second, vorticityRowAmplitude error (first + second) ^ 2) =
      wholeVorticityEuclideanMass error :=
    (Equiv.addLeft first).tsum_eq (fun second => vorticityRowAmplitude error second ^ 2)
  have bound : (∑' second, product error first second) ≤
      Real.sqrt (wholeVorticityEuclideanMass error) * Real.sqrt (wholeVorticityEuclideanMass error) := by
    simpa [product, Real.rpow_two, one_div, shiftedMass, wholeVorticityEuclideanMass,
      Real.sqrt_eq_rpow] using cauchy.2
  refine ⟨cauchy.1, ?_⟩
  have massNonneg : 0 ≤ wholeVorticityEuclideanMass error :=
    tsum_nonneg fun wave => sq_nonneg (vorticityRowAmplitude error wave)
  simpa only [← pow_two, Real.sq_sqrt massNonneg] using bound

private theorem work_budget (error : ComplexVorticityHilbertState) (first : IntegerWavevector)
    (value : IntegerWavevector → Real) (coefficient : Real) (coefficientNonneg : 0 ≤ coefficient)
    (bound : ∀ second, |value second| ≤ coefficient * product error first second) :
    Summable value ∧ |∑' second, value second| ≤ coefficient * wholeVorticityEuclideanMass error := by
  have source := product_budget error first
  have majorant := source.1.mul_left coefficient
  have absolute : Summable fun second => |value second| :=
    majorant.of_nonneg_of_le (fun second => abs_nonneg _) bound
  have summed := absolute.tsum_le_tsum bound majorant
  rw [tsum_mul_left] at summed
  refine ⟨summable_abs_iff.mp absolute, ?_⟩
  have triangle : |∑' second, value second| ≤ ∑' second, |value second| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm (f := value) (by simpa only [Real.norm_eq_abs] using absolute)
  exact triangle.trans (summed.trans (mul_le_mul_of_nonneg_left source.2 coefficientNonneg))

def leftWork (reference error : ComplexVorticityHilbertState)
    (first second : IntegerWavevector) : Real :=
  complexCoordinateRealInner (error (first + second))
    (ReferencePair.stretching (reference first) (error second) second)

def rightWork (reference error : ComplexVorticityHilbertState)
    (first second : IntegerWavevector) : Real :=
  complexCoordinateRealInner (error (first + second))
    (ReferencePair.stretching (error second) (reference first) first)

def derivativeWork (reference error : ComplexVorticityHilbertState)
    (first second : IntegerWavevector) : Real :=
  complexCoordinateRealInner (error (first + second))
    (ReferencePair.transport (error second) (reference first) second first)

/-- Both original bilinear placements share one generated output frequency. -/
def pairWork (reference error : ComplexVorticityHilbertState)
    (first second : IntegerWavevector) : Real :=
  complexCoordinateRealInner (error (first + second))
    (finiteStateVorticityBilinearPairContribution reference error (first, second) +
      finiteStateVorticityBilinearPairContribution error reference (second, first))

theorem pairWork_eq (reference error : ComplexVorticityHilbertState) (first second : IntegerWavevector) :
    pairWork reference error first second =
      leftWork reference error first second + rightWork reference error first second -
        derivativeWork reference error first second - ReferenceTransport.work reference error first second := by
  unfold pairWork leftWork rightWork derivativeWork ReferenceTransport.work
  rw [ReferencePair.bilinear_eq, ReferencePair.bilinear_eq,
    complexCoordinateRealInner_add_right, complexCoordinateRealInner_sub_right,
    complexCoordinateRealInner_sub_right]
  ring

private theorem three_budgets (reference error : ComplexVorticityHilbertState)
    (first : IntegerWavevector) :
    (Summable (leftWork reference error first) ∧
      |∑' second, leftWork reference error first second| ≤
        vorticityRowAmplitude reference first * wholeVorticityEuclideanMass error) ∧
    (Summable (rightWork reference error first) ∧
      |∑' second, rightWork reference error first second| ≤
        vorticityRowAmplitude reference first * wholeVorticityEuclideanMass error) ∧
    (Summable (derivativeWork reference error first) ∧
      |∑' second, derivativeWork reference error first second| ≤
        (Real.sqrt (integerWaveNormSq first) * vorticityRowAmplitude reference first) *
          wholeVorticityEuclideanMass error) := by
  constructor
  · apply work_budget error first _ _ (vorticityRowAmplitude_nonneg _ _)
    intro second
    have bound := ReferencePair.stretchingWork_abs_le
      (error (first + second)) (reference first) (error second) second
    simpa only [leftWork, product, vorticityRowAmplitude, mul_assoc, mul_left_comm, mul_comm] using bound
  · constructor
    · apply work_budget error first _ _ (vorticityRowAmplitude_nonneg _ _)
      intro second
      have bound := ReferencePair.stretchingWork_abs_le
        (error (first + second)) (error second) (reference first) first
      simpa only [rightWork, product, vorticityRowAmplitude, mul_assoc, mul_left_comm, mul_comm] using bound
    · apply work_budget error first _ _
        (mul_nonneg (Real.sqrt_nonneg _) (vorticityRowAmplitude_nonneg _ _))
      intro second
      have bound := ReferencePair.transportWork_abs_le
        (error (first + second)) (error second) (reference first) second first
      rw [Real.sqrt_mul (integerWaveNormSq_nonneg first)] at bound
      simpa only [derivativeWork, product, vorticityRowAmplitude, mul_assoc, mul_left_comm, mul_comm] using bound

def slice (reference error : ComplexVorticityHilbertState) (first : IntegerWavevector) : Real :=
  ∑' second, pairWork reference error first second

/-- The complete mixed slice is controlled by error mass; the background
frequency is the only differentiated frequency in the resulting bound. -/
theorem slice_bound (reference error : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality error)
    (gradient : Summable fun wave : IntegerWavevector => integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (error wave)) (first : IntegerWavevector) :
    Summable (pairWork reference error first) ∧
      |slice reference error first| ≤
        ((2 + Real.sqrt (integerWaveNormSq first)) * vorticityRowAmplitude reference first) *
          wholeVorticityEuclideanMass error := by
  rcases three_budgets reference error first with ⟨left, right, differentiated⟩
  have transport := ReferenceTransport.work_hasSum_zero reference error reality gradient first
  have total := ((left.1.hasSum.add right.1.hasSum).sub differentiated.1.hasSum).sub transport
  have complete : HasSum (pairWork reference error first)
      ((∑' second, leftWork reference error first second) +
        (∑' second, rightWork reference error first second) -
          (∑' second, derivativeWork reference error first second)) := by
    simpa only [Pi.sub_apply, Pi.add_apply, sub_zero, ← pairWork_eq] using total
  refine ⟨complete.summable, ?_⟩
  unfold slice
  rw [complete.tsum_eq]
  let leftSum : Real := ∑' second, leftWork reference error first second
  let rightSum : Real := ∑' second, rightWork reference error first second
  let derivativeSum : Real := ∑' second, derivativeWork reference error first second
  have triangle : |leftSum + rightSum - derivativeSum| ≤ |leftSum| + |rightSum| + |derivativeSum| :=
    (abs_sub (leftSum + rightSum) derivativeSum).trans
      (add_le_add (abs_add_le leftSum rightSum) (le_refl |derivativeSum|))
  have paid := add_le_add (add_le_add left.2 right.2) differentiated.2
  exact triangle.trans (paid.trans_eq (by ring))

end
end SaturationMonoid.NavierStokes.ReferenceWork
