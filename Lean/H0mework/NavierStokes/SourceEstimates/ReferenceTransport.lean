import H0mework.NavierStokes.SourceEstimates.ReferencePair
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger
import H0mework.NavierStokes.WholeSpace.InfiniteFixedOutputNonlinearRow

set_option autoImplicit false

namespace SaturationMonoid.NavierStokes.ReferenceTransport

open Matrix
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientGeneratedShellViscousParseval
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity

noncomputable section

def work (reference error : ComplexVorticityHilbertState) (first second : IntegerWavevector) : Real :=
  complexCoordinateRealInner (error (first + second))
    (ReferencePair.transport (reference first) (error second) first second)

/-- The reference velocity is transverse; its transport pairs two slots of
the same error field and reverses under the original frequency involution. -/
theorem work_swap (reference error : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality error) (first second : IntegerWavevector) :
    work reference error first (outputNegSecondEquiv first second) =
      -work reference error first second := by
  have output : first + outputNegSecondEquiv first second = waveNeg second := by
    ext coordinate
    simp [outputNegSecondEquiv, waveNeg]
  have reflected : error (outputNegSecondEquiv first second) = vectorConj (error (first + second)) :=
    reality (first + second)
  have add : complexWavevector (first + second) =
      complexWavevector first + complexWavevector second := by
    ext coordinate
    simp [complexWavevector]
  have derivative : complexWavevector (outputNegSecondEquiv first second) ⬝ᵥ
      biotSavartVelocityCoefficient first (reference first) =
        -(complexWavevector second ⬝ᵥ biotSavartVelocityCoefficient first (reference first)) := by
    rw [outputNegSecondEquiv_apply, complexWavevector_waveNeg, add, neg_dotProduct, add_dotProduct,
      complexWavevector_dot_biotSavartVelocityCoefficient]
    simp
  unfold work ReferencePair.transport
  rw [output, reality second, reflected, derivative,
    complexCoordinateRealInner_eq_re_dot, complexCoordinateRealInner_eq_re_dot,
    vectorConj_involutive, dotProduct_smul, dotProduct_smul,
    dotProduct_comm (error second) (vectorConj (error (first + second)))]
  simp

/-- The actual H¹ error pays absolute convergence of each full transport slice. -/
theorem work_summable (reference error : ComplexVorticityHilbertState)
    (gradient : Summable fun wave : IntegerWavevector => integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (error wave)) (first : IntegerWavevector) :
    Summable (work reference error first) := by
  let amplitude := fun wave => Real.sqrt (complexCoordinateAmplitudeSq (error (first + wave)))
  let differentiated := fun wave =>
    Real.sqrt (integerWaveNormSq wave * complexCoordinateAmplitudeSq (error wave))
  have shifted : Summable fun wave : IntegerWavevector => amplitude wave ^ 2 := by
    change Summable fun wave : IntegerWavevector => vorticityRowAmplitude error (first + wave) ^ 2
    exact (Equiv.addLeft first).summable_iff.mpr (summable_vorticityRowAmplitude_sq error)
  have differentiatedSq : Summable fun wave : IntegerWavevector => differentiated wave ^ 2 := by
    have equality : (fun wave : IntegerWavevector => differentiated wave ^ 2) =
        (fun wave => integerWaveNormSq wave * complexCoordinateAmplitudeSq (error wave)) := by
      funext wave
      exact Real.sq_sqrt (mul_nonneg (integerWaveNormSq_nonneg _) (complexCoordinateAmplitudeSq_nonneg _))
    rw [equality]
    exact gradient
  have pair := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two
    (fun wave => Real.sqrt_nonneg (complexCoordinateAmplitudeSq (error (first + wave))))
    (fun wave => Real.sqrt_nonneg (integerWaveNormSq wave * complexCoordinateAmplitudeSq (error wave)))
    (by simpa only [Real.rpow_two] using shifted)
    (by simpa only [Real.rpow_two] using differentiatedSq)
  have majorant : Summable fun wave : IntegerWavevector => amplitude wave *
      Real.sqrt (complexCoordinateAmplitudeSq (reference first)) * differentiated wave := by
    simpa only [amplitude, differentiated, mul_assoc, mul_left_comm, mul_comm] using
      pair.1.mul_left (Real.sqrt (complexCoordinateAmplitudeSq (reference first)))
  have absolute : Summable fun wave => |work reference error first wave| :=
    majorant.of_nonneg_of_le (fun wave => abs_nonneg _) fun wave =>
      ReferencePair.transportWork_abs_le (error (first + wave)) (reference first) (error wave) first wave
  exact summable_abs_iff.mp absolute

theorem work_hasSum_zero (reference error : ComplexVorticityHilbertState)
    (reality : FiniteStateFourierReality error)
    (gradient : Summable fun wave : IntegerWavevector => integerWaveNormSq wave *
      complexCoordinateAmplitudeSq (error wave)) (first : IntegerWavevector) :
    HasSum (work reference error first) 0 := by
  have reindex := (outputNegSecondEquiv first).tsum_eq (work reference error first)
  simp_rw [work_swap reference error reality first] at reindex
  rw [tsum_neg] at reindex
  have zero : (∑' wave, work reference error first wave) = 0 := by linarith
  simpa only [zero] using (work_summable reference error gradient first).hasSum

end
end SaturationMonoid.NavierStokes.ReferenceTransport
