import H0mework.Versions.X.NavierStokes.TimeJets.TimeCarrier
import H0mework.Versions.X.NavierStokes.PhysicalJets.CorrectionTime

set_option autoImplicit false
open scoped BigOperators ENNReal Topology

namespace SaturationMonoid.NavierStokes.NativeTimeJetObservation

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientNativeFluidMedium
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartPairDuhamelKineticTriadRedirect
open NativeStressCurlAlgebra NativeStressSource NativeHigherTimeJets
open NativeFullOrderAction NativeFullOrderFlux NativeFullOrderSynthesis NativeFullOrderActionMoments
open NativeTimeJetCarrier NativeCorrectionTime

noncomputable section

def project {index : ℕ} (modes : Finset IntegerWavevector) (profile : Profile index) : Profile index where
  value time := complexSharpSupportProjection modes (profile.value time)
  budget := profile.budget
  continuous := by
    simpa only [Function.comp_def, projectionCLM_apply] using (projectionCLM modes).continuous.comp profile.continuous
  paid order time := by
    apply (profile.paid order time).of_nonneg_of_le
    · intro wave
      exact mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)
    · intro wave
      by_cases inside : wave ∈ modes <;>
        simp [velocityMomentDensity, complexSharpSupportProjection_apply, inside,
          complexCoordinateVectorNormSq]
      exact mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
  bound order time := by
    apply le_trans _ (profile.bound order time)
    rw [tsum_eq_sum (s := modes)]
    · have same : (∑ wave ∈ modes, velocityMomentDensity order
          (complexSharpSupportProjection modes (profile.value time)) wave) =
        ∑ wave ∈ modes, velocityMomentDensity order (profile.value time) wave := by
        apply Finset.sum_congr rfl
        intro wave inside
        simp only [velocityMomentDensity, complexSharpSupportProjection_apply, if_pos inside]
      rw [same]
      exact (profile.paid order time).sum_le_tsum modes
        (fun wave _ => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _))
    · intro wave outside
      simp [velocityMomentDensity, complexSharpSupportProjection_apply, outside,
        complexCoordinateVectorNormSq]

@[simp] theorem project_value {index : ℕ} (modes : Finset IntegerWavevector)
    (profile : Profile index) (time : Time index) :
    (project modes profile).value time = complexSharpSupportProjection modes (profile.value time) := rfl

@[simp] theorem project_budget {index : ℕ} (modes : Finset IntegerWavevector)
    (profile : Profile index) (order : ℕ) : (project modes profile).budget order = profile.budget order := rfl

theorem curl_density_le (order : ℕ) (rows : IntegerWavevector → ComplexCoordinateVector)
    (wave : IntegerWavevector) :
    rawMoment order (fun k => fourierCurlCoefficient k (rows k)) wave ≤
      (2 * Real.pi) ^ 2 * rawMoment (order + 1) rows wave := by
  have curl := curl_amplitude_le wave (rows wave)
  have frequency := normSq_le_frequencySize_sq wave
  have source := mul_le_mul_of_nonneg_left curl (sq_nonneg (frequencySize wave ^ order))
  have raised := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left frequency (sq_nonneg (2 * Real.pi)))
    (complexCoordinateAmplitudeSq_nonneg (rows wave))
  have scaled := mul_le_mul_of_nonneg_left raised (sq_nonneg (frequencySize wave ^ order))
  apply source.trans scaled |>.trans_eq
  unfold rawMoment
  rw [pow_succ]
  simp only [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  ring

def profileCurl {index : ℕ} (profile : Profile index) : Profile index := by
  let rows (time : Time index) (wave : IntegerWavevector) := fourierCurlCoefficient wave (profile.value time wave)
  let budget order := (2 * Real.pi) ^ 2 * profile.budget (order + 1)
  have controls (order : ℕ) (time : Time index) : Summable (rawMoment order (rows time)) ∧
      (∑' wave, rawMoment order (rows time) wave) ≤ budget order := by
    have source := (profile.paid (order + 1) time).mul_left ((2 * Real.pi) ^ 2)
    have point := curl_density_le order (profile.value time)
    have paid := source.of_nonneg_of_le
      (fun wave => mul_nonneg (sq_nonneg _) (complexCoordinateVectorNormSq_nonneg _)) point
    refine ⟨paid, ?_⟩
    apply (paid.tsum_le_tsum point source).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (profile.bound (order + 1) time) (sq_nonneg _)
  apply assemble rows budget _ (fun order time => (controls order time).1) (fun order time => (controls order time).2)
  intro wave
  exact (fourierCurlCoefficientContinuousLinearMap wave).continuous.comp
    ((lp.evalCLM ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).continuous.comp profile.continuous)

@[simp] theorem profileCurl_row {index : ℕ} (profile : Profile index) (time : Time index)
    (wave : IntegerWavevector) :
    (profileCurl profile).value time wave = fourierCurlCoefficient wave (profile.value time wave) := rfl

@[simp] theorem profileCurl_budget {index : ℕ} (profile : Profile index) (order : ℕ) :
    (profileCurl profile).budget order = (2 * Real.pi) ^ 2 * profile.budget (order + 1) := rfl

def correctionProfile {index : ℕ} (modes : Finset IntegerWavevector)
    (left right : Profile index) : Profile index :=
  profileCurl (add (project modes (bilinear left right))
    (scale (-1) (bilinear (project modes left) (project modes right))))

theorem correctionProfile_row {index : ℕ} (modes : Finset IntegerWavevector)
    (left right : Profile index) (time : Time index) (wave : IntegerWavevector) :
    (correctionProfile modes left right).value time wave =
      nativeFluidConstitutiveVorticityAction
        ((fun k => if k ∈ modes then mixedFlux (left.value time) (right.value time) k else 0) -
          mixedFlux (complexSharpSupportProjection modes (left.value time))
            (complexSharpSupportProjection modes (right.value time))) wave := by
  simp only [correctionProfile, profileCurl_row, add, scale, project_value,
    lp.coeFn_add, lp.coeFn_neg, Pi.add_apply, Pi.neg_apply,
    neg_smul, one_smul, complexSharpSupportProjection_apply, bilinear_row]
  rw [← sub_eq_add_neg, ← fourierCurlCoefficientContinuousLinearMap_apply, map_sub]
  rw [fourierCurlCoefficientContinuousLinearMap_apply, fourierCurlCoefficientContinuousLinearMap_apply]
  simp only [projectedDivergenceCLM_apply, fourierCurlCoefficient_transverseProjection]
  rw [← wholeStressActionCLM_apply, map_sub]
  simp only [Pi.sub_apply, wholeStressActionCLM_apply, nativeFluidConstitutiveVorticityAction_projection]
  by_cases inside : wave ∈ modes
  · simp only [if_pos inside, fourierCurlCoefficient_transverseProjection]
    rfl
  · simp only [if_neg inside, zero_sub]
    rw [← fourierCurlCoefficientContinuousLinearMap_apply, map_zero, zero_sub]
    rfl

def correctionPairBudget {index : ℕ} (left right : Profile index) (order : ℕ) : ℝ :=
  4 * (2 * Real.pi) ^ 2 * (9 * (2 * Real.pi) ^ 2 * mixedBudget left right (order + 2))

theorem correctionProfile_budget {index : ℕ} (modes : Finset IntegerWavevector)
    (left right : Profile index) (order : ℕ) :
    (correctionProfile modes left right).budget order = correctionPairBudget left right order := by
  simp only [correctionProfile, profileCurl_budget, add, scale, project_budget, bilinear_budget,
    mixedBudget, Profile.majorantBudget, correctionPairBudget]
  ring

end
end SaturationMonoid.NavierStokes.NativeTimeJetObservation
