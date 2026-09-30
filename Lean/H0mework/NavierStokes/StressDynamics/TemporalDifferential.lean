import H0mework.NavierStokes.StressResolvent.TemporalResolventNext
import H0mework.NavierStokes.StressDynamics.TemporalGenerator
import Mathlib.Analysis.Normed.Module.ContinuousInverse

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
open scoped ContDiff

namespace SaturationMonoid.NavierStokes.NativeTemporalResolventReentry

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeSourceResolvent NativeFiniteActionResolvent NativeCommonAdvectorAction NativeRawStressAction
open NativeTemporalResolvent NativeTemporalResolventGraph
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger NativeActualWorkGenerator

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def action (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) : physicalSpace (modes stress index) →ₗ[ℝ] physicalSpace (modes stress index) :=
  physicalOperator (modes stress index) (modes_zero stress index) (modes_closed stress index) nu
    (advector stress pointLe index (.fixed time)) (advector_reality stress pointLe index (.fixed time))

def dotCLM (wave : IntegerWavevector) : ComplexCoordinateVector →L[ℝ] ℂ :=
  ∑ direction : Coordinate, complexWavevector wave direction • ContinuousLinearMap.proj direction

theorem dotCLM_apply (wave : IntegerWavevector) (value : ComplexCoordinateVector) :
    dotCLM wave value = complexWavevector wave ⬝ᵥ value := by
  simp [dotCLM, dotProduct, complexWavevector]

theorem frozen_smooth (frequencies : Finset IntegerWavevector) :
    ContDiff ℝ ∞ (frozenOperator frequencies nu) := by
  unfold frozenOperator
  apply ContDiff.sum
  intro wave inside
  apply ContDiff.clm_comp contDiff_const
  unfold rowCLM
  apply ContDiff.clm_comp contDiff_const
  apply ContDiff.sub _ contDiff_const
  unfold convectionCLM
  apply ContDiff.sum
  intro first firstMem
  apply ContDiff.sum
  intro second secondMem
  by_cases pair : first + second = wave
  · simp only [if_pos pair]
    have linear := ((dotCLM second).comp ((biotSavartVelocityCLM first).comp (evaluation first))).contDiff (n := ∞)
    change ContDiff ℝ ∞ (fun value =>
      (-((Complex.I * (2 * Real.pi : ℝ)) *
        (complexWavevector second ⬝ᵥ finiteStateVelocityCoefficient value first))) • evaluation second)
    have scalar : ContDiff ℝ ∞ (fun value : ComplexVorticityHilbertState =>
        -((Complex.I * (2 * Real.pi : ℝ)) *
          (complexWavevector second ⬝ᵥ finiteStateVelocityCoefficient value first))) := by
      apply ContDiff.neg
      apply ContDiff.mul contDiff_const
      convert! linear using 1
    exact scalar.smul_const (evaluation second)
  · simp only [if_neg pair]
    exact contDiff_const

def dotA (stress : StressAt escape) (index : ℕ) (time : ℝ) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  fderiv ℝ (frozenOperator (modes stress index) nu) ((stage stress index).trajectory time)
    (finiteStateVorticityGenerator (modes stress index) nu.coeff ((stage stress index).trajectory time))

theorem operator_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (sourceOperator stress index) (dotA stress index time) time :=
  ((frozen_smooth (nu := nu) (modes stress index)).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt
    time ((stage stress index).physical time inside).1

theorem acceleration_product (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    acceleration stress index time =
      dotA stress index time (rawField stress index time) +
        sourceOperator stress index time (rawRate stress index time) := by
  have original := rate_hasDerivAt stress index time inside
  have product := (operator_hasDerivAt stress index time inside).clm_apply
    (rawField_hasDerivAt stress index time inside)
  have same := product.hasDerivWithinAt.congr_of_mem
    (fun sample member => (source_diagonal stress index sample member).symm) inside
  exact (original.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc zero_lt_one time inside)).symm.trans
    (same.derivWithin (uniqueDiffOn_Icc zero_lt_one time inside))

def coordinateRead (frequencies : Finset IntegerWavevector) : ComplexVorticityHilbertState →L[ℝ]
    EuclideanSpace ℂ (frequencies × Coordinate) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : frequencies × Coordinate => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun entry => (ContinuousLinearMap.proj entry.2).comp (evaluation entry.1.1))

def coordinateInverse (frequencies : Finset IntegerWavevector) :
    EuclideanSpace ℂ (frequencies × Coordinate) →L[ℝ] physicalSpace frequencies :=
  (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := (coefficients frequencies).toContinuousLinearMap) (coefficients_injective frequencies)).leftInverse

def physicalRead (frequencies : Finset IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] physicalSpace frequencies :=
  (coordinateInverse frequencies).comp (coordinateRead frequencies)

theorem physicalRead_coe (frequencies : Finset IntegerWavevector) (value : physicalSpace frequencies) :
    physicalRead frequencies value.1 = value :=
  (ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional
    (f := (coefficients frequencies).toContinuousLinearMap) (coefficients_injective frequencies)).leftInverse_leftInverse value

def actionCurve (stress : StressAt escape) (index : ℕ) (time : ℝ) :
    physicalSpace (modes stress index) →L[ℝ] physicalSpace (modes stress index) :=
  (physicalRead (modes stress index)).comp
    ((sourceOperator stress index time).comp (physicalSpace (modes stress index)).subtypeL)

def actionCurveRate (stress : StressAt escape) (index : ℕ) (time : ℝ) :
    physicalSpace (modes stress index) →L[ℝ] physicalSpace (modes stress index) :=
  (physicalRead (modes stress index)).comp
    ((dotA stress index time).comp (physicalSpace (modes stress index)).subtypeL)

theorem actionCurve_original (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    actionCurve stress index time.1 = (action stress pointLe index time).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro value
  exact physicalRead_coe (modes stress index) (action stress pointLe index time value)

theorem actionCurve_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (actionCurve stress index) (actionCurveRate stress index time) time := by
  convert! (show HasDerivAt (fun t => (physicalRead (modes stress index)).comp
    ((sourceOperator stress index t).comp (physicalSpace (modes stress index)).subtypeL))
    (actionCurveRate stress index time) time from ?_) using 1
  simpa only [actionCurve, actionCurveRate, ContinuousLinearMap.comp_zero, ContinuousLinearMap.zero_comp,
    zero_add, add_zero] using
    (hasDerivAt_const time (physicalRead (modes stress index))).clm_comp
      ((operator_hasDerivAt stress index time inside).clm_comp
        (hasDerivAt_const time (physicalSpace (modes stress index)).subtypeL))

def loadCurve (stress : StressAt escape) (index : ℕ) (time : ℝ) : physicalSpace (modes stress index) :=
  physicalRead (modes stress index) (rawField stress index time)

def rateCurve (stress : StressAt escape) (index : ℕ) (time : ℝ) : physicalSpace (modes stress index) :=
  physicalRead (modes stress index) (rawRate stress index time)

def remainderCurve (stress : StressAt escape) (index : ℕ) (time : ℝ) : physicalSpace (modes stress index) :=
  physicalRead (modes stress index) (remainderPath stress index time)

theorem loadCurve_original (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) : loadCurve stress index time.1 = load stress pointLe index (.fixed time) := by
  exact physicalRead_coe _ (load stress pointLe index (.fixed time))

theorem loadCurve_coe (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) : (loadCurve stress index time.1).1 = rawField stress index time.1 := by
  rw [loadCurve_original stress pointLe index time]
  rfl

theorem rateCurve_coe (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) : (rateCurve stress index time.1).1 = rawRate stress index time.1 := by
  have same : (action stress pointLe index time (load stress pointLe index (.fixed time))).1 =
      rawRate stress index time.1 := source_diagonal stress index time.1 time.2
  rw [rateCurve, ← same, physicalRead_coe]

theorem loadCurve_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (loadCurve stress index) (rateCurve stress index time) time :=
  (physicalRead (modes stress index)).hasFDerivAt.comp_hasDerivAt time
    (rawField_hasDerivAt stress index time inside)

theorem remainderCurve_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (remainderCurve stress index)
      (-time • physicalRead (modes stress index) (acceleration stress index time)) time := by
  convert! (physicalRead (modes stress index)).hasFDerivAt.comp_hasDerivAt time
    (remainder_hasDerivAt stress index time inside) using 1
  exact (map_smul _ _ _).symm

theorem remainderCurve_original (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) : remainderCurve stress index time.1 = workRemainder stress pointLe index time := by
  rw [remainderCurve, remainder_source stress pointLe index time, physicalRead_coe]

def implicitCurve (stress : StressAt escape) (index : ℕ) (time : ℝ) :
    physicalSpace (modes stress index) →L[ℝ] physicalSpace (modes stress index) :=
  ContinuousLinearMap.id ℝ _ - time • actionCurve stress index time

theorem physical_acceleration (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    physicalRead (modes stress index) (acceleration stress index time.1) =
      actionCurveRate stress index time.1 (loadCurve stress index time.1) +
        actionCurve stress index time.1 (rateCurve stress index time.1) := by
  rw [acceleration_product stress index time.1 time.2, map_add]
  simp only [actionCurveRate, actionCurve, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    loadCurve_coe stress pointLe index time, rateCurve_coe stress pointLe index time]

/-- The complete physical-time parameter feed, including the generated work rate. -/
theorem source_feed_compatibility (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    -time.1 • physicalRead (modes stress index) (acceleration stress index time.1) +
      (actionCurve stress index time.1 + time.1 • actionCurveRate stress index time.1)
        (loadCurve stress index time.1) =
      implicitCurve stress index time.1 (rateCurve stress index time.1) := by
  have diagonal : actionCurve stress index time.1 (loadCurve stress index time.1) = rateCurve stress index time.1 := by
    simp only [actionCurve, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      loadCurve_coe stress pointLe index time, source_diagonal stress index time.1 time.2, rateCurve]
  rw [physical_acceleration stress pointLe index time]
  simp only [implicitCurve, add_apply, smul_apply,
    sub_apply, ContinuousLinearMap.id_apply, smul_add, neg_smul, diagonal]
  abel

def implicitUnit (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    (physicalSpace (modes stress index) →L[ℝ] physicalSpace (modes stress index))ˣ :=
  (transition stress pointLe index time).symm.toContinuousLinearEquiv.toUnit

theorem implicitUnit_eq (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    (implicitUnit stress pointLe index time : physicalSpace (modes stress index) →L[ℝ]
      physicalSpace (modes stress index)) = implicitCurve stress index time.1 := by
  rw [implicitCurve, actionCurve_original stress pointLe index time]
  rfl

def sourceLoad (stress : StressAt escape) (index : ℕ) (time : ℝ) : physicalSpace (modes stress index) :=
  loadCurve stress index 0 + remainderCurve stress index time

theorem reconstructed_value (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    (↑(implicitUnit stress pointLe index time)⁻¹ : physicalSpace (modes stress index) →L[ℝ]
      physicalSpace (modes stress index)) (sourceLoad stress index time.1) = loadCurve stress index time.1 := by
  change transition stress pointLe index time (sourceLoad stress index time.1) = _
  have initialRead : loadCurve stress index 0 = load stress pointLe index (.fixed zeroTime) :=
    loadCurve_original stress pointLe index zeroTime
  rw [sourceLoad, remainderCurve_original stress pointLe index time,
    initialRead, map_add,
    ← advance, transition_reconstructs, loadCurve_original stress pointLe index time]

/-- The corrected inverse consumes both original parameter actions and returns the physical rate. -/
theorem source_inverse_physical_derivative (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    HasDerivAt (fun sample => Ring.inverse (implicitCurve stress index sample) (sourceLoad stress index sample))
      (rateCurve stress index time.1) time.1 := by
  have input := (remainderCurve_hasDerivAt stress index time.1 time.2).const_add (loadCurve stress index 0)
  have inverse := NativeActualResolventDifferential.implicit_inverse_apply_hasDerivAt
    (actionCurve_hasDerivAt stress index time.1 time.2) input (implicitUnit stress pointLe index time)
    (implicitUnit_eq stress pointLe index time)
  have same := reconstructed_value stress pointLe index time
  change (↑(implicitUnit stress pointLe index time)⁻¹ : physicalSpace (modes stress index) →L[ℝ]
    physicalSpace (modes stress index)) (loadCurve stress index 0 + remainderCurve stress index time.1) = _ at same
  rw [same, source_feed_compatibility stress pointLe index time, ← implicitUnit_eq stress pointLe index time] at inverse
  have cancelled : (↑(implicitUnit stress pointLe index time)⁻¹ : physicalSpace (modes stress index) →L[ℝ]
      physicalSpace (modes stress index)) ((implicitUnit stress pointLe index time : physicalSpace (modes stress index) →L[ℝ]
      physicalSpace (modes stress index)) (rateCurve stress index time.1)) = rateCurve stress index time.1 :=
    (transition stress pointLe index time).apply_symm_apply _
  rw [cancelled] at inverse
  convert! inverse using 1

theorem source_inverse_original (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    (Ring.inverse (implicitCurve stress index time.1) (sourceLoad stress index time.1)).1 = rawField stress index time.1 := by
  have inverse : Ring.inverse (implicitCurve stress index time.1) =
      (↑(implicitUnit stress pointLe index time)⁻¹ : physicalSpace (modes stress index) →L[ℝ]
        physicalSpace (modes stress index)) := by rw [← implicitUnit_eq stress pointLe index time]; simp
  rw [inverse, reconstructed_value stress pointLe index time, loadCurve_coe stress pointLe index time]

theorem source_inverse_original_derivative (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) :
    HasDerivAt (fun sample => (Ring.inverse (implicitCurve stress index sample) (sourceLoad stress index sample)).1)
      (rawRate stress index time.1) time.1 := by
  have original := (physicalSpace (modes stress index)).subtypeL.hasFDerivAt.comp_hasDerivAt time.1
    (source_inverse_physical_derivative stress pointLe index time)
  simp only [Submodule.subtypeL_apply, rateCurve_coe stress pointLe index time] at original
  convert! original using 1

theorem inverse_fixed_load_derivative (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (time : Icc (0 : ℝ) 1) (value : physicalSpace (modes stress index)) :
    HasDerivAt (fun sample => Ring.inverse (implicitCurve stress index sample) value)
      (transition stress pointLe index time ((actionCurve stress index time.1 + time.1 • actionCurveRate stress index time.1)
        (transition stress pointLe index time value))) time.1 := by
  have inverse := NativeActualResolventDifferential.implicit_inverse_apply_hasDerivAt
    (actionCurve_hasDerivAt stress index time.1 time.2) (hasDerivAt_const time.1 value)
    (implicitUnit stress pointLe index time) (implicitUnit_eq stress pointLe index time)
  simp only [zero_add] at inverse
  convert! inverse using 1

end
end SaturationMonoid.NavierStokes.NativeTemporalResolventReentry
