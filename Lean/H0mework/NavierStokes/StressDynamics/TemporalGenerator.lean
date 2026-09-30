import H0mework.NavierStokes.StressResolvent.TemporalResolventGraph
import H0mework.NavierStokes.StressDynamics.PolynomialAction

set_option autoImplicit false
open scoped BigOperators Topology ENNReal

namespace SaturationMonoid.NavierStokes.NativeActualWorkGenerator

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointWholeMildReadWrite
open NativeRecoveryCoverage NativeRecoveryEscapeStress NativeRecoveryTimeGramRaw NativeRecoveryJointTimeKernel
open NativeSourceResolvent NativeRawStressAction NativeRecoveryTimeGramAction NativeTemporalResolvent

noncomputable section

variable {nu : Viscosity} {ledger : GeneratedWholeRestartVelocityEndpointUniformKineticViscousLedgerCore nu}
  {receipt : GeneratedWholeRestartVelocityEndpointWholeMildReadWriteReceipt ledger} {point : ℝ}
  {escape : SourceActionEscape receipt point}

def acceleration (stress : StressAt escape) (index : ℕ) (time : ℝ) : ComplexVorticityHilbertState :=
  NativeSourcePolynomialAction.sourceWord stress index NativeSourcePolynomialAction.velocity 2 time

theorem rate_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (rawRate stress index) (acceleration stress index time) time := by
  have actual := NativeSourcePolynomialAction.sourceWord_hasDerivAt stress index
    NativeSourcePolynomialAction.velocity 1 time inside
  change HasDerivAt (fun sample => NativeSourcePolynomialAction.sourceWord stress index NativeSourcePolynomialAction.velocity 1 sample)
    (acceleration stress index time) time at actual
  simpa only [NativeSourcePolynomialAction.sourceWord_velocityRate] using actual

theorem acceleration_continuousOn (stress : StressAt escape) (index : ℕ) :
    ContinuousOn (acceleration stress index) (Icc (0 : ℝ) 1) :=
  NativeSourcePolynomialAction.sourceWord_continuousOn stress index NativeSourcePolynomialAction.velocity 2

def remainderPath (stress : StressAt escape) (index : ℕ) (time : ℝ) : ComplexVorticityHilbertState :=
  rawField stress index time - rawField stress index 0 - time • rawRate stress index time

theorem remainder_hasDerivAt (stress : StressAt escape) (index : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (remainderPath stress index) (-time • acceleration stress index time) time := by
  have actual := ((rawField_hasDerivAt stress index time inside).sub_const (rawField stress index 0)).sub
    ((hasDerivAt_id time).smul (rate_hasDerivAt stress index time inside))
  convert! actual using 1
  simp

theorem remainder_source (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) :
    remainderPath stress index last.1 = (workRemainder stress pointLe index last).1 := by
  change _ = rawField stress index last.1 - rawField stress index 0 - last.1 •
    NativeCommonAdvectorAction.sourceOperator stress index last.1 (rawField stress index last.1)
  rw [NativeCommonAdvectorAction.source_diagonal stress index last.1 last.2]
  rfl

theorem remainder_generated (stress : StressAt escape) (pointLe : point ≤ 1) (index : ℕ)
    (last : Icc (0 : ℝ) 1) :
    (workRemainder stress pointLe index last).1 =
      ∫ time in (0 : ℝ)..last.1, -time • acceleration stress index time := by
  have subset := uIcc_subset_Icc zeroTime.2 last.2
  have write := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun time inside => remainder_hasDerivAt stress index time (subset inside))
    (((continuousOn_id.neg.smul (acceleration_continuousOn stress index)).mono subset).intervalIntegrable)
  simpa only [← remainder_source, remainderPath, zeroTime, zero_smul, sub_self, sub_zero] using write.symm

def remainderJet (stress : StressAt escape) (index : ℕ) : ℕ → ℝ → ComplexVorticityHilbertState
  | 0 => remainderPath stress index
  | order + 1 => fun time =>
      -(order : ℝ) • NativeSourcePolynomialAction.sourceWord stress index NativeSourcePolynomialAction.velocity
        (order + 1) time -
      time • NativeSourcePolynomialAction.sourceWord stress index NativeSourcePolynomialAction.velocity (order + 2) time

theorem remainderJet_hasDerivAt (stress : StressAt escape) (index order : ℕ) (time : ℝ)
    (inside : time ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (remainderJet stress index order) (remainderJet stress index (order + 1) time) time := by
  cases order with
  | zero =>
      simpa only [remainderJet, Nat.cast_zero, neg_zero, zero_smul, zero_sub, neg_smul] using!
        remainder_hasDerivAt stress index time inside
  | succ order =>
      have first := NativeSourcePolynomialAction.sourceWord_hasDerivAt stress index
        NativeSourcePolynomialAction.velocity (order + 1) time inside
      have second := NativeSourcePolynomialAction.sourceWord_hasDerivAt stress index
        NativeSourcePolynomialAction.velocity (order + 2) time inside
      have actual := (first.const_smul (-(order : ℝ))).sub ((hasDerivAt_id time).smul second)
      convert! actual using 1
      simp only [remainderJet, Nat.cast_add, Nat.cast_one, Nat.add_assoc, id_eq, one_smul, neg_smul,
        add_smul, one_smul]
      abel

end
end SaturationMonoid.NavierStokes.NativeActualWorkGenerator

namespace SaturationMonoid.NavierStokes.NativeActualResolventDifferential

open ContinuousLinearMap
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem inverse_hasDerivAt {path : ℝ → E →L[ℝ] E} {rate : E →L[ℝ] E} {time : ℝ}
    (actual : HasDerivAt path rate time) (unit : (E →L[ℝ] E)ˣ) (same : (unit : E →L[ℝ] E) = path time) :
    HasDerivAt (fun sample => Ring.inverse (path sample))
      (-((↑unit⁻¹ : E →L[ℝ] E) * rate * ↑unit⁻¹)) time := by
  have derivative := hasFDerivAt_ringInverse (𝕜 := ℝ) unit
  rw [same] at derivative
  convert! derivative.comp_hasDerivAt time actual using 1

theorem inverse_apply_hasDerivAt {path : ℝ → E →L[ℝ] E} {rate : E →L[ℝ] E}
    {load : ℝ → E} {loadRate : E} {time : ℝ} (actual : HasDerivAt path rate time)
    (loadActual : HasDerivAt load loadRate time)
    (unit : (E →L[ℝ] E)ˣ) (same : (unit : E →L[ℝ] E) = path time) :
    HasDerivAt (fun sample => Ring.inverse (path sample) (load sample))
      ((↑unit⁻¹ : E →L[ℝ] E) (loadRate - rate ((↑unit⁻¹ : E →L[ℝ] E) (load time)))) time := by
  have derivative := (inverse_hasDerivAt actual unit same).clm_apply loadActual
  have inverseAt : Ring.inverse (path time) = (↑unit⁻¹ : E →L[ℝ] E) := by rw [← same]; simp
  convert! derivative using 1
  rw [inverseAt, map_sub]
  change _ = -((↑unit⁻¹ : E →L[ℝ] E) (rate ((↑unit⁻¹ : E →L[ℝ] E) (load time)))) + _
  abel

theorem implicit_inverse_apply_hasDerivAt {action : ℝ → E →L[ℝ] E} {actionRate : E →L[ℝ] E}
    {load : ℝ → E} {loadRate : E} {time : ℝ} (actual : HasDerivAt action actionRate time)
    (loadActual : HasDerivAt load loadRate time) (unit : (E →L[ℝ] E)ˣ)
    (same : (unit : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E - time • action time) :
    HasDerivAt (fun sample => Ring.inverse (ContinuousLinearMap.id ℝ E - sample • action sample) (load sample))
      ((↑unit⁻¹ : E →L[ℝ] E)
        (loadRate + (action time + time • actionRate) ((↑unit⁻¹ : E →L[ℝ] E) (load time)))) time := by
  have derivative := (hasDerivAt_const time (ContinuousLinearMap.id ℝ E)).sub
    ((hasDerivAt_id time).smul actual)
  have source := inverse_apply_hasDerivAt derivative loadActual unit same
  convert! source using 1
  simp only [id_eq, one_smul, zero_sub, neg_apply, add_apply, smul_apply, sub_neg_eq_add]
  congr 2
  abel

end
end SaturationMonoid.NavierStokes.NativeActualResolventDifferential
