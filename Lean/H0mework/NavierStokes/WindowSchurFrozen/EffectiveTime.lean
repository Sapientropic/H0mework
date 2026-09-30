import H0mework.NavierStokes.WindowSchurFrozen.Effective

set_option autoImplicit false
open scoped BigOperators Topology ContDiff
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryEffectiveTime
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeWholeResolvent NativePhysicalPairing
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryEffectiveInverse (Operator average generator unit)
noncomputable section
variable {nu : Viscosity}

section Compression
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem compress_derivative (left : E →L[ℝ] F) (right : F →L[ℝ] E)
    (curve : ℝ → E →L[ℝ] E) (rate : E →L[ℝ] E) (time : ℝ) (actual : HasDerivAt curve rate time) :
    HasDerivAt (fun s => left.comp ((curve s).comp right)) (left.comp (rate.comp right)) time := by
  have source := (hasDerivAt_const time left).clm_comp (actual.clm_comp (hasDerivAt_const time right))
  simpa only [ContinuousLinearMap.zero_comp,ContinuousLinearMap.comp_zero,zero_add,add_zero] using source

private theorem compress_smooth (left : E →L[ℝ] F) (right : F →L[ℝ] E)
    (curve : ℝ → E →L[ℝ] E) (smooth : ContDiff ℝ ∞ curve) :
    ContDiff ℝ ∞ (fun s => left.comp ((curve s).comp right)) :=
  contDiff_const.clm_comp (smooth.clm_comp contDiff_const)
end Compression

private theorem smooth_leibniz {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (a b : ℝ → R) (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (a*b) time=
      ∑ i∈Finset.range (order+1),(order.choose i : R)*iteratedDeriv i a time*iteratedDeriv (order-i) b time := by
  have smoothA : ContDiff ℝ (order : ℕ) a := ha.of_le (by exact_mod_cast (ENat.natCast_lt_top order).le)
  have smoothB : ContDiff ℝ (order : ℕ) b := hb.of_le (by exact_mod_cast (ENat.natCast_lt_top order).le)
  exact iteratedDeriv_mul (𝕜 := ℝ) (𝔸 := R) (n := order) smoothA.contDiffAt smoothB.contDiffAt

private theorem inverse_derivative {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]
    (curve : ℝ → R) (rate : R) (time : ℝ) (invertible : Rˣ) (original : (invertible : R)=curve time)
    (actual : HasDerivAt curve rate time) :
    HasDerivAt (fun s => Ring.inverse (curve s)) (-((invertible⁻¹ : Rˣ)*rate*(invertible⁻¹ : Rˣ))) time := by
  have inverse := hasFDerivAt_ringInverse (𝕜 := ℝ) invertible
  rw [original] at inverse
  simpa only [Function.comp_def,neg_apply,ContinuousLinearMap.mulLeftRight_apply] using
    inverse.comp_hasDerivAt time actual

theorem average_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (average seed M order) (average seed M (order+1) time) time := by
  simpa only [NativeWindowHistoryEffectiveInverse.average] using! compress_derivative
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)) (includeCLM (modes M) (modes_closed M))
    (NativeWindowHistoryInverseWindow.average seed M order) (NativeWindowHistoryInverseWindow.average seed M (order+1) time)
    time (NativeWindowHistoryInverseWindow.average_hasDerivAt seed M order time)

theorem average_contDiff (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) :
    ContDiff ℝ ∞ (average seed M order) := by
  simpa only [NativeWindowHistoryEffectiveInverse.average] using! compress_smooth
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)) (includeCLM (modes M) (modes_closed M))
    (NativeWindowHistoryInverseWindow.average seed M order) (NativeWindowHistoryInverseWindow.average_contDiff seed M order)

theorem average_iterated (seed : GeneratedWholeRestartCurrent nu) (M base order : ℕ) :
    iteratedDeriv order (average seed M base)=average seed M (base+order) := by
  induction order with
  | zero => simp only [iteratedDeriv_zero,Nat.add_zero]
  | succ order ih =>
    rw [iteratedDeriv_succ,ih]
    funext time
    exact (average_hasDerivAt seed M (base+order) time).deriv

theorem generator_contDiff (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) :
    ContDiff ℝ ∞ (generator seed M) := by
  have same : generator seed M=fun t => Ring.inverse (average seed M 0 t) :=
    funext fun t => (NativeWindowHistoryEffectiveInverse.inverse_original seed M t).symm
  rw [same,contDiff_iff_contDiffAt]
  intro time
  have inverse := contDiffAt_ringInverse ℝ (R := Operator M) (n := ∞) (unit seed M time)
  exact inverse.comp time (average_contDiff seed M 0).contDiffAt

theorem generator_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    HasDerivAt (generator seed M) (-(generator seed M time*average seed M 1 time*generator seed M time)) time := by
  have source := inverse_derivative (R := Operator M) (average seed M 0) (average seed M 1 time) time
    (unit seed M time) rfl (average_hasDerivAt seed M 0 time)
  change HasDerivAt (fun s => Ring.inverse (average seed M 0 s))
    (-(generator seed M time*average seed M 1 time*generator seed M time)) time at source
  simpa only [NativeWindowHistoryEffectiveInverse.inverse_original] using! source

def jet (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) : ℝ → Operator M :=
  iteratedDeriv order (generator seed M)

theorem jet_zero (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) : jet seed M 0=generator seed M := iteratedDeriv_zero

theorem jet_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    HasDerivAt (jet seed M order) (jet seed M (order+1) time) time := by
  have source := ((generator_contDiff seed M).differentiable_iteratedDeriv order (by exact_mod_cast (ENat.natCast_lt_top order))) time
  simpa only [jet,iteratedDeriv_succ] using source.hasDerivAt

theorem jet_leibniz (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    (∑ i∈Finset.range (order+1),(order.choose i : Operator M)*average seed M i time*jet seed M (order-i) time)=
      if order=0 then 1 else 0 := by
  have product : average seed M 0*generator seed M=fun _ => (1 : Operator M) := by
    funext t
    exact (unit seed M t).val_inv
  have source := smooth_leibniz (R := Operator M) (average seed M 0) (generator seed M)
    (average_contDiff seed M 0) (generator_contDiff seed M) order time
  rw [product,iteratedDeriv_const] at source
  simpa only [average_iterated,Nat.zero_add,jet] using! source.symm

theorem jet_recurrence (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ) (time : ℝ) :
    jet seed M (order+1) time= -generator seed M time*
      ∑ i∈Finset.range (order+1),((order+1).choose (i+1) : Operator M)*average seed M (i+1) time*jet seed M (order-i) time := by
  have paid := jet_leibniz seed M (order+1) time
  rw [Finset.sum_range_succ'] at paid
  simp only [Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero,Nat.add_sub_add_right,show ¬order+1=0 by omega,if_false] at paid
  have source := congrArg (fun A : Operator M => generator seed M time*A) paid
  have left : generator seed M time*average seed M 0 time=1 := (unit seed M time).inv_val
  rw [mul_add,← mul_assoc,left,one_mul,mul_zero] at source
  simpa only [neg_mul] using! eq_neg_of_add_eq_zero_right source

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem jet_next (seed : GeneratedWholeRestartCurrent nu) (M order : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    jet seed M order (step.2.clockAdvance+time)=jet step.1 M order time := by
  induction order using Nat.strong_induction_on with
  | h order ih =>
    cases order with
    | zero => exact NativeWindowHistoryEffectiveInverse.generator_next seed M step generated time time0
    | succ order =>
      rw [jet_recurrence,jet_recurrence,NativeWindowHistoryEffectiveInverse.generator_next seed M step generated time time0]
      apply congrArg (fun A : Operator M => -generator step.1 M time*A)
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg₂ (fun A B : Operator M => ((order+1).choose (i+1) : Operator M)*A*B)
        (NativeWindowHistoryEffectiveInverse.average_next seed M (i+1) step generated time time0)
        (ih (order-i) (by omega))

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryEffectiveTime
