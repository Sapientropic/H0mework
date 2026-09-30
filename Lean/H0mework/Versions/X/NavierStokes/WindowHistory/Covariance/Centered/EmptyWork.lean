import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.JointPositiveBudget

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredEmptyWorkPaid
open Set
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (finiteHistory H)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistoryAnnihilationControl (laplacianFiber)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
variable {nu : Viscosity}

theorem source_empty_retained_rate (seed : GeneratedWholeRestartCurrent nu)
    (M : ℕ) (time : ℝ) :
    NativeWindowHistoryAllOrderWord.retained seed M [] time=
      mean (NativeWindowHistoryOseen.rateHistory seed M time)-
        NativeWindowHistorySchurAction.effective seed M time
          (mean (finiteHistory seed time M)) := by
  let v:=NativeWindowHistoryAllOrderWord.value seed M []
  have same (s : ℝ) : v s=mean (finiteHistory seed s M) :=
    NativeWindowHistoryMeanPhysicalJet.include_mean seed M s
  have raw:HasDerivAt (fun t => mean (finiteHistory seed t M))
      (mean (NativeWindowHistoryOseen.rateHistory seed M time)) time :=
    mean.hasFDerivAt.comp_hasDerivAt time
      (NativeWindowHistoryOseen.history_hasDerivAt seed M time)
  have rate:HasDerivAt v (mean (NativeWindowHistoryOseen.rateHistory seed M time)) time :=
    raw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => same s)
  have source:=NativeWindowHistoryAllOrderWord.value_hasDerivAt seed M [] time
  have identity:=source.unique rate
  rw [show NativeWindowHistoryAllOrderWord.value seed M [] time=
    mean (finiteHistory seed time M) from same time] at identity
  apply eq_sub_of_add_eq
  rw [add_comm]
  exact identity

private theorem square_three {E : Type*} [SeminormedAddCommGroup E]
    (x y z : E) : ‖x-y+z‖^2≤3*(‖x‖^2+‖y‖^2+‖z‖^2) := by
  have xy:=norm_sub_le x y
  have xyz:=norm_add_le (x-y) z
  have upper : ‖x-y+z‖≤‖x‖+‖y‖+‖z‖ := by linarith only [xy,xyz]
  have squared:=pow_le_pow_left₀ (norm_nonneg _) upper 2
  nlinarith only [squared,sq_nonneg (‖x‖-‖y‖),sq_nonneg (‖x‖-‖z‖),
    sq_nonneg (‖y‖-‖z‖)]

private theorem square_two {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x+y‖^2≤2*(‖x‖^2+‖y‖^2) := by
  have upper:=norm_add_le x y
  have squared:=pow_le_pow_left₀ (norm_nonneg _) upper 2
  nlinarith only [squared,sq_nonneg (‖x‖-‖y‖)]

private theorem inner_young {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) :
    2*inner ℝ x y≤‖x‖^2+‖y‖^2 := by
  have pair:=real_inner_le_norm x y
  nlinarith only [pair,sq_nonneg (‖x‖-‖y‖)]

theorem source_empty_work_quadratic (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) :
    ∃A B : ℝ,0≤A ∧0≤B ∧∀M (time : ℝ),time∈Icc 0 horizon →
      let w:=mean (finiteHistory seed time M)
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M w)
        (NativeWindowHistoryAllOrderWord.retained seed M [] time)≤
          A*‖laplacianFiber nu M w‖^2+B := by
  obtain ⟨C,C0,lower⟩:=NativeWindowHistoryAllOrderPrincipal.source_lower_bound seed horizon 1 (by norm_num)
  let J0:=NativeForwardWindowJets.budget seed 0
  let J1:=NativeForwardWindowJets.budget seed 1
  let A:=3+5*nu.coeff^2
  let B:=(2+3*C)*J0^2+3*J1^2
  have A0 : 0≤A:=by dsimp only [A]; positivity
  have B0 : 0≤B:=by dsimp only [B]; positivity
  refine ⟨A,B,A0,B0,fun M time inside => ?_⟩
  let w:=mean (finiteHistory seed time M)
  let v:=NativeWindowHistoryMeanPhysicalJet.physicalJet seed M 0 time
  let L:=laplacianFiber nu M w
  let R:=NativeWindowHistoryAllOrderPrincipal.lower seed M time w
  let rate:=mean (NativeWindowHistoryOseen.rateHistory seed M time)
  have included : w=NativePhysicalPairing.includeCLM (NativeWholeH1Mixed.modes M)
      (NativeWholeH1Mixed.modes_closed M) v :=
    (NativeWindowHistoryMeanResidualLoad.include_zero seed M time).symm
  have wBound : ‖w‖^2≤J0^2 := by
    have paid:=NativeWindowHistoryMeanTime.jet_bound seed M 0 time
    rw [← NativeWindowHistoryMeanTime.source_mean seed M time] at paid
    exact pow_le_pow_left₀ (norm_nonneg w) paid 2
  have rateBound : ‖rate‖^2≤J1^2 :=
    pow_le_pow_left₀ (norm_nonneg rate)
      (NativeWindowHistoryMeanTime.source_rate_bound seed M time) 2
  have lowerBound : ‖R‖^2≤‖L‖^2+C*‖w‖^2 := by
    have paid:=lower M time inside v
    rw [← included] at paid
    change ‖R‖^2≤1*‖L‖^2+C*‖NativeFiniteActionResolvent.coefficients
      (NativeWholeH1Mixed.modes M) v‖^2 at paid
    rw [← NativePhysicalPairing.include_norm (NativeWholeH1Mixed.modes M)
      (NativeWholeH1Mixed.modes_zero M) (NativeWholeH1Mixed.modes_closed M),← included] at paid
    simpa only [one_mul] using paid
  have retained : NativeWindowHistoryAllOrderWord.retained seed M [] time=
      rate-R+nu.coeff • L := by
    rw [source_empty_retained_rate]
    have lowerRead : NativeWindowHistorySchurAction.effective seed M time w=
        R-nu.coeff • L := by
      change NativeWindowHistorySchurAction.effective seed M time w=
        (NativeWindowHistorySchurAction.effective seed M time w+nu.coeff • L)-nu.coeff • L
      abel
    rw [lowerRead]
    abel
  have retainedBound : ‖NativeWindowHistoryAllOrderWord.retained seed M [] time‖^2≤
      3*(‖rate‖^2+‖R‖^2+nu.coeff^2*‖L‖^2) := by
    rw [retained]
    have raw:=square_three rate R (nu.coeff • L)
    simpa only [norm_smul,Real.norm_of_nonneg nu.coeff_pos.le,mul_pow] using raw
  have weightBound : ‖NativeWindowHistoryAllOrderPrincipal.weight nu M w‖^2≤
      2*(‖w‖^2+nu.coeff^2*‖L‖^2) := by
    have raw:=square_two w (nu.coeff • L)
    simpa only [NativeWindowHistoryAllOrderPrincipal.weight,add_apply,
      ContinuousLinearMap.id_apply,smul_apply,norm_smul,
      Real.norm_of_nonneg nu.coeff_pos.le,mul_pow] using raw
  have pair:=inner_young (NativeWindowHistoryAllOrderPrincipal.weight nu M w)
    (NativeWindowHistoryAllOrderWord.retained seed M [] time)
  have cost : 2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M w)
      (NativeWindowHistoryAllOrderWord.retained seed M [] time)≤
      A*‖L‖^2+B := by
    dsimp only [A,B]
    have c0 : 0≤2+3*C := by linarith [C0]
    have massPaid:=mul_le_mul_of_nonneg_left wBound c0
    have ratePaid:=mul_le_mul_of_nonneg_left rateBound (by norm_num : (0:ℝ)≤3)
    nlinarith only [pair,weightBound,retainedBound,lowerBound,massPaid,ratePaid]
  exact cost

private theorem quadratic_to_quartic (A x delta : ℝ) (positive : 0<delta) :
    A*x^2≤delta*x^4+A^2/(4*delta) := by
  have identity : delta*x^4+A^2/(4*delta)-A*x^2=
      (2*delta*x^2-A)^2/(4*delta) := by
    field_simp [positive.ne']
    ring
  have square : 0≤(2*delta*x^2-A)^2/(4*delta) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith only [identity,square]

theorem source_empty_work_quartic (seed : GeneratedWholeRestartCurrent nu)
    (horizon delta : ℝ) (positive : 0<delta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →
      let w:=mean (finiteHistory seed time M)
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M w)
        (NativeWindowHistoryAllOrderWord.retained seed M [] time)≤
          delta*‖laplacianFiber nu M w‖^4+C := by
  obtain ⟨A,B,A0,B0,paid⟩:=source_empty_work_quadratic seed horizon
  let C:=B+A^2/(4*delta)
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨C,C0,fun M time inside => ?_⟩
  have work:=paid M time inside
  have absorbed:=quadratic_to_quartic A
    ‖laplacianFiber nu M (mean (finiteHistory seed time M))‖ delta positive
  dsimp only at work ⊢
  dsimp only [C]
  nlinarith only [work,absorbed]

end
end SaturationMonoid.NavierStokes.NativeCenteredEmptyWorkPaid
