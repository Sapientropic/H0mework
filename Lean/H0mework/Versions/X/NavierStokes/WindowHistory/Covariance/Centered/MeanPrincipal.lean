import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.JointBathPaid
import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.MeanStrainSource
import H0mework.Versions.X.NavierStokes.WindowSchurMean.PhysicalJet

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredMeanPrincipal
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWholeResolvent (restrictCLM)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
open NativeWindowHistoryMeanProjection (mean)
noncomputable section
variable {nu : Viscosity}

theorem source_mean_value (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryMeanAction.meanValue seed M time=
      NativeWindowHistoryMeanGradient.meanValue M
        (NativeWindowTraceWholeHistory.finiteHistory seed time M) := by
  unfold NativeWindowHistoryMeanAction.meanValue NativeWindowHistoryMeanGradient.meanValue
  have same := NativeWindowHistoryMeanProjection.mean_comp
    (NativeWindowTraceWholeHistory.projection M)
    (NativeWindowTraceWholeHistory.history seed time)
  change mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)=
    NativeWindowTraceWholeHistory.projection M
      (mean (NativeWindowTraceWholeHistory.history seed time)) at same
  rw [same]
  simp [NativeWindowTraceWholeHistory.projection,restrict_include]

theorem source_word_included (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (j : Coordinate) :
    NativeWindowHistoryAllOrderWord.value seed M [j] time=
      includeCLM (modes M) (modes_closed M)
        (NativeWindowHistorySpatialTransport.finite M j
          (NativeWindowHistoryMeanAction.meanValue seed M time)) := by
  have read : mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)=
      includeCLM (modes M) (modes_closed M)
        (NativeWindowHistoryMeanAction.meanValue seed M time) := by
    rw [source_mean_value]
    exact (NativeWindowHistoryMeanPhysicalJet.include_mean seed M time).symm
  change NativeWindowHistorySpatialWords.fiber M [j]
    (mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))=_
  rw [read]
  exact NativeWindowHistoryOseen.lift_included M _ _

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_mean_commutator (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (time : ℝ) (j : Coordinate) :
    let w:=mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)
    let u:=NativeWindowHistorySpatialWords.fiber M [j] w
    NativeWindowHistorySpatialWords.fiber M [j]
        (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
      NativeWindowHistorySchurAction.effective seed M time u=
        NativeWindowHistoryMeanStrainControl.fiber seed M time u-
          NativeWindowHistorySchurAction.feedback seed M time u := by
  intro w u
  let m:=NativeWindowHistoryMeanAction.meanValue seed M time
  let D:=NativeWindowHistorySpatialTransport.finite M j
  have wm : w=includeCLM (modes M) (modes_closed M) m := by
    change mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)=
      includeCLM (modes M) (modes_closed M)
        (NativeWindowHistoryMeanAction.meanValue seed M time)
    rw [source_mean_value]
    exact NativeWindowHistoryMeanPhysicalJet.include_mean seed M time |>.symm
  have du : u=includeCLM (modes M) (modes_closed M) (D m) := by
    dsimp only [u]
    rw [wm]
    exact NativeWindowHistoryOseen.lift_included M _ _
  have first : NativeWindowHistorySpatialWords.fiber M [j]
      (NativeWindowHistoryMeanAction.meanOperator seed M time w)=
      includeCLM (modes M) (modes_closed M)
        (D (NativeWindowHistoryMeanAction.frozen nu M m m)) := by
    have operatorRead : NativeWindowHistoryMeanAction.meanOperator seed M time w=
        includeCLM (modes M) (modes_closed M)
          (NativeWindowHistoryMeanAction.frozen nu M m m) := by
      rw [wm]
      exact NativeWindowHistoryOseen.lift_included M _ _
    rw [operatorRead]
    exact NativeWindowHistoryOseen.lift_included M _ _
  have second : NativeWindowHistoryMeanAction.meanOperator seed M time u=
      includeCLM (modes M) (modes_closed M)
        (NativeWindowHistoryMeanAction.frozen nu M m (D m)) := by
    rw [du]
    exact NativeWindowHistoryOseen.lift_included M _ _
  have third : NativeWindowHistoryMeanStrainControl.fiber seed M time u=
      includeCLM (modes M) (modes_closed M)
        (NativeWindowHistoryDynamicKernel.transport nu M (D m) m) := by
    rw [du]
    rw [NativeWindowHistoryMeanStrainControl.fiber_original,restrict_include]
  have product:=NativeWindowHistorySpatialTransport.frozen_derivative nu M j m m
  rw [NativeWindowHistorySchurAction.effective,add_apply,first,second,third]
  rw [product,map_add]
  abel

private theorem difference_square {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a-b‖^2≤2*‖a‖^2+2*‖b‖^2 := by
  have bound:=pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
  nlinarith only [bound,sq_nonneg (‖a‖-‖b‖)]

private theorem scalar_young (a b delta : ℝ) (positive : 0<delta) :
    a*b≤delta*b^2+a^2/(4*delta) := by
  have identity : delta*b^2+a^2/(4*delta)-a*b=(2*delta*b-a)^2/(4*delta) := by
    field_simp [positive.ne']
    ring
  have square : 0≤(2*delta*b-a)^2/(4*delta) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith only [identity,square]

private def weightedBudget (nu A epsilon : ℝ) : ℝ :=
  let alpha:=1+2*nu^2/epsilon
  let delta:=epsilon/(2*alpha)
  1+alpha*(A+(A*nu)^2/(4*delta))

private theorem weightedBudget_nonnegative (nu A epsilon : ℝ)
    (A0 : 0≤A) (positive : 0<epsilon) :
    0≤weightedBudget nu A epsilon := by
  unfold weightedBudget
  positivity

private theorem weighted_pair_absorb {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u r : E) (L : E →L[ℝ] E)
    (nu A epsilon : ℝ) (nu0 : 0<nu) (A0 : 0≤A) (positive : 0<epsilon)
    (bound : ‖r‖^2≤A*(‖u‖^2+nu*inner ℝ u (L u))) :
    2*inner ℝ (u+nu • L u) r≤
      epsilon*‖L u‖^2+weightedBudget nu A epsilon*‖u‖^2 := by
  let alpha:=1+2*nu^2/epsilon
  have alpha0 : 0<alpha := by dsimp only [alpha]; positivity
  let delta:=epsilon/(2*alpha)
  have delta0 : 0<delta := by dsimp only [delta]; positivity
  let C:=weightedBudget nu A epsilon
  have pair:=real_inner_le_norm u (L u)
  have scaled:=mul_le_mul_of_nonneg_left pair (mul_nonneg A0 nu0.le)
  have young:=scalar_young (A*nu*‖u‖) ‖L u‖ delta delta0
  have normalized : (A*nu*‖u‖)^2/(4*delta)=((A*nu)^2/(4*delta))*‖u‖^2 := by ring
  rw [normalized] at young
  have rbound : ‖r‖^2≤delta*‖L u‖^2+
      (A+(A*nu)^2/(4*delta))*‖u‖^2 := by
    nlinarith only [bound,scaled,young]
  have a := real_inner_le_norm u r
  have b := real_inner_le_norm (L u) r
  have first : 2*inner ℝ u r≤‖u‖^2+‖r‖^2 := by
    nlinarith only [a,sq_nonneg (‖u‖-‖r‖)]
  have second : 2*nu*inner ℝ (L u) r≤
      (epsilon/2)*‖L u‖^2+(2*nu^2/epsilon)*‖r‖^2 := by
    have scaled:=mul_le_mul_of_nonneg_left b nu0.le
    have square:=sq_nonneg (epsilon*‖L u‖-2*nu*‖r‖)
    have form : (epsilon/2)*‖L u‖^2+(2*nu^2/epsilon)*‖r‖^2=
        ((epsilon^2/2)*‖L u‖^2+2*nu^2*‖r‖^2)/epsilon := by
      field_simp [positive.ne']
    rw [form]
    apply (le_div_iff₀ positive).mpr
    have scaledE:=mul_le_mul_of_nonneg_left scaled positive.le
    nlinarith only [scaledE,square]
  have weighted : 2*inner ℝ (u+nu • L u) r≤
      ‖u‖^2+alpha*‖r‖^2+(epsilon/2)*‖L u‖^2 := by
    rw [inner_add_left,real_inner_smul_left]
    dsimp only [alpha]
    linarith only [first,second]
  have scaled:=mul_le_mul_of_nonneg_left rbound alpha0.le
  have coefficient : alpha*delta=epsilon/2 := by
    dsimp only [delta]
    field_simp [alpha0.ne']
  have final : ‖u‖^2+alpha*(delta*‖L u‖^2+
      (A+(A*nu)^2/(4*delta))*‖u‖^2)+(epsilon/2)*‖L u‖^2=
      epsilon*‖L u‖^2+C*‖u‖^2 := by
    dsimp only [C,weightedBudget]
    calc
      _=(alpha*delta+epsilon/2)*‖L u‖^2+
          (1+alpha*(A+(A*nu)^2/(4*delta)))*‖u‖^2 := by ring
      _=_ := by rw [coefficient]; ring
  calc
    _≤‖u‖^2+alpha*‖r‖^2+(epsilon/2)*‖L u‖^2 := weighted
    _≤‖u‖^2+alpha*(delta*‖L u‖^2+
        (A+(A*nu)^2/(4*delta))*‖u‖^2)+(epsilon/2)*‖L u‖^2 :=
      by linarith only [scaled]
    _=_ := final

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_mean_principal_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →∀j : Coordinate,
      let w:=mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (NativeWindowHistorySpatialWords.fiber M [j]
          (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
            NativeWindowHistorySchurAction.effective seed M time u)≤
          epsilon*‖NativeWindowHistoryAnnihilationControl.laplacianFiber nu M u‖^2+
            C*‖u‖^2 := by
  let K:=NativeWindowHistoryMeanStrainControl.normBudget seed horizon
  have K0 : 0≤K:=NativeWindowHistoryMeanStrainControl.normBudget_nonnegative seed horizon
  obtain ⟨B,B0,feedback⟩:=NativeWindowHistoryAdjointSpatialFeedback.source_feedback_bound seed horizon
  let A:=2*(K+B)
  have A0 : 0≤A:=by dsimp only [A]; positivity
  let C:=weightedBudget nu.coeff A epsilon
  have C0 : 0≤C:=weightedBudget_nonnegative nu.coeff A epsilon A0 positive
  refine ⟨C,C0,fun M time inside j => ?_⟩
  let m:=NativeWindowHistoryMeanAction.meanValue seed M time
  let v:=NativeWindowHistorySpatialTransport.finite M j m
  let w:=mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)
  let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
  let L:=NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
  let R:=NativeWindowHistoryMeanStrainControl.fiber seed M time u-
    NativeWindowHistorySchurAction.feedback seed M time u
  have included : u=includeCLM (modes M) (modes_closed M) v := source_word_included seed M time j
  have energyRead : NativeWindowHistoryHeatDual.energy nu M v=
      ‖u‖^2+nu.coeff*inner ℝ u (L u) := by
    dsimp only [NativeWindowHistoryHeatDual.energy]
    rw [included,include_norm (modes M) (modes_zero M),
      NativeWindowMetricGraphHistory.fiber_gradient,restrict_include]
  have strain:=NativeWindowHistoryMeanStrainControl.fiber_norm seed horizon M time inside u
  have reaction:=feedback M time inside v
  rw [← included,energyRead] at reaction
  have strainRead : ‖NativeWindowHistoryMeanStrainControl.fiber seed M time u‖^2≤
      K*(‖u‖^2+nu.coeff*inner ℝ u (L u)) := by
    rw [← NativeWindowMetricGraphHistory.fiber_gradient] at strain
    exact strain
  have difference:=difference_square
    (NativeWindowHistoryMeanStrainControl.fiber seed M time u)
    (NativeWindowHistorySchurAction.feedback seed M time u)
  have Rbound : ‖R‖^2≤A*(‖u‖^2+nu.coeff*inner ℝ u (L u)) := by
    dsimp only [R,A]
    nlinarith only [difference,strainRead,reaction]
  have paid:=weighted_pair_absorb u R L nu.coeff A epsilon
    nu.coeff_pos A0 positive Rbound
  have read:=source_mean_commutator seed M time j
  dsimp only at read
  change NativeWindowHistorySpatialWords.fiber M [j]
      (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
    NativeWindowHistorySchurAction.effective seed M time u=R at read
  change 2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
      (NativeWindowHistorySpatialWords.fiber M [j]
        (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
          NativeWindowHistorySchurAction.effective seed M time u)≤
      epsilon*‖L u‖^2+C*‖u‖^2
  rw [read]
  exact paid

theorem source_first_word_u_mass (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon)
    (j : Coordinate) :
    ‖NativeWindowHistoryAllOrderWord.value seed M [j] time‖^2≤
      max 0 (NativeWindowAugmentedPayment.graphBudget seed 0 horizon) := by
  let m:=NativeWindowHistoryMeanGradient.meanValue M
    (NativeWindowTraceWholeHistory.finiteHistory seed time M)
  have uread:=source_word_included seed M time j
  rw [source_mean_value] at uread
  rw [uread,include_norm (modes M) (modes_zero M)]
  have one:=Finset.single_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun k _ => sq_nonneg ‖NativeFiniteActionResolvent.coefficients (modes M)
      (NativeWindowHistorySpatialTransport.finite M k m)‖)
    (Finset.mem_univ j)
  have total:=NativeWindowHistoryCreationGeometry.derivative_mass
    (modes M) (modes_zero M) (modes_closed M) m
  have source:=NativeWindowHistoryMeanGradient.source_mean_budget seed horizon M time inside
  have identity : (∑k : Coordinate,
      ‖NativeFiniteActionResolvent.coefficients (modes M)
        (NativeWindowHistorySpatialTransport.finite M k m)‖^2)=
      NativeCommonAdvectorAction.curlPair (modes M) m.1 m.1 := by
    convert total using 1
    apply Finset.sum_congr rfl
    intro k _
    exact (real_inner_self_eq_norm_sq _).symm
  exact one.trans (identity.le.trans (source.trans (le_max_right _ _)))

theorem source_mean_principal_uniform (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →∀j : Coordinate,
      let w:=mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (NativeWindowHistorySpatialWords.fiber M [j]
          (NativeWindowHistoryMeanAction.meanOperator seed M time w)-
            NativeWindowHistorySchurAction.effective seed M time u)≤
          epsilon*‖NativeWindowHistoryAnnihilationControl.laplacianFiber nu M u‖^2+C := by
  obtain ⟨K,K0,paid⟩:=source_mean_principal_paid seed horizon epsilon positive
  let G:=max 0 (NativeWindowAugmentedPayment.graphBudget seed 0 horizon)
  have G0 : 0≤G:=le_max_left _ _
  refine ⟨K*G,mul_nonneg K0 G0,fun M time inside j => ?_⟩
  have first:=paid M time inside j
  have mass:=source_first_word_u_mass seed horizon M time inside j
  have scaled:=mul_le_mul_of_nonneg_left mass K0
  dsimp only at first ⊢
  linarith only [first,scaled]

theorem source_weighted_mean_strain_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →∀j : Coordinate,
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      2*inner ℝ (NativeWindowHistoryAllOrderPrincipal.weight nu M u)
        (NativeWindowHistoryMeanStrainControl.fiber seed M time u)≤
        epsilon*‖NativeWindowHistoryAnnihilationControl.laplacianFiber nu M u‖^2+C := by
  let K:=NativeWindowHistoryMeanStrainControl.normBudget seed horizon
  have K0:0≤K:=NativeWindowHistoryMeanStrainControl.normBudget_nonnegative seed horizon
  let G:=max 0 (NativeWindowAugmentedPayment.graphBudget seed 0 horizon)
  have G0:0≤G:=le_max_left _ _
  let B:=weightedBudget nu.coeff K epsilon
  have B0:0≤B:=weightedBudget_nonnegative nu.coeff K epsilon K0 positive
  let C:=B*G
  refine ⟨C,mul_nonneg B0 G0,fun M time inside j => ?_⟩
  let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
  let L:=NativeWindowHistoryAnnihilationControl.laplacianFiber nu M
  let s:=NativeWindowHistoryMeanStrainControl.fiber seed M time u
  have mass:=source_first_word_u_mass seed horizon M time inside j
  have graph:=NativeWindowMetricGraphHistory.fiber_gradient nu M u
  have strain:=NativeWindowHistoryMeanStrainControl.fiber_norm seed horizon M time inside u
  rw [← graph] at strain
  have bounded : ‖s‖^2≤K*(‖u‖^2+nu.coeff*inner ℝ u (L u)) := strain
  have work:=weighted_pair_absorb u s L nu.coeff K epsilon
    nu.coeff_pos K0 positive bounded
  have scaled:=mul_le_mul_of_nonneg_left mass B0
  change 2*inner ℝ (u+nu.coeff • L u) s≤epsilon*‖L u‖^2+C
  dsimp only [C,B] at *
  linarith only [work,scaled]

end
end SaturationMonoid.NavierStokes.NativeCenteredMeanPrincipal
