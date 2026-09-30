import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.BathSplit

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredBathPaid
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H gradient)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistoryMeanProjection (residual)
noncomputable section
variable {nu : Viscosity}

private theorem pair_young {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a b : E) (n : ℝ) (positive : 0≤n) :
    2*n*inner ℝ a b≤(n^2/2)*‖a‖^2+2*‖b‖^2 := by
  have pair:=real_inner_le_norm a b
  have scaled:=mul_le_mul_of_nonneg_left pair (mul_nonneg (by norm_num : (0:ℝ)≤2) positive)
  nlinarith only [scaled,sq_nonneg (n*‖a‖-2*‖b‖)]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_centered_bath_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃K : ℝ,0≤K ∧∀M≥low,∀time∈Icc 0 horizon,∀q : H,
      residual q=q →
      2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanBlocks.bath seed M time q)≤
        -nu.coeff^2*‖laplacianAction nu M q‖^2+K*gradient M q+
          2*nu.coeff*inner ℝ (laplacianAction nu M q)
            (NativeWindowHistorySchurAdvectorAction.wAction seed M time q) := by
  let delta:=nu.coeff^2/4
  have delta0 : 0<delta:=by dsimp only [delta]; positivity [nu.coeff_pos]
  obtain ⟨low,C,C0,source⟩:=
    NativeWindowHistorySchurAdvectorAction.source_graph_bound seed horizon nonnegative delta delta0
  refine ⟨low,2*C,mul_nonneg (by norm_num) C0,fun M above time inside q centered => ?_⟩
  let L:=laplacianAction nu M q
  let x:=NativeWindowHistorySchurAdvectorAction.xAction seed M time q
  let w:=NativeWindowHistorySchurAdvectorAction.wAction seed M time q
  let g:=gradient M q
  have g0 : 0≤g:=NativeWindowHistoryMeanGradient.gradient_nonnegative seed M q
  have young:=pair_young L x nu.coeff nu.coeff_pos.le
  have xPaid:=source M above time inside q
  have doubled:=mul_le_mul_of_nonneg_left xPaid (by norm_num : (0:ℝ)≤2)
  have paid : 2*nu.coeff*inner ℝ L x≤nu.coeff^2*‖L‖^2+2*C*g := by
    dsimp only [delta] at doubled
    nlinarith only [young,doubled]
  have split:=NativeCenteredBathSplit.source_weighted_bath_split seed M time q centered
  dsimp only [L,x,w,g] at paid ⊢
  rw [inner_add_right] at split
  nlinarith only [split,paid,mul_nonneg nu.coeff_pos.le g0]

theorem source_first_word_q_mass (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (M : ℕ) (time : ℝ) (inside : time∈Icc 0 horizon)
    (j : Coordinate) :
    ‖NativeCenteredWeightedResidualRate.centeredWord seed M j time‖^2≤
      NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon := by
  let h:=NativeWindowTraceWholeHistory.finiteHistory seed time M
  let r:=residual h
  have same : NativeCenteredWeightedResidualRate.centeredWord seed M j time=
      NativeWindowHistorySpatialWords.operator M [j] r :=
    NativeWindowHistoryMeanProjection.residual_comp (NativeWindowHistorySpatialWords.fiber M [j]) h
  have one:=Finset.single_le_sum (s := (Finset.univ : Finset Coordinate))
    (fun k _ => sq_nonneg ‖NativeWindowHistorySpatialWords.operator M [k] r‖)
    (Finset.mem_univ j)
  have total:=NativeWindowHistoryJacobianSpatial.mass_gradient nu M r
  have residualPaid:=NativeWindowHistoryMeanGradient.gradient_residual_le seed M h
  have source:=NativeWindowHistorySchurTemporalControl.source_gradient seed horizon M time inside
  rw [same]
  exact one.trans (total.trans_le (residualPaid.trans source))

private theorem scalar_young (a b delta : ℝ) (positive : 0<delta) :
    a*b≤delta*b^2+a^2/(4*delta) := by
  have identity : delta*b^2+a^2/(4*delta)-a*b=(2*delta*b-a)^2/(4*delta) := by
    field_simp [positive.ne']
    ring
  have square : 0≤(2*delta*b-a)^2/(4*delta) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith only [identity,square]

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
theorem source_original_q_bath_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon : ℝ) (nonnegative : 0≤horizon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀time∈Icc 0 horizon,∀j : Coordinate,
      let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
      2*inner ℝ (NativeWindowHistoryJacobianControl.heat nu M q)
          (NativeWindowHistoryMeanBlocks.bath seed M time q)≤
        -(nu.coeff^2/2)*‖laplacianAction nu M q‖^2+C+
          2*nu.coeff*inner ℝ (laplacianAction nu M q)
            (NativeWindowHistorySchurAdvectorAction.wAction seed M time q) := by
  obtain ⟨low,K,K0,paid⟩:=source_centered_bath_paid seed horizon nonnegative
  let G:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  have G0 : 0≤G:=le_max_left _ _
  let delta:=nu.coeff^2/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity [nu.coeff_pos]
  let C:=K^2/(4*delta)*G
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨low,C,C0,fun M above time inside j => ?_⟩
  let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
  let L:=laplacianAction nu M q
  let g:=gradient M q
  have centered : residual q=q:=NativeWindowHistoryBathResolvent.residual_square _
  have original:=paid M above time inside q centered
  have mass:=source_first_word_q_mass seed horizon M time inside j
  have pairing:=real_inner_le_norm q L
  have read : g=inner ℝ q L := (NativeWindowMetricGraphHistory.history_gradient nu M q).symm
  have scaled:=mul_le_mul_of_nonneg_left pairing K0
  have young:=scalar_young (K*‖q‖) ‖L‖ delta delta0
  have extra:=mul_le_mul_of_nonneg_left mass (div_nonneg (sq_nonneg K) (by positivity : (0:ℝ)≤4*delta))
  have normalized : (K*‖q‖)^2/(4*delta)=(K^2/(4*delta))*‖q‖^2 := by ring
  rw [normalized] at young
  change (K^2/(4*delta))*‖q‖^2≤C at extra
  have lower : K*g≤delta*‖L‖^2+C := by
    rw [read]
    nlinarith only [scaled,young,extra]
  dsimp only [q,L,g,delta] at original lower ⊢
  nlinarith only [original,lower]

end
end SaturationMonoid.NavierStokes.NativeCenteredBathPaid
