import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.RelativeCreation

set_option autoImplicit false
open scoped Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCreatedLoadControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowTraceWholeHistory (H finiteHistory gradient)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeFiniteActionResolvent (physicalSpace pairing)
open NativeWindowHistoryMeanProjection (mean embed)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistorySpatialWords (history)
open NativeWindowHistoryAllOrderWord (value)
open NativeWindowHistoryAllOrderCausal (created load)
open NativeWindowHistoryAllOrderCreatedLoadTranspose (transpose cross)
open NativeWindowHistoryAllOrderJointEnergy (energy)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

private theorem rescale (n w p g : ℝ) (positive : 0<n)
    (paid : 2*n⁻¹*w≤(n⁻¹)^2*p+g) : 2*w≤n⁻¹*p+n*g := by
  have multiplied:=mul_le_mul_of_nonneg_left paid positive.le
  have first : n*(2*n⁻¹*w)=2*w := by field_simp
  have last : n*((n⁻¹)^2*p+g)=n⁻¹*p+n*g := by field_simp
  rwa [first,last] at multiplied

private theorem absolute_young (w P g delta : ℝ) (positive : 0<delta)
    (bound : ∀ a : ℝ,2*a*w≤a^2*P+g) : |2*w|≤delta*g+delta⁻¹*P := by
  have upper:=rescale delta w P g positive (bound delta⁻¹)
  have negative : 2*delta⁻¹*(-w)≤(delta⁻¹)^2*P+g := by
    simpa only [neg_sq,mul_neg,neg_mul] using bound (-delta⁻¹)
  have lower:=rescale delta (-w) P g positive negative
  exact abs_le.mpr ⟨by linarith only [lower],by linarith only [upper]⟩

theorem potential_pair_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ)
    (v : physicalSpace (modes M)) (r : H) (delta : ℝ) (positive : 0<delta) :
    |2*inner ℝ (creation seed M t (includeCLM (modes M) (modes_closed M) v)) r|≤
      delta*gradient M r+delta⁻¹*NativeWindowHistorySchurWeakPairing.potential seed M t v :=
  absolute_young _ _ _ delta positive (NativeWindowHistorySchurWeakPairing.creation_young seed M t v r)

theorem transpose_source (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ A K : ℝ,0 ≤ A ∧ 0 ≤ K ∧ ∀ M (word : List Coordinate) (a B : ℝ) (aB : a ≤ B)
      (t : ℝ),t∈Icc 0 horizon →
      |transpose seed M word a B aB t|≤epsilon*gradient M (history seed M word t)+
        A*gradient M (created seed M word a B aB t)+K*energy seed M word a B aB t := by
  let B:=1+4/epsilon
  have B0 : 0<B:=by positivity
  let delta:=epsilon/(2*B)
  have delta0 : 0<delta:=by positivity
  obtain ⟨K,K0,potentialPaid⟩:=NativeWindowHistoryAllOrderRelativeCreation.source_potential seed horizon delta delta0
  refine ⟨16*nu.coeff^2/epsilon+1,B*K,by positivity,mul_nonneg B0.le K0,fun M word a terminal ordered t inside => ?_⟩
  let x:=history seed M word t
  let y:=created seed M word a terminal ordered t
  let v:=NativeWindowHistoryAllOrderRelativeCreation.physicalValue seed M word t
  have read : value seed M word t=includeCLM (modes M) (modes_closed M) v:=
    (NativeWindowHistoryAllOrderRelativeCreation.include_value seed M word t).symm
  let P:=NativeWindowHistorySchurWeakPairing.potential seed M t v
  have first:=NativeWindowHistoryAllOrderCreatedLoadTranspose.cross_bound seed M t x y (epsilon/4) (by positivity)
  have middle:=potential_pair_bound seed M t v y 1 (by norm_num)
  have last:=potential_pair_bound seed M t v x (epsilon/4) (by positivity)
  rw [← read] at middle last
  have triangle:=(abs_add_le (2*cross seed M t x y+2*inner ℝ (creation seed M t (value seed M word t)) y)
    (2*inner ℝ (creation seed M t (value seed M word t)) x)).trans
    (add_le_add (abs_add_le _ _) (le_refl _))
  have scale : |2*cross seed M t x y|=2*|cross seed M t x y|:=by rw [abs_mul]; norm_num
  rw [scale] at triangle
  have inverse : (epsilon/4)⁻¹=4/epsilon:=by field_simp
  have coefficient : 4*nu.coeff^2/(epsilon/4)=16*nu.coeff^2/epsilon:=by ring
  rw [coefficient] at first
  rw [inverse] at last
  norm_num only [one_mul,inv_one] at middle
  have preliminary : |transpose seed M word a terminal ordered t|≤(epsilon/2)*gradient M x+
      (16*nu.coeff^2/epsilon+1)*gradient M y+B*P :=
    triangle.trans ((add_le_add (add_le_add first middle) last).trans_eq (by dsimp only [B,P]; ring))
  have scaled:=mul_le_mul_of_nonneg_left (potentialPaid M word a terminal ordered t inside) B0.le
  have cancel : B*delta=epsilon/2:=by dsimp only [delta]; field_simp
  have payment : B*P≤(epsilon/2)*gradient M x+(B*K)*energy seed M word a terminal ordered t := by
    simpa only [mul_add,← mul_assoc,cancel,P,v,x] using scaled
  exact preliminary.trans ((add_le_add (le_refl _) payment).trans_eq (by ring))

private theorem young_product (x y d : ℝ) (positive : 0<d) : 2*x*y≤d*x^2+d⁻¹*y^2 := by
  have read : d*(d*x^2+d⁻¹*y^2)=d^2*x^2+y^2 := by field_simp
  suffices bound : d*(2*x*y)≤d*(d*x^2+d⁻¹*y^2) from le_of_mul_le_mul_left bound positive
  rw [read]
  nlinarith only [sq_nonneg (d*x-y)]

theorem endpoint_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (word : List Coordinate)
    (a B : ℝ) (aB : a ≤ B) (t theta : ℝ) (positive : 0<theta) :
    |NativeWindowHistoryAllOrderCreatedLoadTranspose.pairing seed M word a B aB t|≤
      theta*energy seed M word a B aB t+(2/theta)*‖created seed M word a B aB t‖^2 := by
  let x:=history seed M word t
  let y:=created seed M word a B aB t
  have pairing:=abs_real_inner_le_norm y x
  have young:=young_product ‖x‖ ‖y‖ (theta/2) (by positivity)
  have whole:=mul_le_mul_of_nonneg_left
    (NativeWindowHistoryAllOrderJointEnergy.whole_mass seed M word a B aB t)
    (show 0≤theta/2 by positivity)
  have inverse : (theta/2)⁻¹=2/theta:=by field_simp
  rw [inverse] at young
  have scale : |NativeWindowHistoryAllOrderCreatedLoadTranspose.pairing seed M word a B aB t|=
      2*|inner ℝ y x| := by
    rw [NativeWindowHistoryAllOrderCreatedLoadTranspose.pairing,abs_mul]
    norm_num
    rfl
  rw [scale]
  nlinarith only [pairing,young,whole]

set_option backward.isDefEq.respectTransparency false in
theorem source (seed : GeneratedWholeRestartCurrent nu) (horizon theta epsilon : ℝ)
    (thetaPositive : 0<theta) (epsilonPositive : 0<epsilon) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M (word : List Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      |∫t in a..b,2*inner ℝ (created seed M word a horizon start.2 t) (load seed M word t)|≤
        theta*energy seed M word a horizon start.2 b+
          epsilon*(∫t in a..b,gradient M (history seed M word t))+
            C*(∫t in a..b,energy seed M word a horizon start.2 t) := by
  obtain ⟨A,K,A0,K0,transposed⟩:=transpose_source seed horizon (epsilon/2) (by positivity)
  let L:=2/theta+A/nu.coeff
  have L0 : 0<L:=add_pos_of_pos_of_nonneg (div_pos (by norm_num) thetaPositive) (div_nonneg A0 nu.coeff_pos.le)
  let delta:=epsilon/(2*L)
  have delta0 : 0<delta:=by positivity
  obtain ⟨C,C0,response⟩:=NativeWindowHistoryAllOrderRelativeCreation.source_energy seed horizon delta delta0
  refine ⟨K+L*C,add_nonneg K0 (mul_nonneg L0.le C0),fun M word a start b inside => ?_⟩
  let x:=history seed M word
  let y:=created seed M word a horizon start.2
  let E:=energy seed M word a horizon start.2
  have subset : Icc a b ⊆ Icc a horizon:=Icc_subset_Icc le_rfl inside.2
  have xc:Continuous x:=NativeWindowHistoryAllOrderCreatedLoadBudget.history_continuous seed M word
  have yc:ContinuousOn y (Icc a b):=(NativeWindowHistoryAllOrderJointLoad.created_continuous seed M word a horizon start.2).mono subset
  have ec:ContinuousOn E (Icc a b):=(NativeWindowHistoryAllOrderJointLoad.energy_continuous seed M word a horizon start.2).mono subset
  have gx : IntervalIntegrable (fun t => gradient M (x t)) volume a b:=
    ((NativeWindowHistoryCausalDissipation.gradient_continuous nu M).comp xc).intervalIntegrable a b
  have gy : IntervalIntegrable (fun t => gradient M (y t)) volume a b:=
    ((NativeWindowHistoryCausalDissipation.gradient_continuous nu M).comp_continuousOn yc).intervalIntegrable_of_Icc (μ := volume) inside.1
  have ei:IntervalIntegrable E volume a b:=ec.intervalIntegrable_of_Icc (μ := volume) inside.1
  have point (t : ℝ) (ht : t∈Ioc a b) : ‖transpose seed M word a horizon start.2 t‖≤
      (epsilon/2)*gradient M (x t)+A*gradient M (y t)+K*E t :=
    (Real.norm_eq_abs _).trans_le (transposed M word a horizon start.2 t ⟨start.1.trans ht.1.le,ht.2.trans inside.2⟩)
  have boundT:=intervalIntegral.norm_integral_le_of_norm_le inside.1 (Eventually.of_forall point)
    (((gx.const_mul (epsilon/2)).add (gy.const_mul A)).add (ei.const_mul K))
  rw [Real.norm_eq_abs,intervalIntegral.integral_add ((gx.const_mul (epsilon/2)).add (gy.const_mul A)) (ei.const_mul K),
    intervalIntegral.integral_add (gx.const_mul (epsilon/2)) (gy.const_mul A),intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at boundT
  have g0 : 0≤∫t in a..b,gradient M (y t):=intervalIntegral.integral_nonneg_of_forall inside.1
    (fun t => NativeWindowHistoryMeanGradient.gradient_nonnegative seed M (y t))
  have Ly : 2/theta≤L:=le_add_of_nonneg_right (div_nonneg A0 nu.coeff_pos.le)
  have Lg : A≤L*nu.coeff := by
    have cancel:=div_mul_cancel₀ A nu.coeff_pos.ne'
    have other:=mul_nonneg (div_nonneg (by norm_num : (0:ℝ)≤2) thetaPositive.le) nu.coeff_pos.le
    dsimp only [L]
    nlinarith only [cancel,other]
  have combined : (2/theta)*‖y b‖^2+A*(∫t in a..b,gradient M (y t))≤
      L*(‖y b‖^2+nu.coeff*(∫t in a..b,gradient M (y t))) :=
    (add_le_add (mul_le_mul_of_nonneg_right Ly (sq_nonneg _)) (mul_le_mul_of_nonneg_right Lg g0)).trans_eq (by ring)
  have paid:=mul_le_mul_of_nonneg_left (response M word a start b inside) L0.le
  have cancel : L*delta=epsilon/2:=by dsimp only [delta]; field_simp
  have paidResponse : (2/theta)*‖y b‖^2+A*(∫t in a..b,gradient M (y t))≤
      (epsilon/2)*(∫t in a..b,gradient M (x t))+(L*C)*(∫t in a..b,E t) := by
    apply combined.trans
    simpa only [mul_add,← mul_assoc,cancel,x,y,E] using paid
  have endpoint:=endpoint_bound seed M word a horizon start.2 b theta thetaPositive
  rw [NativeWindowHistoryAllOrderCreatedLoadBudget.transpose_write seed M word a horizon start.2 b inside]
  have triangle : |NativeWindowHistoryAllOrderCreatedLoadTranspose.pairing seed M word a horizon start.2 b-
      ∫t in a..b,transpose seed M word a horizon start.2 t|≤
        |NativeWindowHistoryAllOrderCreatedLoadTranspose.pairing seed M word a horizon start.2 b|+
          |∫t in a..b,transpose seed M word a horizon start.2 t| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le
      (NativeWindowHistoryAllOrderCreatedLoadTranspose.pairing seed M word a horizon start.2 b)
      (∫t in a..b,transpose seed M word a horizon start.2 t)
  nlinarith only [triangle,endpoint,boundT,paidResponse]

set_option backward.isDefEq.respectTransparency false in
theorem source_joint (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ M (word : List Coordinate) (a : ℝ) (start : a∈Icc 0 horizon),∀ b∈Icc a horizon,
      (3/4:ℝ)*energy seed M word a horizon start.2 b+
        (nu.coeff/4)*(∫t in a..b,gradient M (history seed M word t))≤
          energy seed M word a horizon start.2 a+C*(∫t in a..b,energy seed M word a horizon start.2 t)+
            ∫t in a..b,2*inner ℝ (history seed M word t) (load seed M word t) := by
  obtain ⟨K,K0,whole⟩:=NativeWindowHistoryAllOrderJointLoad.source_integral seed horizon
  obtain ⟨C,C0,paid⟩:=source seed horizon (1/4) (nu.coeff/4) (by norm_num) (by positivity [nu.coeff_pos])
  refine ⟨K+C,add_nonneg K0 C0,fun M word a start b inside => ?_⟩
  have full:=whole M word a start b inside
  rw [NativeWindowHistoryAllOrderJointLoad.mixed_write seed M word a horizon start.2 b inside] at full
  have createdPaid:=paid M word a start b inside
  have lower:=neg_abs_le (∫t in a..b,2*inner ℝ (created seed M word a horizon start.2 t) (load seed M word t))
  linarith only [full,createdPaid,lower]

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryAllOrderCreatedLoadControl
