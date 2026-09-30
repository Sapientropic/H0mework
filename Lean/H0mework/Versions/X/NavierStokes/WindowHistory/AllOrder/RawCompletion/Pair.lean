import H0mework.Versions.X.NavierStokes.WindowHistory.AllOrder.RawCompletion.Source
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.AdvectorEnergy

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeResidualMetricPair
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWindowHistoryOseen (H action rateHistory forcingHistory)
open NativeWindowTraceWholeHistory (finiteHistory gradient metricAction)
open NativeWindowHistorySpatialWords (history operator)
open NativeWindowHistoryAllOrderCausal (load)
open NativeWindowHistoryAnnihilationControl (laplacianAction)
open NativeWindowHistorySchurAdvectorAction (xAction wAction)
open NativeWindowHistorySchurTranspose (transposeAction)
open NativeWindowHistoryJacobianSpatial (spatial)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

theorem gradient_sum (nu : Viscosity) (M : ℕ) (v : H) :
    (∑j : Coordinate,gradient M (spatial M j v))=‖laplacianAction nu M v‖^2 := by
  have energy:=NativeWindowHistoryJacobianSpatial.energy_gradient nu M v
  simp only [NativeWindowHistorySchurTemporalControl.energy,Finset.sum_add_distrib,← Finset.mul_sum] at energy
  rw [NativeWindowHistoryJacobianSpatial.mass_gradient nu M v] at energy
  have positive:=nu.coeff_pos
  nlinarith only [energy,positive]

theorem gradient_pair (nu : Viscosity) (M : ℕ) (u v : H) :
    (∑j : Coordinate,inner ℝ (spatial M j u) (spatial M j v))=inner ℝ (laplacianAction nu M u) v := by
  have each (j : Coordinate) : inner ℝ (spatial M j u) (spatial M j v)=
      -inner ℝ (spatial M j (spatial M j u)) v := by
    have skew:=NativeWindowHistoryJacobianSpatial.spatial_skew M j (spatial M j u) v
    linarith only [skew]
  have paired:=congrArg (fun z : H => inner ℝ z v) (NativeWindowHistoryJacobianSpatial.spatial_square nu M u)
  have read:=sum_inner (𝕜:=ℝ) (E:=H) Finset.univ (fun j : Coordinate => spatial M j (spatial M j u)) v
  have same : -(∑j : Coordinate,inner ℝ (spatial M j (spatial M j u)) v)=inner ℝ (laplacianAction nu M u) v := by
    have actual:=read.symm.trans paired
    rw [inner_neg_left (𝕜:=ℝ) (E:=H)] at actual
    linarith only [actual]
  simpa only [each,Finset.sum_neg_distrib] using same

private theorem load_trace_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (D : Coordinate → E →L[ℝ] E) (A L : E →L[ℝ] E) (g : E → ℝ) (n : ℝ) (h f : E)
    (paired : ∀v,(∑j,inner ℝ (D j h) (D j v))=inner ℝ (L h) v)
    (squared : (∑j,g (D j h))=‖L h‖^2)
    (damping : ∀v,inner ℝ v (A v)= -n*g v) :
    (∑j,inner ℝ (D j h) (D j (A h)-A (D j h)+D j f))=
      inner ℝ (L h) (A h+f)+n*‖L h‖^2 := by
  have each (j : Coordinate) :
      inner ℝ (D j h) (D j (A h)-A (D j h)+D j f)=
        inner ℝ (D j h) (D j (A h+f))+n*g (D j h) := by
    rw [map_add,inner_add_right,inner_sub_right,inner_add_right,damping]
    ring
  simp_rw [each]
  rw [Finset.sum_add_distrib,paired,← Finset.mul_sum,squared]

private theorem heat_cancel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (l x w f : E) (n : ℝ) :
    inner ℝ l ((-n) • l+x+w+f)+n*‖l‖^2=inner ℝ l (x+w+f) := by
  simp only [inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  ring

set_option backward.isDefEq.respectTransparency false in
theorem load_trace (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) :
    (∑j : Coordinate,inner ℝ (history seed M [j] t) (load seed M [j] t))=
      inner ℝ (laplacianAction nu M (finiteHistory seed t M))
        (xAction seed M t (finiteHistory seed t M)+wAction seed M t (finiteHistory seed t M)+forcingHistory seed M t) := by
  let h:=finiteHistory seed t M
  have first:=load_trace_algebra (E:=H) (spatial M) (action seed M t) (laplacianAction nu M)
    (gradient M) nu.coeff h (forcingHistory seed M t) (gradient_pair nu M h) (gradient_sum nu M h)
      (NativeWindowHistoryOseenGap.action_energy seed M t)
  have actual : (∑j : Coordinate,inner ℝ (history seed M [j] t) (load seed M [j] t))=
      inner ℝ (laplacianAction nu M h) (action seed M t h+forcingHistory seed M t)+
        nu.coeff*‖laplacianAction nu M h‖^2 := first
  have source:=congrArg (fun v : H => inner ℝ (laplacianAction nu M h) (v+forcingHistory seed M t)+
    nu.coeff*‖laplacianAction nu M h‖^2) (NativeWindowHistorySchurAdvectorEnergy.source_action_read seed M t h)
  exact actual.trans (source.trans (heat_cancel (E:=H) _ _ _ _ _))

def work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : ℝ :=
  ∑j : Coordinate,2*inner ℝ (history seed M [j] t) (NativeRawCompletionTransfer.remainder seed M j t)

def heatWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : ℝ :=
  2*inner ℝ (laplacianAction nu M (finiteHistory seed t M))
    (wAction seed M t (finiteHistory seed t M)+forcingHistory seed M t)

def exchange (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : ℝ :=
  2*inner ℝ (laplacianAction nu M (finiteHistory seed t M)) (xAction seed M t (finiteHistory seed t M))-
    ∑j : Coordinate,2*inner ℝ (history seed M [j] t) (transposeAction seed M t (history seed M [j] t))

set_option backward.isDefEq.respectTransparency false in
theorem paired_identity (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) :
    work seed M t=heatWork seed M t+exchange seed M t := by
  unfold work NativeRawCompletionTransfer.remainder heatWork exchange
  simp only [inner_sub_right (𝕜:=ℝ) (E:=H),mul_sub,Finset.sum_sub_distrib,← Finset.mul_sum]
  have source:=load_trace seed M t
  simp only [inner_add_right (𝕜:=ℝ) (E:=H)] at source ⊢
  linarith only [source]

private theorem norm_young {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (n : ℝ) (positive : 0<n) :
    |2*inner ℝ u v|≤n*‖u‖^2+n⁻¹*‖v‖^2 := by
  have pair:=abs_real_inner_le_norm u v
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (mul_le_mul_of_nonneg_left pair (by norm_num : (0:ℝ)≤2)).trans
  apply le_of_mul_le_mul_left (a:=n) _ positive
  have read : n*(n*‖u‖^2+n⁻¹*‖v‖^2)=n^2*‖u‖^2+‖v‖^2 := by field_simp
  rw [read]
  nlinarith only [sq_nonneg (n*‖u‖-‖v‖)]

private theorem graph_work {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (B g epsilon : ℝ) (positive : 0<epsilon)
    (bound : ‖v‖^2≤(epsilon/2)^2*‖u‖^2+B*g) :
    |2*inner ℝ u v|≤epsilon*‖u‖^2+(epsilon/2)⁻¹*B*g := by
  let n:=epsilon/2
  have n0 : 0<n:=div_pos positive (by norm_num)
  have young:=norm_young u v n n0
  have paid:=mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr n0.le)
  change n⁻¹*‖v‖^2≤n⁻¹*(n^2*‖u‖^2+B*g) at paid
  have coefficient : n⁻¹*n^2=n := by field_simp
  rw [mul_add,← mul_assoc,coefficient] at paid
  dsimp only [n] at young paid ⊢
  nlinarith only [young,paid]

set_option backward.isDefEq.respectTransparency false in
theorem source_x_heat (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀t∈Icc 0 horizon,∀h : H,
      |2*inner ℝ (laplacianAction nu M h) (xAction seed M t h)|≤
        epsilon*‖laplacianAction nu M h‖^2+C*gradient M h := by
  obtain ⟨low,B,B0,source⟩:=NativeWindowHistorySchurAdvectorAction.source_graph_bound
    seed horizon nonnegative ((epsilon/2)^2) (sq_pos_of_pos (by positivity))
  refine ⟨low,(epsilon/2)⁻¹*B,by positivity,fun M above t inside h => ?_⟩
  exact graph_work (E:=H) _ _ B (gradient M h) epsilon positive (source M above t inside h)

private theorem sum_work (f d m : Coordinate → ℝ) (e K D G : ℝ)
    (source : ∀j,|f j|≤e*d j+K*m j) (dsum : ∑j,d j=D) (msum : ∑j,m j=G) :
    |∑j,f j|≤e*D+K*G := by
  have paid:=(Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=f)).trans
    (Finset.sum_le_sum fun j _ => source j)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,dsum,msum] using paid

private theorem difference_work (x y e D B K g G : ℝ) (B0 : 0≤B) (K0 : 0≤K)
    (first : |x|≤e/2*D+B*g) (last : |y|≤e/2*D+K*g) (gradient : g≤G) :
    |x-y|≤e*D+(B+K)*G := by
  have source:=(abs_sub x y).trans (add_le_add first last)
  have paid:=mul_le_mul_of_nonneg_left gradient (add_nonneg B0 K0)
  nlinarith only [source,paid]

set_option backward.isDefEq.respectTransparency false in
theorem source_exchange (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃low : ℕ,∃C : ℝ,0≤C ∧∀M≥low,∀t∈Icc 0 horizon,
      |exchange seed M t|≤epsilon*‖laplacianAction nu M (finiteHistory seed t M)‖^2+C := by
  obtain ⟨one,B,B0,xPaid⟩:=source_x_heat seed horizon nonnegative (epsilon/2) (by positivity)
  obtain ⟨two,K,K0,pPaid⟩:=NativeRawCompletionTransfer.source_form seed horizon nonnegative (epsilon/2) (by positivity)
  let G:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  have G0 : 0≤G:=le_max_left _ _
  refine ⟨max one two,(B+K)*G,by positivity,fun M above t inside => ?_⟩
  let h:=finiteHistory seed t M
  have x:=xPaid M ((le_max_left _ _).trans above) t inside h
  have each (j : Coordinate) : |2*inner ℝ (spatial M j h) (transposeAction seed M t (spatial M j h))|≤
      (epsilon/2)*gradient M (spatial M j h)+K*‖spatial M j h‖^2 :=
    pPaid M ((le_max_right _ _).trans above) t inside (spatial M j h)
  have all:=sum_work _ (fun j => gradient M (spatial M j h)) (fun j => ‖spatial M j h‖^2)
    (epsilon/2) K _ _ each (gradient_sum nu M h) (NativeWindowHistoryJacobianSpatial.mass_gradient nu M h)
  exact difference_work _ _ epsilon _ B K _ G B0 K0 x all
    (NativeWindowHistorySchurTemporalControl.source_gradient seed horizon M t inside)


end
end SaturationMonoid.NavierStokes.NativeResidualMetricPair
