import H0mework.Versions.X.NavierStokes.WindowHistory.Covariance.Centered.JointCubicGate

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeCenteredCouplingPaid
open Set
open ThreeDimensionalPeriodicCoarseFilterCore (Coordinate)
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
open NativeWindowTraceWholeHistory (H gradient)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section
variable {nu : Viscosity}

private theorem scalar_young (a b delta : ℝ) (positive : 0<delta) :
    a*b≤delta*b^2+a^2/(4*delta) := by
  have identity : delta*b^2+a^2/(4*delta)-a*b=(2*delta*b-a)^2/(4*delta) := by
    field_simp [positive.ne']
    ring
  have square : 0≤(2*delta*b-a)^2/(4*delta) :=
    div_nonneg (sq_nonneg _) (by positivity)
  linarith only [identity,square]

private theorem gradient_paid {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x : E) (L : E →L[ℝ] E)
    (K eta G : ℝ) (K0 : 0≤K) (eta0 : 0<eta)
    (mass : ‖x‖^2≤G) :
    K*inner ℝ x (L x)≤eta*‖L x‖^2+(K^2/(4*eta))*G := by
  have pair:=real_inner_le_norm x (L x)
  have scaled:=mul_le_mul_of_nonneg_left pair K0
  have young:=scalar_young (K*‖x‖) ‖L x‖ eta eta0
  have normalized : (K*‖x‖)^2/(4*eta)=(K^2/(4*eta))*‖x‖^2 := by ring
  rw [normalized] at young
  have coefficient : 0≤K^2/(4*eta) := by positivity
  have massPaid:=mul_le_mul_of_nonneg_left mass coefficient
  nlinarith only [scaled,young,massPaid]

theorem source_annihilation_q_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon eta : ℝ) (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →∀j : Coordinate,
      let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
      ‖NativeWindowHistoryMeanBlocks.annihilation seed M time q‖^2≤
        eta*‖laplacianAction nu M q‖^2+C := by
  let delta:=eta/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let K:=NativeWindowHistoryAnnihilationControl.budget seed horizon delta
  have K0 : 0≤K:=NativeWindowHistoryAnnihilationControl.budget_nonnegative seed horizon delta delta0
  let G:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  have G0 : 0≤G:=le_max_left _ _
  let C:=(K^2/(4*delta))*G
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨C,C0,fun M time inside j => ?_⟩
  let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
  let L:=laplacianAction nu M
  have original:=NativeWindowHistoryAnnihilationControl.source_annihilation_bound
    seed horizon delta delta0 M time inside q
  have mass:=NativeCenteredBathPaid.source_first_word_q_mass seed horizon M time inside j
  have read : gradient M q=inner ℝ q (L q) :=
    (NativeWindowMetricGraphHistory.history_gradient nu M q).symm
  rw [read] at original
  have paid:=gradient_paid q L K delta G K0 delta0 mass
  dsimp only [q,L,C,delta] at original paid ⊢
  nlinarith only [original,paid]

theorem source_creation_u_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon eta : ℝ) (positive : 0<eta) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →∀j : Coordinate,
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      ‖NativeWindowHistoryMeanAction.creation seed M time u‖^2≤
        eta*‖laplacianFiber nu M u‖^2+C := by
  let delta:=eta/2
  have delta0 : 0<delta:=by dsimp only [delta]; positivity
  let K:=NativeWindowHistoryCreationSource.budget seed horizon delta
  have K0 : 0≤K:=NativeWindowHistoryCreationSource.budget_nonnegative seed horizon delta delta0
  let G:=max 0 (NativeWindowAugmentedPayment.graphBudget seed 0 horizon)
  have G0 : 0≤G:=le_max_left _ _
  let C:=(K^2/(4*delta))*G
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨C,C0,fun M time inside j => ?_⟩
  let m:=NativeWindowHistoryMeanAction.meanValue seed M time
  let v:=NativeWindowHistorySpatialTransport.finite M j m
  let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
  let L:=laplacianFiber nu M
  have included : u=includeCLM (modes M) (modes_closed M) v :=
    NativeCenteredMeanPrincipal.source_word_included seed M time j
  have source:=NativeWindowHistoryCreationSource.source_creation_bound
    seed horizon delta delta0 M time inside v
  have sourceRead : ‖NativeWindowHistoryMeanAction.creation seed M time u‖^2≤
      delta*‖L u‖^2+K*inner ℝ u (L u) := by
    rw [included]
    have graph : NativeFiniteActionResolvent.pairing (modes M)
        (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)
        (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)=
        ‖L (includeCLM (modes M) (modes_closed M) v)‖^2 := by
      change inner ℝ
        (NativeFiniteActionResolvent.coefficients (modes M)
          (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v))
        (NativeFiniteActionResolvent.coefficients (modes M)
          (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu v)) = _
      rw [real_inner_self_eq_norm_sq,
        NativeWindowMetricGraphHistory.laplacian_norm,restrict_include]
    have grad : NativeCommonAdvectorAction.curlPair (modes M) v.1 v.1=
        inner ℝ (includeCLM (modes M) (modes_closed M) v)
          (L (includeCLM (modes M) (modes_closed M) v)) := by
      rw [NativeWindowMetricGraphHistory.fiber_gradient,restrict_include]
    rw [graph,grad] at source
    exact source
  have mass:=NativeCenteredMeanPrincipal.source_first_word_u_mass seed horizon M time inside j
  have paid:=gradient_paid u L K delta G K0 delta0 mass
  dsimp only [u,L,C,delta] at sourceRead paid ⊢
  nlinarith only [sourceRead,paid]

private theorem square_two {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x+y‖^2≤2*(‖x‖^2+‖y‖^2) := by
  have upper:=norm_add_le x y
  have squared:=pow_le_pow_left₀ (norm_nonneg _) upper 2
  nlinarith only [squared,sq_nonneg (‖x‖-‖y‖)]

private theorem pair_young {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (x y : E) (alpha : ℝ) (positive : 0<alpha) :
    2*inner ℝ x y≤alpha*‖x‖^2+alpha⁻¹*‖y‖^2 := by
  have pair:=real_inner_le_norm x y
  have square : 0≤(alpha*‖x‖-‖y‖)^2/alpha :=
    div_nonneg (sq_nonneg _) positive.le
  have identity : (alpha*‖x‖-‖y‖)^2/alpha=
      alpha*‖x‖^2+alpha⁻¹*‖y‖^2-2*‖x‖*‖y‖ := by
    field_simp [positive.ne']
    ring
  rw [identity] at square
  nlinarith only [pair,square]

private theorem weighted_square {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (x y : E) (a : ℝ) (positive : 0≤a) :
    ‖x+a • y‖^2≤2*(‖x‖^2+a^2*‖y‖^2) := by
  have bound:=square_two x (a • y)
  rwa [norm_smul,Real.norm_eq_abs,abs_of_nonneg positive,mul_pow] at bound

theorem source_coupling_paid (seed : GeneratedWholeRestartCurrent nu)
    (horizon epsilonU epsilonQ : ℝ) (uPositive : 0<epsilonU)
    (qPositive : 0<epsilonQ) :
    ∃C : ℝ,0≤C ∧∀M (time : ℝ),time∈Icc 0 horizon →∀j : Coordinate,
      let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
      let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
      2*inner ℝ q (NativeCenteredCouplingCommutator.creationCommutator seed M time u)≤
        epsilonU*‖laplacianFiber nu M u‖^2+
          epsilonQ*‖laplacianAction nu M q‖^2+C := by
  let alpha:=epsilonU/(4*nu.coeff^2)
  let beta:=epsilonQ/(4*nu.coeff^2)
  have alpha0 : 0<alpha:=by dsimp only [alpha]; positivity [nu.coeff_pos]
  have beta0 : 0<beta:=by dsimp only [beta]; positivity [nu.coeff_pos]
  let etaA:=alpha*epsilonQ/2
  let etaC:=beta*epsilonU/2
  have etaA0 : 0<etaA:=by dsimp only [etaA]; positivity
  have etaC0 : 0<etaC:=by dsimp only [etaC]; positivity
  obtain ⟨CA,CA0,annPaid⟩:=source_annihilation_q_paid seed horizon etaA etaA0
  obtain ⟨CC,CC0,crePaid⟩:=source_creation_u_paid seed horizon etaC etaC0
  let GU:=max 0 (NativeWindowAugmentedPayment.graphBudget seed 0 horizon)
  let GQ:=NativeWindowHistorySchurTemporalControl.gradientBudget seed horizon
  have GU0 : 0≤GU:=le_max_left _ _
  have GQ0 : 0≤GQ:=le_max_left _ _
  let C:=2*alpha*GU+alpha⁻¹*CA+2*beta*GQ+beta⁻¹*CC
  have C0 : 0≤C:=by dsimp only [C]; positivity
  refine ⟨C,C0,fun M time inside j => ?_⟩
  let u:=NativeWindowHistoryAllOrderWord.value seed M [j] time
  let q:=NativeCenteredWeightedResidualRate.centeredWord seed M j time
  let LU:=laplacianFiber nu M u
  let LQ:=laplacianAction nu M q
  let w:=NativeWindowHistoryAllOrderPrincipal.weight nu M u
  let h:=NativeWindowHistoryJacobianControl.heat nu M q
  let a:=NativeWindowHistoryMeanBlocks.annihilation seed M time q
  let c:=NativeWindowHistoryMeanAction.creation seed M time u
  have massU:=NativeCenteredMeanPrincipal.source_first_word_u_mass seed horizon M time inside j
  have massQ:=NativeCenteredBathPaid.source_first_word_q_mass seed horizon M time inside j
  have weightRead : w=u+nu.coeff • LU:=rfl
  have heatRead : h=q+nu.coeff • LQ:=rfl
  have wBound:=weighted_square u LU nu.coeff nu.coeff_pos.le
  have hBound:=weighted_square q LQ nu.coeff nu.coeff_pos.le
  rw [← weightRead] at wBound
  rw [← heatRead] at hBound
  have pairA:=pair_young w a alpha alpha0
  have pairC:=pair_young h c beta beta0
  have ann:=annPaid M time inside j
  have cre:=crePaid M time inside j
  have scaledU:=mul_le_mul_of_nonneg_left massU (show 0≤2*alpha by positivity)
  have scaledQ:=mul_le_mul_of_nonneg_left massQ (show 0≤2*beta by positivity)
  have scaledW:=mul_le_mul_of_nonneg_left wBound alpha0.le
  have scaledH:=mul_le_mul_of_nonneg_left hBound beta0.le
  have scaledA:=mul_le_mul_of_nonneg_left ann (inv_nonneg.mpr alpha0.le)
  have scaledC:=mul_le_mul_of_nonneg_left cre (inv_nonneg.mpr beta0.le)
  have coefficientU : 2*alpha*nu.coeff^2+beta⁻¹*etaC=epsilonU := by
    dsimp only [alpha,beta,etaC]
    field_simp [nu.coeff_pos.ne',qPositive.ne']
    ring
  have coefficientQ : 2*beta*nu.coeff^2+alpha⁻¹*etaA=epsilonQ := by
    dsimp only [alpha,beta,etaA]
    field_simp [nu.coeff_pos.ne',uPositive.ne']
    ring
  have coupling:=NativeCenteredCouplingCommutator.source_coupling_commutator seed M time u q
  dsimp only [u,q,LU,LQ,w,h,a,c,C,GU,GQ] at *
  nlinarith only [pairA,pairC,scaledU,scaledQ,scaledW,scaledH,
    scaledA,scaledC,coefficientU,coefficientQ,coupling]

end
end SaturationMonoid.NavierStokes.NativeCenteredCouplingPaid
