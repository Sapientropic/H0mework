import H0mework.Versions.X.NavierStokes.WindowSchurMean.ForceResolution
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatial
import H0mework.Versions.X.NavierStokes.WindowSchurSchur.MixedAction

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanGraph
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanProjection (mean)
open NativeWindowHistorySchurTemporalControl (temporalResponse energy temporalBudget)
open NativeWindowHistorySchurAdvectorAction (xAction wAction)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowHistoryAnnihilationRows (input)
open NativeWindowHistoryJacobianSpatial (spatial)
open NativeWindowHistoryCreationGeometry (transport)
open NativeWindowStressOseenTest (evaluate)
open NativeWindowAugmentedGradient (derivative)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

private theorem sum_square (b : Coordinate → ℝ) (positive : ∀j,0≤b j) :
    (∑j,b j^2)≤(∑j,b j)^2 := by
  simp only [Fin.sum_univ_three]
  nlinarith only [mul_nonneg (positive 0) (positive 1),mul_nonneg (positive 0) (positive 2),mul_nonneg (positive 1) (positive 2)]

theorem finite_self_bound (nu : Viscosity) (M : ℕ) (u : physicalSpace (modes M))
    (delta K : ℝ) (delta0 : 0≤delta) (K0 : 0≤K)
    (point : ∀i,‖evaluate (modes M) (modes M) i u‖≤
      delta*‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖+
        K*‖coefficients (modes M) u‖) :
    ‖coefficients (modes M) (transport (modes M) (modes_zero M) (modes_closed M) nu u u)‖≤
      3*(delta*‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖+
        K*‖coefficients (modes M) u‖)*
          (∑j : Coordinate,‖coefficients (modes M) (derivative (modes M) (modes_zero M) (modes_closed M) j u)‖) := by
  let A:=delta*‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖+
    K*‖coefficients (modes M) u‖
  let b:=fun j => ‖coefficients (modes M) (derivative (modes M) (modes_zero M) (modes_closed M) j u)‖
  have a0:0≤A:=add_nonneg (mul_nonneg delta0 (norm_nonneg _)) (mul_nonneg K0 (norm_nonneg _))
  have b0:0≤∑j,b j:=Finset.sum_nonneg fun j _ => norm_nonneg _
  have sup:(∑i : Coordinate,‖evaluate (modes M) (modes M) i u‖^2)≤3*A^2 :=
    (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (point i) 2).trans_eq (by simp only [Fin.sum_univ_three]; ring)
  have grad:curlPair (modes M) u.1 u.1=∑j,b j^2 := by
    have actual:=NativeWindowHistoryCreationGeometry.derivative_mass (modes M) (modes_zero M) (modes_closed M) u
    simpa only [b,pairing,LinearMap.mk₂_apply,real_inner_self_eq_norm_sq] using actual.symm
  have gradient0:=NativeWindowHistorySchurSampleControl.gradient_nonnegative M u
  have bounded:=(NativeWindowHistorySchurTranspose.finite_bound nu M u u).trans (mul_le_mul_of_nonneg_right sup gradient0)
  rw [grad] at bounded
  have more:=mul_le_mul_of_nonneg_left (sum_square b (fun j => norm_nonneg _)) (show 0≤3*A^2 by positivity)
  apply (sq_le_sq₀ (norm_nonneg _) (show 0≤3*A*(∑j,b j) by positivity)).mp
  nlinarith only [bounded,more,sq_nonneg (A*(∑j,b j))]

theorem integral_norm_product (u v : H) :
    (∫lag,‖u lag‖*‖v lag‖ ∂averageMeasure)≤‖u‖*‖v‖ := by
  have source:=NativeWindowHistoryAnnihilationControl.cauchy_square (fun lag => ‖u lag‖) (fun lag => ‖v lag‖)
    (Lp.memLp u).norm (Lp.memLp v).norm
  rw [← NativeWindowTraceWholeHistory.norm_square,← NativeWindowTraceWholeHistory.norm_square,← mul_pow] at source
  have positive:0≤∫lag,‖u lag‖*‖v lag‖ ∂averageMeasure :=
    integral_nonneg fun lag => mul_nonneg (norm_nonneg (u lag)) (norm_nonneg (v lag))
  exact (sq_le_sq₀ positive (mul_nonneg (norm_nonneg u) (norm_nonneg v))).mp source

private theorem distribute (a b c d : ℝ) (z : Coordinate → ℝ) :
    3*(a*b+c*d)*(∑j,z j)=∑j,(3*a*(b*z j)+3*c*(d*z j)) := by
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  ring

theorem mean_self_bound (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (delta K : ℝ) (delta0 : 0≤delta) (K0 : 0≤K)
    (point : ∀u : physicalSpace (modes M),∀i,‖evaluate (modes M) (modes M) i u‖≤
      delta*‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖+
        K*‖coefficients (modes M) u‖) :
    ‖mean (wAction seed M time (temporalResponse seed M time))‖≤
      3*(delta*‖laplacianAction nu M (temporalResponse seed M time)‖+K*‖temporalResponse seed M time‖)*
        ∑j : Coordinate,‖spatial M j (temporalResponse seed M time)‖ := by
  let w:=temporalResponse seed M time
  let l:=laplacianAction nu M w
  let d:=fun j => spatial M j w
  have derivativeRead:∀ᵐ lag ∂averageMeasure,∀j,
      ‖coefficients (modes M) (derivative (modes M) (modes_zero M) (modes_closed M) j (input M w lag))‖=‖d j lag‖ := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [(NativeWindowHistorySpatialWords.fiber M [j]).coeFn_compLpL w] with lag read
    change d j lag=NativeWindowHistorySpatialWords.fiber M [j] (w lag) at read
    exact ((congrArg norm read).trans ((congrArg norm (NativeWindowHistoryJacobianSpatial.fiber_original M j (w lag))).trans
      (include_norm (modes M) (modes_zero M) (modes_closed M) _))).symm
  have bounded:∀ᵐ lag ∂averageMeasure,‖wAction seed M time w lag‖≤
      ∑j : Coordinate,(3*delta*(‖l lag‖*‖d j lag‖)+3*K*(‖w lag‖*‖d j lag‖)) := by
    filter_upwards [NativeWindowHistorySchurAdvectorAction.wAction_ae seed M time w,derivativeRead,
      (laplacianFiber nu M).coeFn_compLpL w] with lag original derived laplace
    rw [original,NativeWindowHistorySchurAdvectorFiber.family_original,include_norm (modes M) (modes_zero M)]
    have paid:=finite_self_bound nu M (input M w lag) delta K delta0 K0 (point (input M w lag))
    have laplaceRead:‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (input M w lag))‖=‖l lag‖ :=
      (NativeWindowMetricGraphHistory.laplacian_norm nu M (w lag)).symm.trans (congrArg norm laplace).symm
    simp only [derived,laplaceRead] at paid
    have mass:=NativeWindowMetricGraphHistory.restricted_norm M (w lag)
    have factor:delta*‖l lag‖+K*‖coefficients (modes M) (input M w lag)‖≤delta*‖l lag‖+K*‖w lag‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left mass K0)
    have sum0:0≤∑j : Coordinate,‖d j lag‖:=Finset.sum_nonneg fun j _ => norm_nonneg (d j lag)
    have bigger:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left factor (show (0:ℝ)≤3 by norm_num)) sum0
    exact (paid.trans bigger).trans_eq (distribute delta ‖l lag‖ K ‖w lag‖ (fun j => ‖d j lag‖))
  have first (j : Coordinate) : Integrable (fun lag => ‖l lag‖*‖d j lag‖) averageMeasure :=
    (Lp.memLp l).norm.integrable_mul (Lp.memLp (d j)).norm
  have last (j : Coordinate) : Integrable (fun lag => ‖w lag‖*‖d j lag‖) averageMeasure :=
    (Lp.memLp w).norm.integrable_mul (Lp.memLp (d j)).norm
  have paid:=integral_mono_ae ((Lp.memLp (wAction seed M time w)).norm.integrable (by norm_num))
    (integrable_finsetSum Finset.univ fun j _ => ((first j).const_mul (3*delta)).add ((last j).const_mul (3*K))) bounded
  have row (j : Coordinate) :
      (∫lag,3*delta*(‖l lag‖*‖d j lag‖)+3*K*(‖w lag‖*‖d j lag‖) ∂averageMeasure)≤
        3*delta*(‖l‖*‖d j‖)+3*K*(‖w‖*‖d j‖) := by
    rw [integral_add ((first j).const_mul (3*delta)) ((last j).const_mul (3*K)),integral_const_mul,integral_const_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left (integral_norm_product l (d j)) (by positivity))
      (mul_le_mul_of_nonneg_left (integral_norm_product w (d j)) (by positivity))
  have sumRead:=integral_finsetSum Finset.univ (fun j _ => ((first j).const_mul (3*delta)).add ((last j).const_mul (3*K)))
  have averaged:‖mean (wAction seed M time w)‖≤∫lag,‖wAction seed M time w lag‖ ∂averageMeasure :=
    (congrArg norm (NativeWindowHistoryMeanProjection.mean_original (wAction seed M time w))).trans_le (norm_integral_le_integral_norm _)
  exact averaged.trans (paid.trans (sumRead.trans_le ((Finset.sum_le_sum fun j _ => row j).trans_eq
    (distribute delta ‖l‖ K ‖w‖ (fun j => ‖d j‖)).symm)))

private theorem norm_sum_square (d : Coordinate → H) : (∑j,‖d j‖)^2≤3*(∑j,‖d j‖^2) := by
  have source:=Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset Coordinate) (fun _ => (1:ℝ)) (fun j => ‖d j‖)
  simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat,mul_one] using source

theorem mean_self_square (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ)
    (delta K : ℝ) (delta0 : 0≤delta) (K0 : 0≤K)
    (point : ∀u : physicalSpace (modes M),∀i,‖evaluate (modes M) (modes M) i u‖≤
      delta*‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu u)‖+
        K*‖coefficients (modes M) u‖) :
    ‖mean (wAction seed M time (temporalResponse seed M time))‖^2≤
      54*(delta^2*‖laplacianAction nu M (temporalResponse seed M time)‖^2+K^2*‖temporalResponse seed M time‖^2)*
        NativeWindowTraceWholeHistory.gradient M (temporalResponse seed M time) := by
  let w:=temporalResponse seed M time
  let L:=‖laplacianAction nu M w‖
  let U:=‖w‖
  let G:=NativeWindowTraceWholeHistory.gradient M w
  have source:=pow_le_pow_left₀ (norm_nonneg _) (mean_self_bound seed M time delta K delta0 K0 point) 2
  have sum:=norm_sum_square (fun j => spatial M j w)
  rw [NativeWindowHistoryJacobianSpatial.mass_gradient nu M w] at sum
  have scaled:=mul_le_mul_of_nonneg_left sum (show 0≤(3*(delta*L+K*U))^2 by positivity)
  have grad0:=NativeWindowHistoryMeanGradient.gradient_nonnegative seed M w
  have square:(delta*L+K*U)^2≤2*(delta^2*L^2+K^2*U^2) := by nlinarith only [sq_nonneg (delta*L-K*U)]
  have last:=mul_le_mul_of_nonneg_right square (show 0≤27*G from mul_nonneg (by norm_num) grad0)
  change _≤54*(delta^2*L^2+K^2*U^2)*G
  change _≤(3*(delta*L+K*U)*(∑j : Coordinate,‖spatial M j w‖))^2 at source
  nlinarith only [source,scaled,last]

theorem source_self_bound (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃ C : ℝ,0≤C ∧∀ M,∀ time∈Icc 0 horizon,
      ‖mean (wAction seed M time (temporalResponse seed M time))‖^2≤
        epsilon*‖laplacianAction nu M (temporalResponse seed M time)‖^2+C := by
  let T:=temporalBudget seed horizon
  let A:=T/nu.coeff
  have T0:0≤T:=NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon
  have A0:0≤A:=div_nonneg T0 nu.coeff_pos.le
  let delta:=Real.sqrt (epsilon/(54*(A+1)))
  have denominator:0<54*(A+1):=by positivity
  have delta0:0<delta:=Real.sqrt_pos.mpr (div_pos positive denominator)
  have deltaSquare:delta^2*(54*(A+1))=epsilon := by
    rw [show delta^2=epsilon/(54*(A+1)) from Real.sq_sqrt (div_nonneg positive.le denominator.le)]
    exact div_mul_cancel₀ _ denominator.ne'
  have small:54*delta^2*A≤epsilon := by nlinarith only [deltaSquare,sq_nonneg delta]
  obtain ⟨K,K0,point⟩:=NativeWindowMetricGraphSynthesis.exists_evaluate_bound nu delta delta0
  refine ⟨54*K^2*T*A,by positivity,fun M time inside => ?_⟩
  let w:=temporalResponse seed M time
  have original:=mean_self_square seed M time delta K delta0.le K0 (fun u i =>
    point (modes M) (modes M) (modes_zero M) (modes_closed M) u i)
  have grad:=NativeWindowHistorySchurMixedAction.temporal_gradient seed horizon M time inside
  have energyBound:=NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  have g0:=NativeWindowHistoryMeanGradient.gradient_nonnegative seed M w
  have mass:‖w‖^2≤T := by
    change ‖w‖^2+nu.coeff*NativeWindowTraceWholeHistory.gradient M w≤T at energyBound
    linarith only [energyBound,mul_nonneg nu.coeff_pos.le g0]
  have product:=mul_le_mul mass grad g0 T0
  have lower:=mul_le_mul_of_nonneg_left grad (show 0≤54*delta^2*‖laplacianAction nu M w‖^2 by positivity)
  have upper:=mul_le_mul_of_nonneg_left product (show 0≤54*K^2 by positivity)
  have paid:=mul_le_mul_of_nonneg_right small (sq_nonneg ‖laplacianAction nu M w‖)
  change _≤epsilon*‖laplacianAction nu M w‖^2+54*K^2*T*A
  linarith only [original,lower,upper,paid]

theorem mean_square (v : H) : ‖mean v‖^2≤‖v‖^2 := by
  have source:=NativeWindowMetricGraphGreen.mass_split v
  nlinarith only [source,sq_nonneg ‖NativeWindowHistoryMeanProjection.residual v‖]

private theorem pair_square {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a+b‖^2≤2*‖a‖^2+2*‖b‖^2 := by
  have bound:=pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [bound,sq_nonneg (‖a‖-‖b‖)]

private theorem four_square {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a-b+c+d‖^2≤4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have first:=pair_square a (-b)
  rw [norm_neg,← sub_eq_add_neg] at first
  have last:=pair_square c d
  have all:=pair_square (a-b) (c+d)
  rw [← add_assoc] at all
  linarith only [first,last,all]

theorem source_input_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      ‖NativeWindowHistoryMeanForceResolution.input seed M time‖^2≤
        epsilon*‖laplacianAction nu M (temporalResponse seed M time)‖^2+C := by
  have small:0<epsilon/8:=by positivity
  obtain ⟨low,B,B0,first⟩:=NativeWindowHistorySchurAdvectorAction.source_graph_bound seed horizon nonnegative (epsilon/8) small
  obtain ⟨C,C0,last⟩:=source_self_bound seed horizon (epsilon/8) small
  let A:=temporalBudget seed horizon/nu.coeff
  have A0:0≤A:=div_nonneg (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon) nu.coeff_pos.le
  refine ⟨low,4*(NativeForwardWindowJets.budget seed 0^2+NativeForwardWindowJets.budget seed 1^2+B*A+C),by positivity,
    fun M above time inside => ?_⟩
  let w:=temporalResponse seed M time
  have x:‖mean (xAction seed M time w)‖^2≤(epsilon/8)*‖laplacianAction nu M w‖^2+B*A :=
    (mean_square _).trans ((first M above time inside w).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (NativeWindowHistorySchurMixedAction.temporal_gradient seed horizon M time inside) B0)))
  have y:=last M time inside
  have m:‖mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)‖≤NativeForwardWindowJets.budget seed 0 := by
    change ‖(mean (NativeWindowTraceWholeHistory.finiteHistory seed time M)).1‖≤_
    rw [NativeWindowHistoryMeanTime.source_mean]
    exact NativeWindowHistoryMeanTime.jet_bound seed M 0 time
  have r:=NativeWindowHistoryMeanTime.source_rate_bound seed M time
  have mass:=pow_le_pow_left₀ (norm_nonneg _) m 2
  have rate:=pow_le_pow_left₀ (norm_nonneg _) r 2
  have source:=four_square (mean (NativeWindowTraceWholeHistory.finiteHistory seed time M))
    (mean (NativeWindowHistoryOseen.rateHistory seed M time)) (mean (xAction seed M time w)) (mean (wAction seed M time w))
  change ‖NativeWindowHistoryMeanForceResolution.input seed M time‖^2≤_ at source
  linarith only [source,mass,rate,x,y]

open NativeWindowHistoryMeanForceResolution (resolved resolvedSample)

theorem source_x_resolved (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      ‖xAction seed M time (resolved seed M time)‖^2≤
        epsilon*‖laplacianAction nu M (resolved seed M time)‖^2+C := by
  rcases NativeWindowHistoryMeanForceResolution.source_resolved_energy (nu:=nu) seed horizon nonnegative with ⟨last,A,A0,paid⟩
  have existing:=NativeWindowHistorySchurAdvectorAction.source_graph_bound (nu:=nu) seed horizon nonnegative epsilon positive
  rcases existing with ⟨first,B,B0,source⟩
  refine ⟨max first last,B*(A/nu.coeff),mul_nonneg B0 (div_nonneg A0 nu.coeff_pos.le),fun M above time inside => ?_⟩
  have e:=paid M ((le_max_right _ _).trans above) time inside
  have grad:NativeWindowTraceWholeHistory.gradient M (resolved seed M time)≤A/nu.coeff := by
    apply (le_div_iff₀ nu.coeff_pos).mpr
    change ‖resolved seed M time‖^2+nu.coeff*_≤A at e
    nlinarith only [e,sq_nonneg ‖resolved seed M time‖]
  exact (source M ((le_max_left _ _).trans above) time inside _).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left grad B0))

theorem source_w_resolved (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      ‖wAction seed M time (resolved seed M time)‖^2≤
        epsilon*‖laplacianAction nu M (temporalResponse seed M time)‖^2+C := by
  obtain ⟨low,B,B0,source⟩:=NativeWindowHistoryMeanForceResolution.source_resolved_bound (nu:=nu) seed horizon nonnegative
  have existing:=NativeWindowHistorySchurTranspose.exists_finite_bound nu (B/nu.coeff)
    (div_nonneg B0 nu.coeff_pos.le) epsilon positive
  rcases existing with ⟨K,K0,point⟩
  refine ⟨low,K*temporalBudget seed horizon,
    mul_nonneg K0 (NativeWindowHistorySchurTemporalControl.temporalBudget_nonnegative seed horizon),fun M above time inside => ?_⟩
  let w:=temporalResponse seed M time
  let y:=resolved seed M time
  let l:=laplacianAction nu M w
  have bounded:∀ᵐ lag ∂averageMeasure,‖wAction seed M time y lag‖^2≤epsilon*‖l lag‖^2+K*‖w lag‖^2 := by
    filter_upwards [NativeWindowHistorySchurAdvectorAction.wAction_ae seed M time y,
      NativeWindowHistoryMeanForceResolution.resolved_ae seed M time,source M above time inside,
      (laplacianFiber nu M).coeFn_compLpL w] with lag actual read bound laplace
    have grad:curlPair (modes M) (resolvedSample seed M time lag).1 (resolvedSample seed M time lag).1≤B/nu.coeff := by
      apply (le_div_iff₀ nu.coeff_pos).mpr
      change ‖coefficients (modes M) (resolvedSample seed M time lag)‖^2+nu.coeff*_≤B at bound
      nlinarith only [bound,sq_nonneg ‖coefficients (modes M) (resolvedSample seed M time lag)‖]
    rw [actual,read,NativeWindowHistorySchurAdvectorFiber.family_original]
    rw [NativePhysicalPairing.restrict_include (modes M) (modes_zero M) (modes_closed M) (resolvedSample seed M time lag),
      include_norm (modes M) (modes_zero M)]
    have paid:=point M (input M w lag) (resolvedSample seed M time lag) grad
    have graph:‖coefficients (modes M) (NativeWindowOperatorGreen.laplacian (modes M) (modes_zero M) (modes_closed M) nu
      (input M w lag))‖=‖l lag‖ :=
      (NativeWindowMetricGraphHistory.laplacian_norm nu M (w lag)).symm.trans (congrArg norm laplace).symm
    rw [graph] at paid
    exact paid.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (NativeWindowMetricGraphHistory.restricted_norm M (w lag)) 2) K0))
  have lp:=((Lp.memLp l).integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have wp:=((Lp.memLp w).integrable_norm_pow (by decide : (2 : ℕ)≠0))
  have paid:=integral_mono_ae ((Lp.memLp (wAction seed M time y)).integrable_norm_pow (by decide : (2 : ℕ)≠0))
    ((lp.const_mul epsilon).add (wp.const_mul K)) bounded
  have lRead:(∫lag,epsilon*‖l lag‖^2 ∂averageMeasure)=epsilon*‖l‖^2 :=
    (integral_const_mul epsilon (fun lag => ‖l lag‖^2)).trans
      (congrArg (epsilon*·) (NativeWindowTraceWholeHistory.norm_square l).symm)
  have wRead:(∫lag,K*‖w lag‖^2 ∂averageMeasure)=K*‖w‖^2 :=
    (integral_const_mul K (fun lag => ‖w lag‖^2)).trans
      (congrArg (K*·) (NativeWindowTraceWholeHistory.norm_square w).symm)
  have sumRead:=(integral_add (lp.const_mul epsilon) (wp.const_mul K)).trans
    (congrArg₂ (fun a b : ℝ => a+b) lRead wRead)
  have averaged:=(NativeWindowTraceWholeHistory.norm_square (wAction seed M time y)).trans_le (paid.trans_eq sumRead)
  have e:=NativeWindowHistorySchurTemporalControl.source_temporal_energy seed horizon M time inside
  have g0:=NativeWindowHistoryMeanGradient.gradient_nonnegative seed M w
  have mass:‖w‖^2≤temporalBudget seed horizon := by
    change ‖w‖^2+nu.coeff*_≤_ at e
    linarith only [e,mul_nonneg nu.coeff_pos.le g0]
  exact averaged.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left mass K0))

theorem resolved_heat (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    resolved seed M time+nu.coeff • laplacianAction nu M (resolved seed M time)=
      NativeWindowHistoryMeanProjection.embed (NativeWindowHistoryMeanForceResolution.input seed M time)+
        xAction seed M time (resolved seed M time)+wAction seed M time (resolved seed M time) := by
  have original:=NativeWindowHistoryMeanForceResolution.resolved_equation (nu:=nu) seed M time
  have split:=congrArg (fun A : H →L[ℝ] H => A (resolved seed M time))
    (NativeWindowHistorySchurAdvectorAction.source_action_split (nu:=nu) seed M time)
  simp only [add_apply] at split
  have heat:=NativeWindowHistorySchurAdvectorEnergy.diffusion_history nu M (resolved seed M time)
  have exactSplit:=split.trans (congrArg₂ (fun a b : H => a+b)
    (congrArg₂ (fun a b : H => a+b) heat rfl) rfl)
  have rest:resolved seed M time-(((-nu.coeff) • laplacianAction nu M (resolved seed M time)+
      xAction seed M time (resolved seed M time))+wAction seed M time (resolved seed M time))=
      NativeWindowHistoryMeanProjection.embed (NativeWindowHistoryMeanForceResolution.input seed M time) :=
    (congrArg (fun a : H => resolved seed M time-a) exactSplit).symm.trans original
  rw [neg_smul] at rest
  exact (congrArg (fun v : H => v+xAction seed M time (resolved seed M time)+wAction seed M time (resolved seed M time)) rest).symm.trans
    (by module) |>.symm

private theorem positive_graph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a : ℝ) (positive : 0<a) (z l f : E) (source : z+a • l=f) (green : 0 ≤ inner ℝ z l) :
    a^2*‖l‖^2≤‖f‖^2 := by
  have actual:=congrArg (fun v : E => ‖v‖^2) source
  rw [norm_add_sq_real,norm_smul,Real.norm_eq_abs,abs_of_pos positive,real_inner_smul_right] at actual
  nlinarith only [actual,sq_nonneg ‖z‖,mul_nonneg positive.le green]

private theorem three_square {E : Type*} [SeminormedAddCommGroup E] (a b c : E) :
    ‖a+b+c‖^2≤4*(‖a‖^2+‖b‖^2+‖c‖^2) := by
  have first:=pair_square a b
  have last:=pair_square (a+b) c
  linarith only [first,last,sq_nonneg ‖c‖]

theorem source_resolved_graph (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      ‖laplacianAction nu M (resolved seed M time)‖^2≤
        epsilon*‖laplacianAction nu M (temporalResponse seed M time)‖^2+C := by
  have viscosity:0<nu.coeff^2:=sq_pos_of_pos nu.coeff_pos
  have small:0<nu.coeff^2*epsilon/16:=div_pos (mul_pos viscosity positive) (by norm_num)
  obtain ⟨first,A,A0,paidA⟩:=source_input_bound (nu:=nu) seed horizon nonnegative (nu.coeff^2*epsilon/16) small
  have existingB:=source_x_resolved (nu:=nu) seed horizon nonnegative (nu.coeff^2/8) (div_pos viscosity (by norm_num))
  obtain ⟨middle,B,B0,paidB⟩:=existingB
  have existingC:=source_w_resolved (nu:=nu) seed horizon nonnegative (nu.coeff^2*epsilon/16) small
  obtain ⟨last,C,C0,paidC⟩:=existingC
  refine ⟨max first (max middle last),8*(A+B+C)/nu.coeff^2,by positivity,fun M above time inside => ?_⟩
  let y:=resolved seed M time
  let w:=temporalResponse seed M time
  have green:0 ≤ inner ℝ y (laplacianAction nu M y) :=
    (NativeWindowHistoryMeanGradient.gradient_nonnegative seed M y).trans_eq
      (NativeWindowMetricGraphHistory.history_gradient nu M y).symm
  have coercive:=positive_graph (E:=H) nu.coeff nu.coeff_pos _ _ _ (resolved_heat seed M time) green
  have sum:=three_square (E:=H) (NativeWindowHistoryMeanProjection.embed (NativeWindowHistoryMeanForceResolution.input seed M time))
    (xAction seed M time y) (wAction seed M time y)
  have normRead:=congrArg (fun a : ℝ => a^2)
    (NativeWindowHistoryMeanProjection.embed_norm (NativeWindowHistoryMeanForceResolution.input seed M time))
  have sumRead:=sum.trans_eq (congrArg (fun a : ℝ => 4*(a+‖xAction seed M time y‖^2+‖wAction seed M time y‖^2)) normRead)
  have a:=paidA M ((le_max_left _ _).trans above) time inside
  have b:=paidB M ((le_max_left _ _).trans ((le_max_right _ _).trans above)) time inside
  have c:=paidC M ((le_max_right _ _).trans ((le_max_right _ _).trans above)) time inside
  have cancel:nu.coeff^2*(8*(A+B+C)/nu.coeff^2)=8*(A+B+C):=mul_div_cancel₀ _ viscosity.ne'
  apply (mul_le_mul_iff_right₀ viscosity).mp
  nlinarith only [coercive,sumRead,a,b,c,cancel]

theorem mean_graph_bound (nu : Viscosity) (M : ℕ) (v : H) :
    ‖laplacianFiber nu M (mean v)‖^2≤‖laplacianAction nu M v‖^2 :=
  (congrArg (fun u : wholePhysical => ‖u‖^2)
    (NativeWindowHistoryMeanProjection.mean_comp (laplacianFiber nu M) v)).symm.trans_le
      (mean_square (laplacianAction nu M v))

theorem source_mean_graph (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,
      ‖laplacianFiber nu M (mean (resolved seed M time))‖^2≤
        epsilon*‖laplacianAction nu M (temporalResponse seed M time)‖^2+C := by
  obtain ⟨low,C,C0,source⟩:=source_resolved_graph (nu:=nu) seed horizon nonnegative epsilon positive
  exact ⟨low,C,C0,fun M above time inside => (mean_graph_bound nu M _).trans (source M above time inside)⟩

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem input_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    NativeWindowHistoryMeanForceResolution.input seed M (step.2.clockAdvance+time)=
      NativeWindowHistoryMeanForceResolution.input step.1 M time :=
  (NativeWindowHistoryMeanForceResolution.input_original seed M _).trans
    ((congrArg₂ (fun (c : wholePhysical) (f : H) => c-mean f)
      (NativeWindowHistoryInverseWindow.commonForce_next seed M step generated time nonnegative)
      (NativeWindowHistoryOseen.forcingHistory_next seed M step generated time nonnegative)).trans
        (NativeWindowHistoryMeanForceResolution.input_original step.1 M time).symm)

theorem mean_graph_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (nonnegative : 0≤time) :
    laplacianFiber nu M (mean (resolved seed M (step.2.clockAdvance+time)))=
      laplacianFiber nu M (mean (resolved step.1 M time)) :=
  congrArg (fun v : H => laplacianFiber nu M (mean v))
    (NativeWindowHistoryMeanForceResolution.resolved_next seed M step generated time nonnegative)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanGraph
