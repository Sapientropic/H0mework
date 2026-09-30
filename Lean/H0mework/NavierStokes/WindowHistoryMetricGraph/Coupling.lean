import H0mework.NavierStokes.WindowHistoryMetricGraph.History

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowMetricGraphCoupling
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open NativeFiniteActionResolvent NativeCommonAdvectorAction NativeWholeH1Mixed
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativeWindowHistoryOseen (H action)
open NativeWindowHistoryMeanProjection (embed)
open NativeWindowHistoryMeanAction (creation)
open NativeWindowHistoryMeanBlocks (annihilation)
open NativeWindowTraceWholeHistory (metric metricAction)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
noncomputable section
variable {nu : Viscosity}

private def theta (epsilon K : ℝ) : ℝ := epsilon/(4*(K+1))
private def delta (epsilon K : ℝ) : ℝ := epsilon*theta epsilon K
private def remainder (epsilon K B D : ℝ) : ℝ := theta epsilon K*K+(B^2+D^2)/(16*delta epsilon K*theta epsilon K)

private theorem theta_positive {epsilon K : ℝ} (positive : 0 < epsilon) (K0 : 0 ≤ K) : 0 < theta epsilon K :=
  div_pos positive (by positivity)

private theorem delta_positive {epsilon K : ℝ} (positive : 0 < epsilon) (K0 : 0 ≤ K) : 0 < delta epsilon K :=
  mul_pos positive (theta_positive positive K0)

private theorem remainder_nonnegative {epsilon K : ℝ} (positive : 0 < epsilon) (K0 : 0 ≤ K) (B D : ℝ) :
    0 ≤ remainder epsilon K B D := by
  have a := theta_positive positive K0
  have b := delta_positive positive K0
  unfold remainder
  positivity

private theorem young (x y eta : ℝ) (positive : 0 < eta) : x*y ≤ eta*x^2+y^2/(4*eta) := by
  have cancel : (4*eta)*(y^2/(4*eta))=y^2 := mul_div_cancel₀ _ (by positivity : 4*eta≠0)
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < 4*eta)).mp
  nlinarith only [sq_nonneg (2*eta*x-y),cancel]

private theorem slope (c d m B eta : ℝ) (positive : 0 < eta)
    (bound : c^2 ≤ eta*d^2+B*m*d) : c^2 ≤ 2*eta*d^2+(B^2/(4*eta))*m^2 := by
  have small := young d (B*m) eta positive
  have same : (B*m)^2/(4*eta)=(B^2/(4*eta))*m^2 := by ring
  nlinarith only [bound,small,same]

private theorem cross_arithmetic (epsilon K B D t1 t2 c a d1 d2 m1 m2 : ℝ)
    (positive : 0 < epsilon) (K0 : 0 ≤ K)
    (first : t1^2 ≤ K*(d1^2+m1^2)) (last : t2^2 ≤ K*(d2^2+m2^2))
    (created : c^2 ≤ delta epsilon K*d1^2+B*m1*d1)
    (annihilated : a^2 ≤ delta epsilon K*d2^2+D*m2*d2) :
    t2*c+a*t1 ≤ epsilon*(d1^2+d2^2)+remainder epsilon K B D*(m1^2+m2^2) := by
  let eta := theta epsilon K
  let z := delta epsilon K
  have eta0 : 0 < eta := theta_positive positive K0
  have z0 : 0 < z := delta_positive positive K0
  have cu := slope c d1 m1 B z z0 created
  have ar := slope a d2 m2 D z z0 annihilated
  have extra := add_nonneg
    (mul_nonneg (div_nonneg (sq_nonneg B) (by positivity : 0 ≤ 4*z)) (sq_nonneg m2))
    (mul_nonneg (div_nonneg (sq_nonneg D) (by positivity : 0 ≤ 4*z)) (sq_nonneg m1))
  have sum : c^2+a^2 ≤ 2*z*(d1^2+d2^2)+((B^2+D^2)/(4*z))*(m1^2+m2^2) := by
    simp only [add_div]
    nlinarith only [cu,ar,extra]
  have tSum : t1^2+t2^2 ≤ K*((d1^2+d2^2)+(m1^2+m2^2)) := by linarith only [first,last]
  have tScaled := mul_le_mul_of_nonneg_left tSum eta0.le
  have cScaled := div_le_div_of_nonneg_right sum (by positivity : 0 ≤ 4*eta)
  have y1 := young t2 c eta eta0
  have y2 := young t1 a eta eta0
  have used : t2*c+a*t1 ≤ eta*K*((d1^2+d2^2)+(m1^2+m2^2))+
      (2*z*(d1^2+d2^2)+((B^2+D^2)/(4*z))*(m1^2+m2^2))/(4*eta) := by
    simp only [add_div] at cScaled ⊢
    linarith only [tScaled,cScaled,y1,y2]
  have leading : eta*K ≤ epsilon/4 := by
    dsimp only [eta,theta]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 4*(K+1))).mpr
    nlinarith
  have rate : z/(2*eta)=epsilon/2 := by
    dsimp only [z,delta]
    change epsilon*eta/(2*eta)=epsilon/2
    field_simp [eta0.ne']
  have actual : eta*K*((d1^2+d2^2)+(m1^2+m2^2))+
      (2*z*(d1^2+d2^2)+((B^2+D^2)/(4*z))*(m1^2+m2^2))/(4*eta)=
      (eta*K+z/(2*eta))*(d1^2+d2^2)+remainder epsilon K B D*(m1^2+m2^2) := by
    change _=(eta*K+z/(2*eta))*(d1^2+d2^2)+(eta*K+(B^2+D^2)/(16*z*eta))*(m1^2+m2^2)
    field_simp [eta0.ne',z0.ne']
    ring
  have paid := mul_le_mul_of_nonneg_right (show eta*K+z/(2*eta) ≤ epsilon by rw [rate]; linarith)
    (add_nonneg (sq_nonneg d1) (sq_nonneg d2))
  linarith only [used,actual,paid]

def coupling (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ) (F : Finset IntegerWavevector)
    (R : ℕ) (u : wholePhysical) (v : H) : ℝ :=
  inner ℝ (embed u) (metricAction seed frame M F R (action seed M time (NativeWindowHistoryMeanProjection.residual v)))+
    inner ℝ (NativeWindowHistoryMeanProjection.residual v) (metricAction seed frame M F R (action seed M time (embed u)))

theorem coupling_adjoint (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ) (F : Finset IntegerWavevector)
    (R : ℕ) (u : wholePhysical) (v : H) : coupling seed M frame time F R u v=
      inner ℝ (metricAction seed frame M F R v) (creation seed M time u)+
        inner ℝ (annihilation seed M time v) (metric seed frame M F R u) := by
  have original : coupling seed M frame time F R u v=inner ℝ v
      (metricAction seed frame M F R (creation seed M time u)-creation seed M time ((metric seed frame M F R).adjoint u)) :=
    NativeWindowHistoryMeanBlocks.metric_coupling seed M frame time F R u v
  rw [NativeWindowMetricGraphHistory.metric_adjoint] at original
  have cancel := NativeWindowHistoryMeanBlocks.coupling_green seed M time (metric seed frame M F R u) v
  have one := NativeWindowMetricGraphHistory.action_symmetric seed frame M F R v (creation seed M time u)
  have two := real_inner_comm (F := H) v (creation seed M time (metric seed frame M F R u))
  have three := real_inner_comm (F := wholePhysical) (annihilation seed M time v) (metric seed frame M F R u)
  have difference := inner_sub_right (𝕜 := ℝ) v (metricAction seed frame M F R (creation seed M time u))
    (creation seed M time (metric seed frame M F R u))
  linarith only [original,cancel,one,two,three,difference]

theorem coupling_abs (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ) (F : Finset IntegerWavevector)
    (R : ℕ) (u : wholePhysical) (v : H) : |coupling seed M frame time F R u v| ≤
      ‖metricAction seed frame M F R v‖*‖creation seed M time u‖+
        ‖annihilation seed M time v‖*‖metric seed frame M F R u‖ := by
  rw [coupling_adjoint]
  simpa only [] using! (abs_add_le _ _).trans (add_le_add
    (abs_real_inner_le_norm (metricAction seed frame M F R v) (creation seed M time u))
    (abs_real_inner_le_norm (annihilation seed M time v) (metric seed frame M F R u)))

private theorem creation_estimate (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) (u : wholePhysical) :
    ‖creation seed M time u‖^2 ≤ epsilon*‖laplacianFiber nu M u‖^2+
      NativeWindowHistoryCreationSource.budget seed horizon epsilon*‖u‖*‖laplacianFiber nu M u‖ := by
  have source := NativeWindowHistoryCreationSource.source_whole_bound seed horizon epsilon positive M time inside u
  dsimp only at source
  have bounded : curlPair (modes M) (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1
      (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1 ≤ ‖u‖*‖laplacianFiber nu M u‖ := by
    rw [← NativeWindowMetricGraphHistory.fiber_gradient nu M u]
    exact real_inner_le_norm u (laplacianFiber nu M u)
  have paid := mul_le_mul_of_nonneg_left bounded (NativeWindowHistoryCreationSource.budget_nonnegative seed horizon epsilon positive)
  rw [NativeWindowMetricGraphHistory.laplacian_norm]
  change ‖creation seed M time u‖^2 ≤ epsilon*‖coefficients (modes M) _‖^2+_
  have normed := real_inner_self_eq_norm_sq (coefficients (modes M) (NativeWindowOperatorGreen.laplacian
    (modes M) (modes_zero M) (modes_closed M) nu (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)))
  change pairing (modes M) _ _=‖coefficients (modes M) _‖^2 at normed
  rw [normed] at source
  rw [NativeWindowMetricGraphHistory.laplacian_norm] at paid
  nlinarith only [source,paid]

private theorem annihilation_estimate (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0 < epsilon)
    (M : ℕ) (time : ℝ) (inside : time ∈ Icc 0 horizon) (v : H) :
    ‖annihilation seed M time v‖^2 ≤ epsilon*‖laplacianAction nu M v‖^2+
      NativeWindowHistoryAnnihilationControl.budget seed horizon epsilon*‖v‖*‖laplacianAction nu M v‖ := by
  have source := NativeWindowHistoryAnnihilationControl.source_annihilation_bound seed horizon epsilon positive M time inside v
  have paid := mul_le_mul_of_nonneg_left (NativeWindowMetricGraphHistory.gradient_bound nu M v)
    (NativeWindowHistoryAnnihilationControl.budget_nonnegative seed horizon epsilon positive)
  nlinarith only [source,paid]

theorem source_coupling_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,∀ u : wholePhysical,∀ v : H,
      |coupling seed M frame time (integerWaveFrequencyCube cutoff) radius u v| ≤
        epsilon*(‖laplacianFiber nu M u‖^2+‖laplacianAction nu M v‖^2)+C*(‖u‖^2+‖v‖^2) := by
  obtain ⟨first,K1,K10,point⟩ := NativeWindowMetricGraphHistory.source_point_bound seed horizon nonnegative
  obtain ⟨last,K2,K20,history⟩ := NativeWindowMetricGraphHistory.source_history_bound seed horizon nonnegative
  let K:=K1+K2+1
  have K0 : 0 ≤ K := by dsimp only [K]; positivity
  let z:=delta epsilon K
  have z0 : 0 < z := delta_positive positive K0
  let B:=NativeWindowHistoryCreationSource.budget seed horizon z
  let D:=NativeWindowHistoryAnnihilationControl.budget seed horizon z
  refine ⟨max first last,remainder epsilon K B D,remainder_nonnegative positive K0 B D,
    fun radius above cutoff covered M frame frameInside time timeInside u v => ?_⟩
  have t1 := (point radius ((le_max_left _ _).trans above) cutoff ((le_max_left _ _).trans covered) M frame frameInside u).1
  have t2 := (history radius ((le_max_right _ _).trans above) cutoff ((le_max_right _ _).trans covered) M frame frameInside v).1
  have t1' : ‖metric seed frame M (integerWaveFrequencyCube cutoff) radius u‖^2 ≤ K*(‖laplacianFiber nu M u‖^2+‖u‖^2) :=
    t1.trans (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (by positivity))
  have t2' : ‖metricAction seed frame M (integerWaveFrequencyCube cutoff) radius v‖^2 ≤ K*(‖laplacianAction nu M v‖^2+‖v‖^2) :=
    t2.trans (mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith) (by positivity))
  exact (coupling_abs seed M frame time _ radius u v).trans
    (cross_arithmetic epsilon K B D _ _ _ _ _ _ _ _ positive K0 t1' t2'
      (creation_estimate seed horizon z z0 M time timeInside u) (annihilation_estimate seed horizon z z0 M time timeInside v))

def principalWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (frame time : ℝ)
    (F : Finset IntegerWavevector) (R : ℕ) (u : wholePhysical) (v : H) : ℝ :=
  -2*nu.coeff*inner ℝ (metric seed frame M F R u) (laplacianFiber nu M u)-
    2*nu.coeff*inner ℝ (metricAction seed frame M F R v) (laplacianAction nu M v)+
      2*coupling seed M frame time F R u v

theorem source_principal_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0 ≤ horizon) :
    ∃ low : ℕ,∃ C : ℝ,0 ≤ C ∧ ∀ radius ≥ low,∀ cutoff ≥ low,∀ M : ℕ,
      ∀ frame ∈ Icc 0 horizon,∀ time ∈ Icc 0 horizon,∀ u : wholePhysical,∀ v : H,
      principalWork seed M frame time (integerWaveFrequencyCube cutoff) radius u v ≤
        -(nu.coeff^2/2)*(‖laplacianFiber nu M u‖^2+‖laplacianAction nu M v‖^2)+C*(‖u‖^2+‖v‖^2) := by
  have pointFact := @NativeWindowMetricGraphHistory.source_point_bound nu seed horizon nonnegative
  rcases pointFact with ⟨first,K1,K10,point⟩
  have historyFact := @NativeWindowMetricGraphHistory.source_history_bound nu seed horizon nonnegative
  rcases historyFact with ⟨last,K2,K20,history⟩
  obtain ⟨third,K3,K30,cross⟩ := source_coupling_bound seed horizon nonnegative (nu.coeff^2/4) (by positivity [nu.coeff_pos])
  refine ⟨max (max first last) third,K1+K2+2*K3,by positivity,
    fun radius above cutoff covered M frame frameInside time timeInside u v => ?_⟩
  have a : first ≤ max (max first last) third := (le_max_left _ _).trans (le_max_left _ _)
  have b : last ≤ max (max first last) third := (le_max_right _ _).trans (le_max_left _ _)
  have c : third ≤ max (max first last) third := le_max_right _ _
  have one := (point radius (a.trans above) cutoff (a.trans covered) M frame frameInside u).2
  have two := (history radius (b.trans above) cutoff (b.trans covered) M frame frameInside v).2
  have three := cross radius (c.trans above) cutoff (c.trans covered) M frame frameInside time timeInside u v
  have extra := add_nonneg (mul_nonneg K10 (sq_nonneg ‖v‖)) (mul_nonneg K20 (sq_nonneg ‖u‖))
  have signed := le_abs_self (coupling seed M frame time (integerWaveFrequencyCube cutoff) radius u v)
  unfold principalWork
  nlinarith only [one,two,three,extra,signed]

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem coupling_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (frame time : ℝ)
    (frame0 : 0 ≤ frame) (time0 : 0 ≤ time) (u : wholePhysical) (v : H) :
    coupling seed M (step.2.clockAdvance+frame) (step.2.clockAdvance+time) F R u v=
      coupling step.1 M frame time F R u v := by
  have same := NativeWindowHistoryOseen.whole_next seed M step generated time time0
  simp only [Prod.mk.injEq] at same
  simp only [coupling,same.1,NativeWindowTraceWholeHistory.metricAction_next seed step generated frame frame0]

theorem principal_next (seed : GeneratedWholeRestartCurrent nu)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step)
    (M : ℕ) (F : Finset IntegerWavevector) (R : ℕ) (frame time : ℝ)
    (frame0 : 0 ≤ frame) (time0 : 0 ≤ time) (u : wholePhysical) (v : H) :
    principalWork seed M (step.2.clockAdvance+frame) (step.2.clockAdvance+time) F R u v=
      principalWork step.1 M frame time F R u v := by
  have same : metric seed (step.2.clockAdvance+frame) M F R=metric step.1 frame M F R :=
    congrArg (fun op : wholePhysical →L[ℝ] wholePhysical => NativeWindowTraceWholeHistory.projection M-op)
      (NativeWindowTraceWholeHistory.joint_next seed step generated frame frame0 M F R)
  simp only [principalWork,same,NativeWindowTraceWholeHistory.metricAction_next seed step generated frame frame0,
    coupling_next seed step generated M F R frame time frame0 time0]

end
end SaturationMonoid.NavierStokes.NativeWindowMetricGraphCoupling
