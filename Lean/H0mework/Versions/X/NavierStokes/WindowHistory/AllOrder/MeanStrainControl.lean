import H0mework.Versions.X.NavierStokes.WindowSchurMean.ResidualLoad
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianSpatialTransport

set_option autoImplicit false
open scoped Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrainControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeWholeResolvent (wholePhysical restrictCLM restrict_energy)
open NativeFiniteActionResolvent (physicalSpace pairing coefficients)
open NativeCommonAdvectorAction (curlPair)
open NativePhysicalPairing (includeCLM include_norm)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H)
open NativeWindowHistoryMeanAction (meanValue)
open NativeWindowHistoryAdjointSpatialHalf (moment outputSquare energyCap)
open NativeWindowHistoryAdjointSpatialFeedback (transportCap transportCap_nonnegative)
open NativeWindowHistoryDynamicKernel (transport)
open NativeForwardWindowPairingReadout (averageMeasure)
open NativeWindowTraceWholeHistory (gradient)
noncomputable section
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
local instance historySeminormed : SeminormedAddCommGroup H :=
  (inferInstance : NormedAddCommGroup H).toSeminormedAddCommGroup
variable {nu : Viscosity}

def fiber (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : wholePhysical →L[ℝ] wholePhysical :=
  NativeWindowHistoryOseen.lift M ((transport nu M).flip (meanValue seed M t))

def action (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) : H →L[ℝ] H :=
  (fiber seed M t).compLpL 2 averageMeasure

theorem fiber_original (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) (u : wholePhysical) :
    fiber seed M t u=includeCLM (modes M) (modes_closed M)
      (transport nu M (restrictCLM (modes M) (modes_zero M) (modes_closed M) u) (meanValue seed M t)) := rfl

private theorem strong_square (M : ℕ) (v : physicalSpace (modes M)) :
    outputSquare true (modes M) v=‖includeCLM (modes M) (modes_closed M) v‖^2 := by
  rw [include_norm (modes M) (modes_zero M)]
  have source:=(NativeWindowHistoryCreationGeometry.pairing_mass (modes M) v).symm.trans
    (real_inner_self_eq_norm_sq (coefficients (modes M) v))
  simpa only [NativeWindowHistoryAdjointSpatialHalf.outputSquare,NativeWindowHistoryAdjointSpatialHalf.weight,
    if_true,one_pow,one_mul] using source

def normBudget (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : ℝ :=
  transportCap*energyCap nu*max 0 (NativeWindowSobolevVelocity.budget seed 0 horizon)

theorem normBudget_nonnegative (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) : 0≤normBudget seed horizon := by
  unfold normBudget
  positivity [transportCap_nonnegative,NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu]

theorem finite_norm (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (t : ℝ)
    (inside : t∈Icc 0 horizon) (u : physicalSpace (modes M)) :
    ‖includeCLM (modes M) (modes_closed M) (transport nu M u (meanValue seed M t))‖^2≤
      normBudget seed horizon*(‖includeCLM (modes M) (modes_closed M) u‖^2+nu.coeff*curlPair (modes M) u.1 u.1) := by
  let m:=NativeWindowHistoryMeanPhysicalJet.physicalJet seed M 0 t
  have native:=NativeWindowHistoryAdjointSpatialHalf.transport_bound true (modes M) (modes_zero M) (modes_closed M) nu u m
  rw [strong_square] at native
  have first:=NativeWindowHistoryAdjointSpatialHalf.moment_energy nu M u
  have last:=(NativeWindowHistoryCreationMean.mean_moment seed 0 horizon M t inside).trans (le_max_right 0 _)
  have product:=mul_le_mul first last (NativeWindowHistoryAdjointSpatialHalf.moment_nonnegative _ _ _)
    (mul_nonneg (NativeWindowHistoryAdjointSpatialHalf.energyCap_positive nu).le
      (NativeWindowHistoryHeatDual.energy_nonnegative nu M u))
  have bound:=mul_le_mul_of_nonneg_left product transportCap_nonnegative
  rw [← NativeWindowHistoryMeanResidualLoad.jet_zero_mean seed M t,NativeWindowHistoryDynamicKernel.transport_apply]
  apply native.trans
  rw [include_norm (modes M) (modes_zero M)]
  simpa only [transportCap,NativeWindowHistoryAdjointSpatialHalf.inputOrder,if_true,
    NativeWindowHistoryHeatDual.energy,normBudget,mul_assoc,mul_left_comm,mul_comm,m] using bound

theorem fiber_norm (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (M : ℕ) (t : ℝ)
    (inside : t∈Icc 0 horizon) (u : wholePhysical) :
    ‖fiber seed M t u‖^2≤normBudget seed horizon*
      (‖u‖^2+nu.coeff*curlPair (modes M)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1) := by
  rw [fiber_original]
  have source:=finite_norm seed horizon M t inside (restrictCLM (modes M) (modes_zero M) (modes_closed M) u)
  have projected:=pow_le_pow_left₀ (norm_nonneg _) (restrict_energy (modes M) (modes_zero M) (modes_closed M) u) 2
  rw [← include_norm (modes M) (modes_zero M) (modes_closed M)] at projected
  exact source.trans (mul_le_mul_of_nonneg_left (add_le_add projected (le_refl _)) (normBudget_nonnegative seed horizon))

private theorem young_work {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) (delta : ℝ) (positive : 0<delta) :
    |2*inner ℝ u v|≤delta*‖v‖^2+delta⁻¹*‖u‖^2 := by
  have paired:=abs_real_inner_le_norm u v
  have scalar : delta*(delta*‖v‖^2+delta⁻¹*‖u‖^2)=delta^2*‖v‖^2+‖u‖^2 := by field_simp
  rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  apply (mul_le_mul_of_nonneg_left paired (by norm_num : (0:ℝ)≤2)).trans
  apply le_of_mul_le_mul_left (a := delta) _ positive
  rw [scalar]
  nlinarith only [sq_nonneg (delta*‖v‖-‖u‖)]

theorem source_point (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M t,t∈Icc 0 horizon →∀u : wholePhysical,
      |2*inner ℝ u (fiber seed M t u)|≤epsilon*curlPair (modes M)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1+C*‖u‖^2 := by
  let K:=normBudget seed horizon
  have K0 : 0≤K:=normBudget_nonnegative seed horizon
  let delta:=epsilon/(K*nu.coeff+1)
  have denominator : 0<K*nu.coeff+1:=by positivity [nu.coeff_pos]
  have delta0 : 0<delta:=div_pos positive denominator
  refine ⟨delta*K+delta⁻¹,add_nonneg (mul_nonneg delta0.le K0) (inv_nonneg.mpr delta0.le),?_⟩
  intro M t inside u
  let g:=curlPair (modes M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) u).1
  have g0 : 0≤g:=by
    dsimp only [g]
    rw [← NativeDualCurlResolvent.gradient_norm_sq (modes M) (modes_zero M)]
    exact sq_nonneg _
  have source:=mul_le_mul_of_nonneg_left (fiber_norm seed horizon M t inside u) delta0.le
  have paired:=young_work u (fiber seed M t u) delta delta0
  have relative : delta*K*nu.coeff≤epsilon := by
    dsimp only [delta]
    rw [div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_iff₀ denominator]
    nlinarith only [positive.le]
  have high:=mul_le_mul_of_nonneg_right relative g0
  change delta*‖fiber seed M t u‖^2≤delta*(K*(‖u‖^2+nu.coeff*g)) at source
  change |2*inner ℝ u (fiber seed M t u)|≤epsilon*g+(delta*K+delta⁻¹)*‖u‖^2
  nlinarith only [paired,source,high]

theorem action_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (t : ℝ) (x : H) :
    action seed M t x=ᵐ[averageMeasure] fun lag => fiber seed M t (x lag) :=
  (fiber seed M t).coeFn_compLpL x

set_option backward.isDefEq.respectTransparency false in
theorem source_form (seed : GeneratedWholeRestartCurrent nu) (horizon epsilon : ℝ) (positive : 0<epsilon) :
    ∃C : ℝ,0≤C ∧∀M t,t∈Icc 0 horizon →∀x : H,
      |2*inner ℝ x (action seed M t x)|≤epsilon*gradient M x+C*‖x‖^2 := by
  obtain ⟨C,C0,paid⟩:=source_point seed horizon epsilon positive
  refine ⟨C,C0,fun M t inside x => ?_⟩
  have mass:=((Lp.memLp x).integrable_norm_pow (by norm_num : (2:ℕ)≠0)).const_mul C
  have grad:=(NativeWindowTraceWholeHistory.gradient_integrable nu M x).const_mul epsilon
  have point : ∀ᵐlag ∂averageMeasure,‖2*inner ℝ (x lag) (fiber seed M t (x lag))‖≤
      epsilon*curlPair (modes M)
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) (x lag)).1
        (restrictCLM (modes M) (modes_zero M) (modes_closed M) (x lag)).1+C*‖x lag‖^2 :=
    Eventually.of_forall fun lag => (Real.norm_eq_abs _).trans_le (paid M t inside (x lag))
  have bound:=norm_integral_le_of_norm_le (grad.add mass) point
  simp only [Pi.add_apply] at bound
  rw [integral_add grad mass] at bound
  simp only [integral_const_mul] at bound
  rw [← NativeWindowTraceWholeHistory.norm_square] at bound
  have read : inner ℝ x (action seed M t x)=
      ∫lag,inner ℝ (x lag) (fiber seed M t (x lag)) ∂averageMeasure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [action_ae seed M t x] with lag actual
    rw [actual]
  rw [read]
  exact (Real.norm_eq_abs _).symm.trans_le bound

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem action_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (t : ℝ) (nonnegative : 0≤t) :
    action seed M (step.2.clockAdvance+t)=action step.1 M t := by
  have same:=NativeWindowHistoryMeanPhysicalJet.physicalJet_next seed M 0 step generated t nonnegative
  rw [NativeWindowHistoryMeanResidualLoad.jet_zero_mean,NativeWindowHistoryMeanResidualLoad.jet_zero_mean] at same
  have acted:=congrArg (fun v : physicalSpace (modes M) =>
    NativeWindowHistoryOseen.lift M ((transport nu M).flip v)) same
  exact congrArg (fun A : wholePhysical →L[ℝ] wholePhysical => A.compLpL 2 averageMeasure) acted
end
end SaturationMonoid.NavierStokes.NativeWindowHistoryMeanStrainControl
