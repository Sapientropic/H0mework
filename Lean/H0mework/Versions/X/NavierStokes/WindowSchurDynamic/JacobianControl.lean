import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.Energy
import H0mework.Versions.X.NavierStokes.WindowSchurDynamic.JacobianForm

set_option autoImplicit false
open scoped BigOperators Topology
namespace SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianControl
open Set Filter MeasureTheory
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open NativeFiniteActionResolvent NativeCommonAdvectorAction
open NativeWholeResolvent (wholePhysical restrictCLM)
open NativePhysicalPairing (includeCLM include_norm restrict_include)
open NativeWholeH1Mixed (modes modes_zero modes_closed)
open NativeWindowHistoryOseen (H action forcingHistory rateHistory)
open NativeWindowHistoryDynamicHistory (kernelAction kernelAction_ae)
open NativeWindowHistorySchurTranspose (transposeAction)
open NativeWindowHistoryAnnihilationRows (input)
open NativeWindowHistoryAnnihilationControl (laplacianFiber laplacianAction)
open NativeWindowHistorySchurTemporalControl (energy temporalResponse)
open NativeWindowTraceWholeHistory (gradient finiteHistory)
open NativeForwardWindowPairingReadout (averageMeasure)
noncomputable section
variable {nu : Viscosity}

def correction (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  (kernelAction seed M time).comp (transposeAction seed M time)

def jacobian (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H-correction seed M time

theorem correction_ae (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (v : H) :
    correction seed M time v=ᵐ[averageMeasure] fun lag => includeCLM (modes M) (modes_closed M)
      (NativeWindowHistoryJacobianForm.response seed M (time-lag)
        (NativeWindowHistorySchurSampleControl.sample seed M time lag) (input M v lag)) := by
  filter_upwards [kernelAction_ae seed M time (transposeAction seed M time v),
    NativeWindowHistorySchurTranspose.transpose_ae seed M time v,
    NativeWindowHistorySchurSampleControl.sample_include seed M time] with lag solved transported actual
  change correction seed M time v lag=_ at solved
  rw [solved,transported,← actual,NativeWindowHistorySchurAdvectorFiber.family_original,restrict_include]
  change includeCLM (modes M) (modes_closed M) (NativeWindowHistoryFrozenInverse.physical seed M (time-lag)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M)
      (includeCLM (modes M) (modes_closed M) _)))=_
  rw [restrict_include]
  rfl

def density (nu : Viscosity) (M : ℕ) (v : wholePhysical) : ℝ :=
  ‖v‖^2+nu.coeff*curlPair (modes M)
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1
    (restrictCLM (modes M) (modes_zero M) (modes_closed M) v).1

theorem density_integrable (nu : Viscosity) (M : ℕ) (v : H) :
    Integrable (fun lag => density nu M (v lag)) averageMeasure :=
  ((Lp.memLp v).integrable_norm_pow (by decide : (2 : ℕ)≠0)).add
    ((NativeWindowTraceWholeHistory.gradient_integrable nu M v).const_mul nu.coeff)

theorem density_integral (nu : Viscosity) (M : ℕ) (v : H) :
    (∫lag,density nu M (v lag) ∂averageMeasure)=energy nu M v := by
  have source:=integral_add ((Lp.memLp v).integrable_norm_pow (by decide : (2 : ℕ)≠0))
    ((NativeWindowTraceWholeHistory.gradient_integrable nu M v).const_mul nu.coeff)
  exact source.trans (congrArg₂ (fun a b : ℝ => a+b) (NativeWindowTraceWholeHistory.norm_square v).symm
    (integral_const_mul nu.coeff (fun lag => curlPair (modes M) (input M v lag).1 (input M v lag).1)))

theorem density_include (nu : Viscosity) (M : ℕ) (v : physicalSpace (modes M)) :
    density nu M (includeCLM (modes M) (modes_closed M) v)=NativeWindowHistoryHeatDual.energy nu M v := by
  rw [density,include_norm (modes M) (modes_zero M),restrict_include]
  rfl

theorem density_restrict (nu : Viscosity) (M : ℕ) (v : wholePhysical) :
    NativeWindowHistoryHeatDual.energy nu M (restrictCLM (modes M) (modes_zero M) (modes_closed M) v)≤density nu M v := by
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) (NativeWindowMetricGraphHistory.restricted_norm M v) 2) le_rfl

theorem source_correction_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,∀ v : H,
      energy nu M (correction seed M time v)≤epsilon*energy nu M v+C*‖v‖^2 := by
  obtain ⟨low,C,C0,source⟩:=NativeWindowHistoryJacobianForm.source_point_bound seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun M above time inside v => ?_⟩
  have point:∀ᵐ lag ∂averageMeasure,density nu M (correction seed M time v lag)≤
      epsilon*density nu M (v lag)+C*‖v lag‖^2 := by
    filter_upwards [correction_ae seed M time v,source M above time inside] with lag read bound
    rw [read,density_include]
    exact (bound (input M v lag)).trans (add_le_add
      (mul_le_mul_of_nonneg_left (density_restrict nu M (v lag)) positive.le)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (NativeWindowMetricGraphHistory.restricted_norm M (v lag)) 2) C0))
  have massPaid:=(Lp.memLp v).integrable_norm_pow (by decide : (2 : ℕ)≠0)
  have integrated:=integral_mono_ae (density_integrable nu M (correction seed M time v))
    (((density_integrable nu M v).const_mul epsilon).add (massPaid.const_mul C)) point
  have first:=(integral_const_mul epsilon (fun lag => density nu M (v lag))).trans
    (congrArg (epsilon*·) (density_integral nu M v))
  have last:=(integral_const_mul C (fun lag => ‖v lag‖^2)).trans
    (congrArg (C*·) (NativeWindowTraceWholeHistory.norm_square v).symm)
  have sumRead:=(integral_add ((density_integrable nu M v).const_mul epsilon) (massPaid.const_mul C)).trans
    (congrArg₂ (fun a b : ℝ => a+b) first last)
  exact (density_integral nu M (correction seed M time v)).symm.trans_le (integrated.trans_eq sumRead)

def heat (nu : Viscosity) (M : ℕ) : H →L[ℝ] H := ContinuousLinearMap.id ℝ H+nu.coeff • laplacianAction nu M

def form (nu : Viscosity) (M : ℕ) (v w : H) : ℝ := inner ℝ v (heat nu M w)

private theorem linear_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v l : E) (a : ℝ) : inner ℝ u (v+a • l)=inner ℝ u v+a*inner ℝ u l := by
  rw [inner_add_right,real_inner_smul_right]

theorem form_split (nu : Viscosity) (M : ℕ) (v w : H) :
    form nu M v w=inner ℝ v w+nu.coeff*inner ℝ v (laplacianAction nu M w) :=
  linear_pair (E := H) v w (laplacianAction nu M w) nu.coeff

theorem form_self (nu : Viscosity) (M : ℕ) (v : H) : form nu M v v=energy nu M v := by
  exact (form_split nu M v v).trans (congrArg₂ (fun a b : ℝ => a+nu.coeff*b)
    (real_inner_self_eq_norm_sq v) (NativeWindowMetricGraphHistory.history_gradient nu M v))

theorem form_symmetric (nu : Viscosity) (M : ℕ) (v w : H) : form nu M v w=form nu M w v := by
  have lap:inner ℝ v (laplacianAction nu M w)=inner ℝ w (laplacianAction nu M v) := by
    rw [L2.inner_def,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(laplacianFiber nu M).coeFn_compLpL w,(laplacianFiber nu M).coeFn_compLpL v] with lag first last
    change inner ℝ (v lag) (((laplacianFiber nu M).compLpL 2 averageMeasure w) lag)=
      inner ℝ (w lag) (((laplacianFiber nu M).compLpL 2 averageMeasure v) lag)
    rw [first,last,← NativeWindowHistoryDynamicTest.laplacian_symmetric,real_inner_comm]
  exact (form_split nu M v w).trans ((congrArg₂ (fun a b : ℝ => a+nu.coeff*b)
    (real_inner_comm w v) lap).trans (form_split nu M w v).symm)

private theorem positive_young {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (L : E →L[ℝ] E) (positive : ∀ x,0 ≤ inner ℝ x (L x))
    (symmetric : ∀ x y,inner ℝ x (L y)=inner ℝ y (L x)) (v w : E) (a : ℝ) :
    2*a*inner ℝ v (L w)≤a^2*inner ℝ v (L v)+inner ℝ w (L w) := by
  have source:=positive (a • v-w)
  simp only [map_sub,map_smul,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right] at source
  rw [symmetric w v] at source
  nlinarith only [source]

theorem form_young (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (v w : H) (a : ℝ) :
    2*a*form nu M v w≤a^2*energy nu M v+energy nu M w := by
  have source:=positive_young (E := H) (heat nu M)
    (fun x => (NativeWindowHistorySchurTemporalControl.energy_nonnegative seed M x).trans_eq (form_self nu M x).symm)
    (form_symmetric nu M) v w a
  change 2*a*form nu M v w≤a^2*form nu M v v+form nu M w w at source
  exact source.trans_eq (congrArg₂ (fun x y : ℝ => a^2*x+y) (form_self nu M v) (form_self nu M w))

private theorem scalar_absorption (e y z m C epsilon : ℝ) (positive : 0<epsilon)
    (first : 2*epsilon*z≤epsilon^2*e+y) (last : 2*(-epsilon)*z≤(-epsilon)^2*e+y)
    (bound : y≤epsilon^2*e+C*m) : |z|≤epsilon*e+(C/(2*epsilon))*m := by
  have cancel:2*epsilon*(C/(2*epsilon))=C:=mul_div_cancel₀ _ (by positivity)
  have scaled:2*epsilon*(epsilon*e+(C/(2*epsilon))*m)=2*epsilon^2*e+C*m := by
    calc
      _=2*epsilon^2*e+(2*epsilon*(C/(2*epsilon)))*m := by ring
      _=_ := by rw [cancel]
  apply abs_le.mpr
  constructor
  · apply (mul_le_mul_iff_right₀ (show 0<2*epsilon by positivity)).mp
    rw [mul_neg,scaled]
    nlinarith only [last,bound]
  · apply (mul_le_mul_iff_right₀ (show 0<2*epsilon by positivity)).mp
    rw [scaled]
    nlinarith only [first,bound]

theorem source_form_bound (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,∀ v : H,
      |form nu M v (correction seed M time v)|≤epsilon*energy nu M v+C*‖v‖^2 := by
  obtain ⟨low,C,C0,source⟩:=source_correction_bound seed horizon nonnegative (epsilon^2) (sq_pos_of_pos positive)
  refine ⟨low,C/(2*epsilon),div_nonneg C0 (by positivity),fun M above time inside v => ?_⟩
  have first:=form_young seed M v (correction seed M time v) epsilon
  have last:=form_young seed M v (correction seed M time v) (-epsilon)
  have bounded:=source M above time inside v
  exact scalar_absorption _ _ _ _ C epsilon positive first last bounded

theorem source_coercivity (seed : GeneratedWholeRestartCurrent nu) (horizon : ℝ) (nonnegative : 0≤horizon)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ low : ℕ,∃ C : ℝ,0≤C ∧∀ M≥low,∀ time∈Icc 0 horizon,∀ v : H,
      (1-epsilon)*energy nu M v-C*‖v‖^2≤form nu M v (jacobian seed M time v) := by
  obtain ⟨low,C,C0,source⟩:=source_form_bound seed horizon nonnegative epsilon positive
  refine ⟨low,C,C0,fun M above time inside v => ?_⟩
  have identity:form nu M v (jacobian seed M time v)=energy nu M v-form nu M v (correction seed M time v) := by
    change inner ℝ v (heat nu M (v-correction seed M time v))=_
    rw [map_sub,inner_sub_right (𝕜 := ℝ) (E := H)]
    exact congrArg (fun x => x-form nu M v (correction seed M time v)) (form_self nu M v)
  have paid:=(le_abs_self _).trans (source M above time inside v)
  rw [identity]
  linarith only [paid]

def skewWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (q v : H) : ℝ :=
  form nu M v (correction seed M time q)-form nu M q (correction seed M time v)

private theorem mixed_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (L R : E →L[ℝ] E) (symmetric : ∀ x y,inner ℝ x (L y)=inner ℝ y (L x)) (q v : E) :
    2*inner ℝ q ((ContinuousLinearMap.id ℝ E-R).adjoint (L v))=
      2*inner ℝ q (L (v-R v))-2*(inner ℝ v (L (R q))-inner ℝ q (L (R v))) := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  simp only [sub_apply,ContinuousLinearMap.id_apply,map_sub,inner_sub_left,inner_sub_right]
  rw [symmetric (R q) v]
  ring

theorem mixed_identity (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) (q v : H) :
    2*inner ℝ q (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (jacobian seed M time) (heat nu M v))=
      2*form nu M q (jacobian seed M time v)-2*skewWork seed M time q v := by
  simpa only [jacobian,skewWork,form,sub_apply,ContinuousLinearMap.id_apply] using!
    mixed_pair (E := H) (heat nu M) (correction seed M time) (form_symmetric nu M) q v

def sourceSkewWork (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) : ℝ :=
  skewWork seed M time (action seed M time (finiteHistory seed time M)+forcingHistory seed M time)
    (temporalResponse seed M time)

theorem source_mixed_identity (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    2*inner ℝ (rateHistory seed M time)
      (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (jacobian seed M time) (heat nu M (temporalResponse seed M time)))=
        2*form nu M (rateHistory seed M time) (jacobian seed M time (temporalResponse seed M time))-
          2*sourceSkewWork seed M time := by
  rw [mixed_identity]
  exact congrArg (fun x => 2*form nu M (rateHistory seed M time)
    (jacobian seed M time (temporalResponse seed M time))-2*x)
      (congrArg (fun q => skewWork seed M time q (temporalResponse seed M time))
        (NativeWindowHistoryOseen.source_equation seed M time))

private theorem adjoint_difference {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (K T : E →L[ℝ] E) (q : E) :
    (ContinuousLinearMap.id ℝ E-K.comp T).adjoint q=q-T.adjoint (K.adjoint q) := by
  apply ext_inner_left ℝ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right,inner_sub_right,
    ContinuousLinearMap.adjoint_inner_right,ContinuousLinearMap.adjoint_inner_right]
  simp only [sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,inner_sub_left]

theorem source_test (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (jacobian seed M time)
      (heat nu M (temporalResponse seed M time))=
        NativeWindowHistoryDynamicEnergy.test seed M time (temporalResponse seed M time) := by
  have principal:heat nu M (temporalResponse seed M time)=
      NativeWindowHistoryDynamicEnergy.principal nu M (temporalResponse seed M time) :=
    congrArg (fun v : H => v+nu.coeff • laplacianAction nu M (temporalResponse seed M time))
      (NativeWindowHistoryDynamicEnergy.residual_projected seed M time).symm
  have actual:=adjoint_difference (E := H) (kernelAction seed M time) (transposeAction seed M time)
    (NativeWindowHistoryDynamicEnergy.principal nu M (temporalResponse seed M time))
  apply (congrArg (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := H) (jacobian seed M time)) principal).trans
  simpa only [jacobian,correction] using! actual

theorem dynamic_joint_work (seed : GeneratedWholeRestartCurrent nu) (M : ℕ) (time : ℝ) :
    NativeWindowHistoryDynamicEnergy.jointWork seed M time=
      2*form nu M (rateHistory seed M time) (jacobian seed M time (temporalResponse seed M time))-
        2*sourceSkewWork seed M time := by
  have read:=congrArg (fun v : H => 2*inner ℝ (rateHistory seed M time) v) (source_test seed M time)
  exact read.symm.trans (source_mixed_identity seed M time)

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointRecursiveMacroRuntime

theorem jacobian_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    jacobian seed M (step.2.clockAdvance+time)=jacobian step.1 M time := by
  exact congrArg (fun T : H →L[ℝ] H => ContinuousLinearMap.id ℝ H-T)
    (congrArg₂ (fun K T : H →L[ℝ] H => K.comp T)
      (NativeWindowHistoryDynamicHistory.kernelAction_next seed M step generated time time0)
      (NativeWindowHistorySchurTranspose.transpose_next seed M step generated time time0))

theorem sourceSkewWork_next (seed : GeneratedWholeRestartCurrent nu) (M : ℕ)
    (step : Response (GeneratedWholeRestartEndpointMacroStep nu) seed)
    (generated : generatedWholeRestartEndpointMacroRespond seed=some step) (time : ℝ) (time0 : 0≤time) :
    sourceSkewWork seed M (step.2.clockAdvance+time)=sourceSkewWork step.1 M time := by
  have read (s : GeneratedWholeRestartCurrent nu) (t : ℝ) :
      sourceSkewWork s M t=skewWork s M t (rateHistory s M t) (temporalResponse s M t) :=
    congrArg (fun q => skewWork s M t q (temporalResponse s M t)) (NativeWindowHistoryOseen.source_equation s M t).symm
  have op:=congrArg₂ (fun K T : H →L[ℝ] H => K.comp T)
    (NativeWindowHistoryDynamicHistory.kernelAction_next seed M step generated time time0)
    (NativeWindowHistorySchurTranspose.transpose_next seed M step generated time time0)
  have pair:=congrArg₂ (fun q v : H => (q,v)) (NativeWindowHistoryOseen.rateHistory_next seed M step generated time time0)
    (NativeWindowHistorySchurTemporalControl.temporal_next seed M step generated time time0)
  exact (read seed _).trans ((congrArg₂ (fun (R : H →L[ℝ] H) (p : H×H) =>
    form nu M p.2 (R p.1)-form nu M p.1 (R p.2)) op pair).trans (read step.1 time).symm)

end
end SaturationMonoid.NavierStokes.NativeWindowHistoryJacobianControl
