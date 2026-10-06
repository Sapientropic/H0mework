import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceNeumannDomain

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumMixedControl
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open CanonicalGradedSpatialSource PreparationVacuumPhysicalFeedback PreparationVacuumElectromagneticIdentity
open Filter
open scoped Matrix BigOperators Topology Matrix.Norms.Operator
attribute [local irreducible] activeKernel kernelFrame effectiveKernel complementGreen

def readerBudget : ℝ:=(termsPrice (reflectedTerms kernelTerms):ℝ)
def residualBudget : ℝ:=(termsPrice quadraticTerms:ℝ)+(termsPrice cubicTerms:ℝ)
def effectiveErrorBudget : ℝ:=2*readerBudget*variationBudget*inverseBudget*residualBudget

theorem readerBudget_nonneg : 0 ≤ readerBudget:=by unfold readerBudget;exact_mod_cast termsPrice_nonneg (reflectedTerms kernelTerms)
theorem residualBudget_nonneg : 0 ≤ residualBudget:=by
  unfold residualBudget
  exact add_nonneg (by exact_mod_cast termsPrice_nonneg quadraticTerms) (by exact_mod_cast termsPrice_nonneg cubicTerms)
theorem effectiveErrorBudget_nonneg : 0 ≤ effectiveErrorBudget:=by
  have a:=readerBudget_nonneg
  have b:=variationBudget_ge_one
  have c:=inverseBudget_ge_one
  have d:=residualBudget_nonneg
  unfold effectiveErrorBudget
  positivity

private theorem reflected_origin_zero (p : Fin 4→ℂ) : reflectedKernelFrame p*activeKernel 0=0 :=by
  have h:=congrArg Matrix.transpose sourceKernel_generated
  have symmetric : (activeKernel 0).transpose=activeKernel 0:=by
    simpa only [neg_zero] using activeKernel_reflect (0:Fin 4→ℂ)
  rw [Matrix.transpose_mul,Matrix.transpose_zero,symmetric] at h
  have constant : reflectedKernelFrame p=(kernelFrame 0).transpose:=by
    rw [kernel_reflected]
    congr 1
    unfold kernelFrame
    have constantTerms : originTerms kernelTerms=kernelTerms:=by decide +kernel
    simpa only [constantTerms] using sourceMatrix_origin_constant kernelTerms (-p)
  rw [constant]
  exact h

private theorem reflected_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (bound : ∀i,‖p i‖ ≤ r) :
    ‖reflectedKernelFrame p‖ ≤ readerBudget :=by
  have checked : (reflectedTerms kernelTerms).all (fun a=>decide (a.powers.total=0))=true:=by decide +kernel
  have homogeneous : ∀a∈reflectedTerms kernelTerms,a.powers.total=0:=by
    intro a ha
    exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  simpa only [pow_zero,mul_one,reflectedKernelFrame,readerBudget] using
    sourceMatrix_homogeneous_price (reflectedTerms kernelTerms) 0 homogeneous p r nonneg bound

private theorem residual_price (p : Fin 4→ℂ) (r : ℝ) (nonneg : 0 ≤ r) (small : r ≤ 1) (bound : ∀i,‖p i‖ ≤ r) :
    ‖sourceMatrix quadraticTerms p+sourceMatrix cubicTerms p‖ ≤ residualBudget*r^2 :=by
  have two : ∀a∈quadraticTerms,a.powers.total=2:=by intro a ha;exact of_decide_eq_true (List.mem_filter.mp ha).2
  have three : ∀a∈cubicTerms,a.powers.total=3:=by intro a ha;exact of_decide_eq_true (List.mem_filter.mp ha).2
  have power : r^3 ≤ r^2:=by nlinarith [mul_nonneg (sub_nonneg.mpr small) (sq_nonneg r)]
  have thirdNonneg : (0:ℝ) ≤ (termsPrice cubicTerms:ℝ):=by exact_mod_cast termsPrice_nonneg cubicTerms
  calc
    _ ≤ ‖sourceMatrix quadraticTerms p‖+‖sourceMatrix cubicTerms p‖:=norm_add_le _ _
    _ ≤ (termsPrice quadraticTerms:ℝ)*r^2+(termsPrice cubicTerms:ℝ)*r^3:=
      add_le_add (sourceMatrix_homogeneous_price quadraticTerms 2 two p r nonneg bound)
        (sourceMatrix_homogeneous_price cubicTerms 3 three p r nonneg bound)
    _ ≤ (termsPrice quadraticTerms:ℝ)*r^2+(termsPrice cubicTerms:ℝ)*r^2:=by gcongr
    _=residualBudget*r^2:=by unfold residualBudget;ring

theorem effective_principal_price (time space : ℂ) (r : ℝ) (nonneg : 0 ≤ r) (cap : r ≤ sourceRadius)
    (bound : ∀i,‖planeMomentum time space i‖ ≤ r) :
    ‖effectiveKernel (controlledPoint (planeMomentum time space) (fun i=>(bound i).trans cap))-sourcePrincipal time space‖ ≤
      effectiveErrorBudget*r^3 :=by
  let point:=controlledPoint (planeMomentum time space) (fun i=>(bound i).trans cap)
  have exactReturn:=effectiveKernel_principal_return time space point.property
  have difference : effectiveKernel point-sourcePrincipal time space=
      -(reflectedKernelFrame (planeMomentum time space)*(activeKernel (planeMomentum time space)-activeKernel 0)*
        complementGreen point*(sourceMatrix quadraticTerms (planeMomentum time space)+sourceMatrix cubicTerms (planeMomentum time space))) :=by
    dsimp only [point,controlledPoint]
    rw [exactReturn]
    rw [mul_sub,reflected_origin_zero,sub_zero]
    abel
  change ‖effectiveKernel point-sourcePrincipal time space‖ ≤ _
  rw [difference,norm_neg]
  have b:=readerBudget_nonneg
  have k:=variationBudget_ge_one
  have c:=inverseBudget_ge_one
  have d:=residualBudget_nonneg
  calc
    _ ≤ ((‖reflectedKernelFrame (planeMomentum time space)‖*
        ‖activeKernel (planeMomentum time space)-activeKernel 0‖)*‖complementGreen point‖)*
        ‖sourceMatrix quadraticTerms (planeMomentum time space)+sourceMatrix cubicTerms (planeMomentum time space)‖:=by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))) (norm_nonneg _))
    _ ≤ ((readerBudget*(variationBudget*r))*(2*inverseBudget))*(residualBudget*r^2):=by
      gcongr
      · exact reflected_price _ r nonneg bound
      · exact activeKernel_delta_price _ r nonneg (cap.trans sourceRadius_le_one) bound
      · exact complementGreen_price _ _
      · exact residual_price _ r nonneg (cap.trans sourceRadius_le_one) bound
    _=effectiveErrorBudget*r^3:=by unfold effectiveErrorBudget;ring

private theorem plane_scaled (time space scale : ℂ) :
    planeMomentum (scale*time) (scale*space)=scale • planeMomentum time space :=by
  ext i
  fin_cases i <;> simp [planeMomentum]

theorem principal_scaled (time space scale : ℂ) : sourcePrincipal (scale*time) (scale*space)=scale^2 • sourcePrincipal time space :=by
  have checked : principalTerms.all (fun a=>decide (a.powers.total=2))=true:=by decide +kernel
  have homogeneous : ∀a∈principalTerms,a.powers.total=2:=by intro a ha;exact of_decide_eq_true (List.all_eq_true.mp checked a ha)
  rw [sourcePrincipal,plane_scaled,sourceMatrix_homogeneous principalTerms 2 homogeneous]
  rfl

def raySize (time space : ℂ) : ℝ:=1+‖time‖+‖space‖
theorem raySize_positive (time space : ℂ) : 0<raySize time space :=by unfold raySize;positivity

def SourceRay (time space : ℂ):= {scale : ℂ // ‖scale‖*raySize time space ≤ sourceRadius}

private theorem ray_bound (time space scale : ℂ) :
    ∀i,‖planeMomentum (scale*time) (scale*space) i‖ ≤ ‖scale‖*raySize time space :=by
  intro i
  fin_cases i
  · change ‖scale*time‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold raySize;nlinarith [norm_nonneg space]
  · change ‖scale*space‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    unfold raySize;nlinarith [norm_nonneg time]
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    exact mul_nonneg (norm_nonneg _) (le_of_lt (raySize_positive time space))
  · change ‖(0:ℂ)‖ ≤ _
    rw [norm_zero]
    exact mul_nonneg (norm_nonneg _) (le_of_lt (raySize_positive time space))

def sourceRayPoint (time space : ℂ) (scale : SourceRay time space) : complementRegular:=
  controlledPoint (planeMomentum (scale.val*time) (scale.val*space))
    (fun i=>(ray_bound time space scale.val i).trans scale.property)

def normalizedEffective (time space : ℂ) (scale : SourceRay time space) : Matrix (Fin 289) (Fin 289) ℂ:=
  (scale.val^2)⁻¹ • effectiveKernel (sourceRayPoint time space scale)

theorem normalizedEffective_price (time space : ℂ) (scale : SourceRay time space) (nonzero : scale.val≠0) :
    ‖normalizedEffective time space scale-sourcePrincipal time space‖ ≤
      effectiveErrorBudget*(raySize time space)^3*‖scale.val‖ :=by
  have size:=raySize_positive time space
  have actual:=effective_principal_price (scale.val*time) (scale.val*space) (‖scale.val‖*raySize time space)
    (by positivity) scale.property (ray_bound time space scale.val)
  have difference : normalizedEffective time space scale-sourcePrincipal time space=
      (scale.val^2)⁻¹ • (effectiveKernel (sourceRayPoint time space scale)-sourcePrincipal (scale.val*time) (scale.val*space)) :=by
    rw [principal_scaled,smul_sub,smul_smul,inv_mul_cancel₀ (pow_ne_zero 2 nonzero),one_smul]
    rfl
  rw [difference,norm_smul,norm_inv,norm_pow]
  calc
    _ ≤ (‖scale.val‖^2)⁻¹*(effectiveErrorBudget*(‖scale.val‖*raySize time space)^3):=
      mul_le_mul_of_nonneg_left actual (inv_nonneg.mpr (sq_nonneg _))
    _= _ :=by
      have positive : ‖scale.val‖≠0:=norm_ne_zero_iff.mpr nonzero
      field_simp

theorem sourceRay_near (time space : ℂ) : ∀ᶠ scale in 𝓝 (0:ℂ),‖scale‖*raySize time space ≤ sourceRadius :=by
  have positive:=sourceRadius_pos
  have c : Continuous (fun scale : ℂ=>‖scale‖*raySize time space):=by fun_prop
  have h:=c.continuousAt.eventually_lt_const (show ‖(0:ℂ)‖*raySize time space<sourceRadius by simpa using positive)
  exact h.mono (fun _ h=>h.le)

theorem sourceRay_filter_nonempty (time space : ℂ) :
    (Filter.comap (Subtype.val : SourceRay time space→ℂ) (𝓝[≠] (0:ℂ))).NeBot :=by
  apply Filter.NeBot.comap_of_range_mem (inferInstance : (𝓝[≠] (0:ℂ)).NeBot)
  filter_upwards [(sourceRay_near time space).filter_mono nhdsWithin_le_nhds] with scale h
  exact ⟨⟨scale,h⟩,rfl⟩

/-- Complete Schur dynamics, including its complement, has the generated principal as its actual second-order limit. -/
theorem normalizedEffective_generated (time space : ℂ) :
    Tendsto (normalizedEffective time space) (Filter.comap Subtype.val (𝓝[≠] (0:ℂ))) (𝓝 (sourcePrincipal time space)) :=by
  have source : Tendsto (Subtype.val : SourceRay time space→ℂ)
      (Filter.comap Subtype.val (𝓝[≠] (0:ℂ))) (𝓝[≠] (0:ℂ)):=tendsto_comap
  have atZero:=source.mono_right nhdsWithin_le_nhds
  have off : ∀ᶠ scale in 𝓝[≠] (0:ℂ),scale≠0:=by
    filter_upwards [self_mem_nhdsWithin] with scale h
    exact h
  have upper : Tendsto (fun scale : SourceRay time space=>effectiveErrorBudget*(raySize time space)^3*‖scale.val‖)
      (Filter.comap Subtype.val (𝓝[≠] (0:ℂ))) (𝓝 (0:ℝ)):=by
    simpa only [norm_zero,mul_zero,SourceRay] using tendsto_const_nhds.mul atZero.norm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _=>norm_nonneg _)) _ upper
  exact (source.eventually off).mono (fun scale h=>normalizedEffective_price time space scale h)

/-- The actual current equation consumes the complete Schur price, retaining the generated field and co-source. -/
theorem actual_effective_response_price (q : PhysicalResponsePoint) (p : PhysicalMomentum) (momentum : ℝ)
    (left right : RestStateIndex) (time : ℂ) (T r : ℝ) (nonneg : 0 ≤ r) (cap : r ≤ sourceRadius)
    (bound : ∀i,‖planeMomentum time (Complex.I*(momentum:ℂ)) i‖ ≤ r) :
    ‖sourcePrincipal time (Complex.I*(momentum:ℂ))*ᵥ
        blockCoordinates (actualBlockField q p momentum left right time T)-
      effectiveReader (controlledPoint (planeMomentum time (Complex.I*(momentum:ℂ))) (fun i=>(bound i).trans cap))*ᵥ
        actualBlockForcing q p momentum left right time T‖ ≤
      effectiveErrorBudget*r^3*‖blockCoordinates (actualBlockField q p momentum left right time T)‖ :=by
  let point:=controlledPoint (planeMomentum time (Complex.I*(momentum:ℂ))) (fun i=>(bound i).trans cap)
  have actual:=actual_effective_dynamics q p momentum left right time T point.property
  have price:=effective_principal_price time (Complex.I*(momentum:ℂ)) r nonneg cap bound
  dsimp only [controlledPoint] at price ⊢
  rw [←actual,←Matrix.sub_mulVec]
  exact (Matrix.linfty_opNorm_mulVec _ _).trans
    (mul_le_mul_of_nonneg_right (by simpa only [norm_sub_rev] using price) (norm_nonneg _))

theorem readerPrice_exact : termsPrice (reflectedTerms kernelTerms)=(32/5:ℚ) :=by decide +kernel
theorem residualPrices_exact :
    (termsPrice quadraticTerms,termsPrice cubicTerms)=((9067497/184250:ℚ),(1997611/54270:ℚ)) :=by decide +kernel

theorem effectiveErrorBudget_exact : effectiveErrorBudget=
    2*(32/5:ℝ)*(1359767/375)*(94372417/751740)*(9067497/184250+1997611/54270) :=by
  have quadratic:=congrArg Prod.fst residualPrices_exact
  have cubic:=congrArg Prod.snd residualPrices_exact
  dsimp only at quadratic cubic
  rw [effectiveErrorBudget,readerBudget,residualBudget,inverseBudget,variationBudget,
    readerPrice_exact,inversePrice_exact,variationPrice_exact,quadratic,cubic]
  norm_num

end LowEnergy.PreparationVacuumMixedControl
