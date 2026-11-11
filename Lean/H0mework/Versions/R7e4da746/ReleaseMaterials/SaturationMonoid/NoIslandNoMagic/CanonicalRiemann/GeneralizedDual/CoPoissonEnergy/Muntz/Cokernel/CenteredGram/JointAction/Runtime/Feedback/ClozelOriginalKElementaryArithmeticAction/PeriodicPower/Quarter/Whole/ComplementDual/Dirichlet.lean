import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Dirichlet
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.Inverse.ReturnMellin
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open scoped Topology ENNReal InnerProductSpace
open private weightedRawTerm raw_sum from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.LogCounting.Source
local notation "q" => (1/4:ℝ)
local notation "μplus" => volume.restrict (Ioi (0:ℝ))

private theorem compact_power_mellin (w z:ℂ) (above:w.re<z.re):
    HasMellin (compactRaw (powerRaw w)) z ((q:ℂ)^(z-star w)/(z-star w)):=by
  let a:ℂ:=z-star w-1
  have exponent:-1<a.re:=by dsimp only [a];simp only [sub_re,star_def,conj_re,one_re];linarith
  have ordinary:IntervalIntegrable (fun x:ℝ=>(x:ℂ)^a) volume 0 q:=
    intervalIntegral.intervalIntegrable_cpow' exponent
  have field:EqOn (fun x:ℝ=>(x:ℂ)^(z-1)*compactRaw (powerRaw w) x)
      ((Ioc (0:ℝ) q).indicator (fun x:ℝ=>(x:ℂ)^a)) (Ioi 0):=by
    intro x positive
    change 0<x at positive
    dsimp only
    by_cases below:x≤q
    · rw [compactRaw,indicator_of_mem (show x∈symmetricInterval q from ⟨by linarith,below⟩),
        indicator_of_mem (show x∈Ioc (0:ℝ) q from ⟨positive,below⟩),powerRaw,abs_of_pos positive,
        ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr positive.ne')]
      congr 1
      dsimp only [a]
      ring
    · rw [compactRaw,indicator_of_notMem (show x∉symmetricInterval q from fun hx=>below hx.2),
        mul_zero,indicator_of_notMem (show x∉Ioc (0:ℝ) q from fun hx=>below hx.2)]
  have domain:MellinConvergent (compactRaw (powerRaw w)) z:=by
    change IntegrableOn (fun x:ℝ=>(x:ℂ)^(z-1)*compactRaw (powerRaw w) x) (Ioi 0)
    have global:Integrable ((Ioc (0:ℝ) q).indicator (fun x:ℝ=>(x:ℂ)^a)):=
      (integrable_indicator_iff measurableSet_Ioc).mpr ordinary.1
    apply global.integrableOn.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x positive
    exact (field positive).symm
  refine ⟨domain,?_⟩
  simp only [mellin,smul_eq_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi field,integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,inter_eq_left.mpr Ioc_subset_Ioi_self,
    ←intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤q),integral_cpow (Or.inl exponent)]
  have nonzero:z-star w≠0:=by
    intro equal
    have real:=congrArg Complex.re equal
    simp only [sub_re,star_def,conj_re,zero_re] at real
    linarith
  rw [show a+1=z-star w by dsimp [a];ring,Complex.ofReal_zero,Complex.zero_cpow nonzero,sub_zero]

/-- The same L¹ dual has its actual seed pole and smooth correction as one Mellin source. -/
theorem actual_dual_mellin_source (w:ℂ) (below:w.re<1) (z:ℂ)
    (positive:0<z.re) (above:w.re<z.re):
    HasMellin (compactRaw (dualRaw w below)) z
      ((1/2:ℂ)*(q:ℂ)^(z-star w)/(z-star w)+mellin (compactRaw (smoothRaw w below)) z):=by
  have power:=compact_power_mellin w z above
  have regular:=actual_compact_mellin _ (actual_smooth_contDiff w below).continuous z positive
  have split:compactRaw (dualRaw w below)=
      fun x:ℝ=>(1/2:ℂ)*compactRaw (powerRaw w) x+compactRaw (smoothRaw w below) x:=by
    funext x
    by_cases inside:x∈symmetricInterval q
    · simp only [compactRaw,indicator_of_mem inside,dualRaw,seedRaw,smoothRaw]
      ring
    · simp only [compactRaw,indicator_of_notMem inside,mul_zero,add_zero]
  rw [split]
  have source:=hasMellin_add (power.1.const_smul (1/2:ℂ)) regular
  rw [mellin_const_smul,power.2] at source
  simpa only [smul_eq_mul,mul_div_assoc] using source

private def countedTerm (w:ℂ) (below:w.re<1) (n:ℕ) (x:ℝ):ℂ:=
  compactRaw (dualRaw w below) ((n+1:ℕ)*x)

private def priceTerm (w:ℂ) (below:w.re<1) (z:ℂ) (n:ℕ) (x:ℝ):ℂ:=
  (x:ℂ)^(z-1)*countedTerm w below n x

private theorem floor_tsum (w:ℂ) (below:w.re<1) (x:ℝ) (nonzero:x≠0):
    (∑'n:ℕ,countedTerm w below n x)=floorRaw w below x:=by
  have weighted:((|x|:ℝ):ℂ)*(∑'n:ℕ,countedTerm w below n x)=
      ((|x|:ℝ):ℂ)*floorRaw w below x:=by
    simpa only [weightedRawTerm,countedTerm,compactRaw,arithmeticRaw,floorRaw,tsum_mul_left]
      using raw_sum (dualRaw w below) x
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr nonzero)) weighted

private theorem term_integrable (w:ℂ) (below:w.re<1) (z:ℂ) (large:1<z.re) (n:ℕ):
    Integrable (priceTerm w below z n) μplus:=by
  have source:=(actual_dual_mellin_source w below z (by linarith) (by linarith)).1
  have positive:(0:ℝ)<(n+1:ℕ):=by positivity
  exact (MellinConvergent.comp_mul_left positive).mpr source

private theorem term_scaled (w:ℂ) (below:w.re<1) (z:ℂ) (n:ℕ) (x:ℝ) (positive:0<x):
    priceTerm w below z n x=
      (((n+1:ℕ):ℂ)^(1-z))*
        ((((n+1:ℕ)*x:ℝ):ℂ)^(z-1)*compactRaw (dualRaw w below) ((n+1:ℕ)*x)):=by
  have np:(0:ℝ)<(n+1:ℕ):=by positivity
  have nz:(((n+1:ℕ):ℂ)^(z-1))≠0:=by
    rw [Ne,Complex.cpow_eq_zero_iff,not_and_or]
    exact Or.inl (by exact_mod_cast (Nat.succ_ne_zero n))
  simp only [priceTerm,countedTerm,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg np.le positive.le]
  simp only [Complex.ofReal_natCast]
  rw [show 1-z= -(z-1) by ring,Complex.cpow_neg]
  field_simp

private theorem term_norm_integral (w:ℂ) (below:w.re<1) (z:ℂ) (n:ℕ):
    (∫x:ℝ,‖priceTerm w below z n x‖ ∂μplus)=
      ((n+1:ℕ):ℝ)^(-z.re)*
        ∫x:ℝ,‖(x:ℂ)^(z-1)*compactRaw (dualRaw w below) x‖ ∂μplus:=by
  let N:ℝ:=(n+1:ℕ)
  have positive:0<N:=by dsimp [N];positivity
  have field:EqOn (fun x:ℝ=>‖priceTerm w below z n x‖)
      (fun x:ℝ=>‖(N:ℂ)^(1-z)‖*
        ‖((N*x:ℝ):ℂ)^(z-1)*compactRaw (dualRaw w below) (N*x)‖) (Ioi 0):=by
    intro x hx
    dsimp only
    rw [term_scaled w below z n x hx,norm_mul]
    simp only [N,Complex.ofReal_natCast]
  rw [setIntegral_congr_fun measurableSet_Ioi field,integral_const_mul,
    integral_comp_mul_left_Ioi (fun x:ℝ=>‖(x:ℂ)^(z-1)*compactRaw (dualRaw w below) x‖) 0 positive,
    mul_zero,smul_eq_mul,←mul_assoc,Complex.norm_cpow_eq_rpow_re_of_pos positive]
  simp only [sub_re,one_re]
  rw [←Real.rpow_neg_one,←Real.rpow_add positive]
  congr 1
  congr 1
  ring

private theorem norm_series (z:ℂ) (large:1<z.re):
    Summable (fun n:ℕ=>((n+1:ℕ):ℝ)^(-z.re)):=by
  have series:Summable (fun n:ℕ=>(n:ℝ)^(-z.re)):=Real.summable_nat_rpow.mpr (by linarith)
  exact (summable_nat_add_iff 1).mpr series

private theorem term_norm_summable (w:ℂ) (below:w.re<1) (z:ℂ) (large:1<z.re):
    Summable (fun n:ℕ=>∫x:ℝ,‖priceTerm w below z n x‖ ∂μplus):=by
  simpa only [term_norm_integral] using (norm_series z large).mul_right
    (∫x:ℝ,‖(x:ℂ)^(z-1)*compactRaw (dualRaw w below) x‖ ∂μplus)

private theorem actual_counting_domain (w:ℂ) (below:w.re<1) (z:ℂ) (large:1<z.re):
    MellinConvergent (floorRaw w below) z:=by
  let v (n:ℕ):Lp ℂ 1 μplus:=(term_integrable w below z large n).toL1 (priceTerm w below z n)
  have vn (n:ℕ):‖v n‖=∫x:ℝ,‖priceTerm w below z n x‖ ∂μplus:=by
    rw [L1.norm_eq_integral_norm]
    apply integral_congr_ae
    filter_upwards [(term_integrable w below z large n).coeFn_toL1] with x eq
    exact congrArg norm eq
  have summed:Summable (fun n:ℕ=>‖v n‖):=by
    simpa only [vn] using term_norm_summable w below z large
  let total:Lp ℂ 1 μplus:=∑'n:ℕ,v n
  have source:Integrable (total:ℝ→ℂ) μplus:=memLp_one_iff_integrable.mp (Lp.memLp total)
  have actual:(total:ℝ→ℂ)=ᵐ[μplus]
      fun x:ℝ=>(x:ℂ)^(z-1)*floorRaw w below x:=by
    have coeSum:=Lp.hasSum_coeFn_tsum (tsum_enorm_ne_top_iff_summable_norm.mpr summed)
    have terms:∀ᵐx:ℝ∂μplus,∀n:ℕ,v n x=priceTerm w below z n x:=
      ae_all_iff.mpr (fun n=>(term_integrable w below z large n).coeFn_toL1)
    filter_upwards [coeSum,terms,ae_restrict_mem measurableSet_Ioi] with x sum read positive
    have raw:=sum.congr_fun (fun n=>(read n).symm)
    change (((∑'n:ℕ,v n):Lp ℂ 1 μplus):ℝ→ℂ) x=_
    rw [←raw.tsum_eq]
    simp only [priceTerm,tsum_mul_left,floor_tsum w below x positive.ne']
  exact source.congr actual

/-- The complete original integer grid has an absolute Mellin/Fubini source in Re(z)>1. -/
theorem actual_counting_dirichlet (w:ℂ) (below:w.re<1) (z:ℂ) (large:1<z.re):
    HasMellin (floorRaw w below) z
      (riemannZeta z*mellin (compactRaw (dualRaw w below)) z):=by
  have summed:=hasSum_integral_of_summable_integral_norm
    (fun n=>term_integrable w below z large n) (term_norm_summable w below z large)
  have integral (n:ℕ):(∫x:ℝ,priceTerm w below z n x ∂μplus)=
      (((n+1:ℕ):ℂ)^(-z))*mellin (compactRaw (dualRaw w below)) z:=by
    have positive:(0:ℝ)<(n+1:ℕ):=by positivity
    exact mellin_comp_mul_left _ z positive
  have whole:(∫x:ℝ,(∑'n:ℕ,priceTerm w below z n x) ∂μplus)=mellin (floorRaw w below) z:=by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x positive
    simp only [priceTerm,tsum_mul_left,floor_tsum w below x positive.ne',smul_eq_mul]
  rw [whole,show (fun n:ℕ=>∫x:ℝ,priceTerm w below z n x ∂μplus)=
    (fun n:ℕ=>(((n+1:ℕ):ℂ)^(-z))*mellin (compactRaw (dualRaw w below)) z) from funext integral] at summed
  have norms:Summable (fun n:ℕ=>‖(((n+1:ℕ):ℂ)^(-z))‖):=by
    have eq (n:ℕ):‖(((n+1:ℕ):ℂ)^(-z))‖=((n+1:ℕ):ℝ)^(-z.re):=by
      rw [←Complex.ofReal_natCast,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      rfl
    simpa only [eq] using norm_series z large
  have zeta:(∑'n:ℕ,(((n+1:ℕ):ℂ)^(-z)))=riemannZeta z:=by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow large]
    simp only [Nat.cast_add,Nat.cast_one,Complex.cpow_neg,one_div]
  have target:=norms.of_norm.hasSum.mul_right (mellin (compactRaw (dualRaw w below)) z)
  rw [zeta] at target
  exact ⟨actual_counting_domain w below z large,summed.unique target⟩

theorem actual_counting_source_factorization (w:ℂ) (below:w.re<1) (z:ℂ) (large:1<z.re):
    HasMellin (floorRaw w below) z
      (riemannZeta z*((1/2:ℂ)*(q:ℂ)^(z-star w)/(z-star w)+
        mellin (compactRaw (smoothRaw w below)) z)):=by
  have source:=actual_counting_dirichlet w below z large
  rw [(actual_dual_mellin_source w below z (by linarith) (by linarith)).2] at source
  exact source

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Dirichlet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
