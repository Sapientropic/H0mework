import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaQuarterGapHeatSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.JointLogConductorSource
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.RelativeConductorGapReadback
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFace

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalGamma.Source.GammaGapLocal
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalGamma.Source.JointLogConductor
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalGamma.Source.RelativeConductorStrong OriginalGamma.Source.RelativeConductorGapReadback
noncomputable section
local notation "q" => (1/4:ℝ)
local notation "edge" => (1/8:ℝ)

macro "gapLocalPaid% " field:ident : term => do
  let owner:=Lean.Name.num `_private.H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.GammaQuarterGapHeatSource 0
  let scope:=`SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState.OriginalGamma.Source.GammaQuarterGapHeat
  return Lean.mkIdent (owner.append (scope.append field.getId.eraseMacroScopes))

/-- The complete off-diagonal Gamma source, with its original negative half factor. -/
def originalGapGammaRaw (w:BurnolL2) (x:ℝ) : ℂ :=
  -(1/2:ℂ)*(∫y:ℝ,w y*((|x-y|⁻¹:ℝ):ℂ))

private def sourceBudget (w:BurnolL2) : ℝ :=
  (1/2:ℝ)*41*(∫y:ℝ,(1+|y|)⁻¹*‖w y‖)

private theorem raw_measured (w:BurnolL2) : StronglyMeasurable (originalGapGammaRaw w) := by
  have kernel:StronglyMeasurable (fun p:ℝ×ℝ=>w p.2*((|p.1-p.2|⁻¹:ℝ):ℂ)) :=
    ((Lp.stronglyMeasurable w).comp_measurable measurable_snd).mul
      (show Measurable (fun p:ℝ×ℝ=>((|p.1-p.2|⁻¹:ℝ):ℂ)) from by fun_prop).stronglyMeasurable
  exact kernel.integral_prod_right'.const_mul (-(1/2:ℂ))

private theorem actual_gap_kernel_domain (w:BurnolL2)
    (gap:∀ᵐ y:ℝ ∂volume,|y|<q→w y=0) (x:ℝ) (inside:x∈Icc (0:ℝ) edge) :
    Integrable (fun y:ℝ=>w y*((|x-y|⁻¹:ℝ):ℂ)) ∧
    ‖originalGapGammaRaw w x‖≤sourceBudget w := by
  have normalized:Integrable (fun y:ℝ=>(1+|y|)⁻¹*‖w y‖) :=
    (gapLocalPaid% tail_weight_memLp).integrable_mul (Lp.memLp w).norm
  have measured:StronglyMeasurable (fun y:ℝ=>w y*((|x-y|⁻¹:ℝ):ℂ)) :=
    (Lp.stronglyMeasurable w).mul
      (show Measurable (fun y:ℝ=>((|x-y|⁻¹:ℝ):ℂ)) from by fun_prop).stronglyMeasurable
  have bound:∀ᵐ y:ℝ ∂volume,
      ‖w y*((|x-y|⁻¹:ℝ):ℂ)‖≤41*((1+|y|)⁻¹*‖w y‖) := by
    filter_upwards [gap] with y empty
    by_cases vanished:w y=0
    · simp only [vanished,zero_mul,norm_zero]
      positivity
    have away:q≤|y| := by
      by_contra fails
      exact vanished (empty (lt_of_not_ge fails))
    have triangle:|y|≤|x-y|+|x| := by
      calc
        |y|=|(y-x)+x|:=by congr 1;ring
        _≤|y-x|+|x|:=by simpa only [Real.norm_eq_abs] using norm_add_le (y-x) x
        _=|x-y|+|x|:=by rw [abs_sub_comm y x]
    have apart:edge≤|x-y| := by rw [abs_of_nonneg inside.1] at triangle;linarith [inside.2]
    have distance : 0 < |x-y| :=(by norm_num : (0:ℝ)<edge).trans_le apart
    have source:|x-y|⁻¹≤41*(1+|y|)⁻¹ := by
      have paid:=(gapLocalPaid% source_kernel_tail_bound) edge x y (by norm_num)
        (by rw [abs_of_nonneg inside.1];linarith [inside.2]) apart
      norm_num only at paid
      exact paid
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr distance.le)]
    calc
      _≤‖w y‖*(41*(1+|y|)⁻¹):=mul_le_mul_of_nonneg_left source (norm_nonneg _)
      _=_:=by ring
  have domain:Integrable (fun y:ℝ=>w y*((|x-y|⁻¹:ℝ):ℂ)) :=
    (normalized.const_mul 41).mono' measured.aestronglyMeasurable bound
  refine ⟨domain,?_⟩
  unfold originalGapGammaRaw sourceBudget
  rw [norm_mul]
  norm_num only [norm_neg,norm_div,norm_one,norm_ofNat]
  calc
    _≤(1/2:ℝ)*(∫y:ℝ,‖w y*((|x-y|⁻¹:ℝ):ℂ)‖):=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by norm_num)
    _≤(1/2:ℝ)*(∫y:ℝ,41*((1+|y|)⁻¹*‖w y‖)):=
      mul_le_mul_of_nonneg_left (integral_mono_ae domain.norm (normalized.const_mul 41) bound) (by norm_num)
    _=_:=by rw [integral_const_mul];ring

private theorem raw_origin_domain (w:BurnolL2)
    (gap:∀ᵐ y:ℝ ∂volume,|y|<q→w y=0) :
    IntegrableOn (originalGapGammaRaw w) (Ioo (0:ℝ) edge) := by
  have bound:IntegrableOn (fun _:ℝ=>sourceBudget w) (Ioo (0:ℝ) edge) :=
    integrableOn_const (C:=sourceBudget w) (s:=Ioo (0:ℝ) edge)
      (by rw [Real.volume_Ioo];exact ENNReal.ofReal_ne_top)
  apply bound.mono' (raw_measured w).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x inside
  exact (actual_gap_kernel_domain w gap x ⟨inside.1.le,inside.2.le⟩).2

private theorem actual_gap_weak (w gamma:BurnolL2) (source:GammaPair w gamma)
    (gap:∀ᵐ y:ℝ ∂volume,|y|<q→w y=0)
    (test:SchwartzMap ℝ ℂ) (support:tsupport test⊆Ioo (0:ℝ) edge) :
    inner ℂ (test.toLp 2 volume) gamma=∫x:ℝ,star (test x)*originalGapGammaRaw w x := by
  have originalSupport:tsupport test⊆Ioo (0:ℝ) q := fun x member=>
    ⟨(support member).1,by linarith [(support member).2]⟩
  have window:∀ᵐ y:ℝ ∂volume,y∈Ioo (0:ℝ) q→w y=0 := by
    filter_upwards [gap] with y read inside
    exact read (by rw [abs_of_pos inside.1];exact inside.2)
  have domain:=(gapLocalPaid% source_spatial_read_integrable) test w originalSupport window
  change Integrable (fun xy:ℝ×ℝ=>star (test xy.1)*w xy.2*((|xy.1-xy.2|⁻¹:ℝ):ℂ)) (volume.prod volume) at domain
  rw [←source test,(gapLocalPaid% gamma_gap_source) test w originalSupport window,
    integral_prod _ domain,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  rw [originalGapGammaRaw,←integral_const_mul,←integral_const_mul,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  ring

private theorem raw_test_domain (w:BurnolL2)
    (gap:∀ᵐ y:ℝ ∂volume,|y|<q→w y=0) (g:ℝ→ℝ)
    (smooth:ContDiff ℝ (↑(⊤:ENat):WithTop ENat) g) (compact:HasCompactSupport g)
    (support:tsupport g⊆Ioo (0:ℝ) edge) :
    Integrable (fun x:ℝ=>g x • originalGapGammaRaw w x) := by
  have ordinary:Integrable g volume:=smooth.continuous.integrable_of_hasCompactSupport compact
  have bound:Integrable (fun x:ℝ=>‖g x‖*sourceBudget w):=ordinary.norm.mul_const _
  apply bound.mono' (smooth.continuous.stronglyMeasurable.smul (raw_measured w)).aestronglyMeasurable
  filter_upwards with x
  change ‖g x • originalGapGammaRaw w x‖≤‖g x‖*sourceBudget w
  by_cases vanished:g x=0
  · simp only [vanished,zero_smul,norm_zero,zero_mul,le_refl]
  · have inside:=support (subset_tsupport g vanished)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (actual_gap_kernel_domain w gap x ⟨inside.1.le,inside.2.le⟩).2 (norm_nonneg _)

/-- A real q-gap and the actual Gamma weak source generate the local nonlocal-kernel value and its uniform origin budget; no raw formula or regularity is supplied. -/
theorem actual_original_q_gap_Gamma_local_source (w gamma:BurnolL2) (source:GammaPair w gamma)
    (gap:∀ᵐ y:ℝ ∂volume,|y|<q→w y=0) :
    (∀x∈Icc (0:ℝ) edge,‖originalGapGammaRaw w x‖≤
      (1/2:ℝ)*41*(∫y:ℝ,(1+|y|)⁻¹*‖w y‖)) ∧
    (∀ᵐ x:ℝ ∂volume,x∈Ioo (0:ℝ) edge→gamma x=originalGapGammaRaw w x) := by
  refine ⟨fun x inside=>(actual_gap_kernel_domain w gap x inside).2,?_⟩
  have localGamma:=((Lp.memLp gamma).locallyIntegrable (by norm_num : (1:ENNReal)≤2)).locallyIntegrableOn (Ioo (0:ℝ) edge)
  have localRaw:LocallyIntegrableOn (originalGapGammaRaw w) (Ioo (0:ℝ) edge) (volume:Measure ℝ) :=
    locallyIntegrableOn_of_locallyIntegrable_restrict (raw_origin_domain w gap).locallyIntegrable
  have vanished:=isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (localGamma.sub localRaw) ?_
  · filter_upwards [vanished] with x zero inside
    exact sub_eq_zero.mp (zero inside)
  · intro g smooth compact support
    have complexCompact:HasCompactSupport (Complex.ofRealCLM ∘ g):=compact.comp_left rfl
    let test:SchwartzMap ℝ ℂ:=complexCompact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp smooth)
    have testSupport:tsupport test⊆Ioo (0:ℝ) edge:=
      (tsupport_comp_subset (g:=Complex.ofRealCLM) rfl g).trans support
    have read:=actual_gap_weak w gamma source gap test testSupport
    have gammaRead:inner ℂ (test.toLp 2 volume) gamma=∫x:ℝ,g x • gamma x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [test.coeFn_toLp 2 volume] with x actual
      rw [actual,RCLike.inner_apply,starRingEnd_apply]
      change gamma x*star (g x:ℂ)=g x • gamma x
      rw [Complex.star_def,Complex.conj_ofReal,Complex.real_smul,mul_comm]
    have rawRead:(∫x:ℝ,star (test x)*originalGapGammaRaw w x)=∫x:ℝ,g x • originalGapGammaRaw w x := by
      apply integral_congr_ae
      filter_upwards with x
      change star (g x:ℂ)*originalGapGammaRaw w x=_
      rw [Complex.star_def,Complex.conj_ofReal,Complex.real_smul]
    rw [gammaRead,rawRead] at read
    have domain:=((Lp.memLp gamma).locallyIntegrable (by norm_num : (1:ENNReal)≤2)).integrable_smul_left_of_hasCompactSupport smooth.continuous compact
    simp_rw [Pi.sub_apply,smul_sub]
    rw [integral_sub domain (raw_test_domain w gap g smooth compact support),read,sub_self]

end
end OriginalGamma.Source.GammaGapLocal
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
