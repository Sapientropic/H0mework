import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.FullPrice

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.ConstantContact
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalKElementaryArithmeticAction.FreeParameter.UnitConsumer OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow
open scoped Topology InnerProductSpace
open private mass_integrable from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.FullPrice
local notation "q" => (1/4 : ℝ)
local notation "T" => burnolTateReciprocalL2
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "test" => OriginalKElementaryArithmeticAction.FreeParameter.RadiusConsumer.radiusTest

def constantField : BurnolL2 := D (Real.log 16) (T ConstantDual.value)

theorem actual_constant_field_raw : (constantField : ℝ→ℂ)=ᵐ[volume]
    fun x=>-((Int.fract (4*|x|):ℝ):ℂ)/((4*|x|:ℝ):ℂ) := by
  have raw := (burnolTateReciprocalL2_coeFn ConstantDual.value).trans
    (burnolTateReciprocalRaw_ae_congr (Lp.memLp ConstantDual.value)
      ConstantDual.sawtooth_memLp ConstantDual.value_coeFn)
  have pull := (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
    (r:=Real.exp (Real.log 16)) (Real.exp_ne_zero _)).ae raw
  filter_upwards [burnolMultiplicativeDilation_coeFn (Real.log 16) (T ConstantDual.value),pull]
    with x dilation read
  change D (Real.log 16) (T ConstantDual.value) x=_
  rw [dilation]
  change (Real.exp (Real.log 16/2):ℂ)*(T ConstantDual.value) (Real.exp (Real.log 16)*x)=_
  simp only [smul_eq_mul] at read
  rw [read,Real.exp_half,Real.exp_log (by norm_num : (0:ℝ)<16)]
  have squareRoot : Real.sqrt (16:ℝ)=4 := by
    rw [show (16:ℝ)=4^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤4)]
  rw [squareRoot]
  simp only [burnolTateReciprocalRaw,ConstantDual.sawtoothRaw,abs_inv,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<16),div_inv_eq_mul]
  have scalar : q*(16*|x|)=4*|x| := by ring
  rw [scalar]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat,mul_inv_rev,div_eq_mul_inv]
  norm_num
  ring

private theorem first_cell (x : ℝ) (nonzero : x≠0) (small : |x|<2*q) :
    -((Int.fract (4*|x|):ℝ):ℂ)/((4*|x|:ℝ):ℂ)=
      if |x|<q then -1 else -1+((4*|x|:ℝ):ℂ)⁻¹ := by
  have positive : 0< |x| := abs_pos.mpr nonzero
  have absNe : ((|x|:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have den : ((4*|x|:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  by_cases inner : |x|<q
  · rw [if_pos inner,Int.fract_eq_self.mpr ⟨by positivity,by linarith⟩]
    field_simp [den,absNe]
  · have floor : Int.floor (4*|x|)=1 := by
      apply Int.floor_eq_iff.mpr
      constructor <;> norm_num <;> linarith
    rw [if_neg inner,Int.fract,floor]
    push_cast
    field_simp [den,absNe]
    ring

def inverseBandRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  if q< |x| ∧ |x|<q*Real.exp h then star (F (test c h) x)/((|x|:ℝ):ℂ) else 0

def inverseBandPrice (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  ∫ x : ℝ,inverseBandRaw c h x

private theorem contact_integrand (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) :
    (fun x : ℝ=>inner ℂ (F (test c h) x) (constantField x))=ᵐ[volume]
      fun x=>-massRaw c h x+(1/4:ℂ)*inverseBandRaw c h x := by
  filter_upwards [actual_constant_field_raw,actual_transformed_outside c h nonnegative,
    volume.ae_ne (0:ℝ),volume.ae_ne q,volume.ae_ne (-q),
    volume.ae_ne (q*Real.exp h),volume.ae_ne (-(q*Real.exp h))]
    with x field outside nonzero neq neMinus neEdge neMinusEdge
  have notQuarter : |x|≠q := by
    intro same
    rcases eq_or_eq_neg_of_abs_eq same with same|same
    · exact neq same
    · exact neMinus same
  have notEdge : |x|≠q*Real.exp h := by
    intro same
    rcases eq_or_eq_neg_of_abs_eq same with same|same
    · exact neEdge same
    · exact neMinusEdge same
  change q*Real.exp h< |x| → F (test c h) x=0 at outside
  rw [RCLike.inner_apply,starRingEnd_apply]
  unfold massRaw inverseBandRaw
  by_cases inside : |x|<q*Real.exp h
  · rw [if_pos inside,field,first_cell x nonzero (inside.trans bound)]
    by_cases before : |x|<q
    · rw [if_pos before,if_neg (fun both=>not_lt_of_ge before.le both.1)]
      ring
    · have after : q< |x| := lt_of_le_of_ne (le_of_not_gt before) notQuarter.symm
      rw [if_neg before,if_pos ⟨after,inside⟩]
      push_cast
      ring
  · have beyond : q*Real.exp h< |x| := lt_of_le_of_ne (le_of_not_gt inside) notEdge.symm
    rw [if_neg inside,if_neg (fun both=>inside both.2),outside beyond,star_zero,mul_zero]
    ring

private theorem inverse_band_integrable (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) : Integrable (inverseBandRaw c h) := by
  have source := (L2.integrable_inner (𝕜:=ℂ) (F (test c h)) constantField).congr
    (contact_integrand c h nonnegative bound)
  have combined := (source.add (mass_integrable c h)).const_mul (4:ℂ)
  convert combined using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- The original constant contact pays its whole mass and its actual first-cell inverse term together. -/
theorem actual_original_constant_contact (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0≤h) (bound : q*Real.exp h<2*q) :
    inner ℂ (movedTest c h) ConstantDual.value=
      -fullMass c h+(1/4:ℂ)*inverseBandPrice c h := by
  have moved := (D (Real.log 16)).inner_map_map (T (movedTest c h)) (T ConstantDual.value)
  rw [OriginalRieszFiniteSynthesis.tate_pairing,burnolTateReciprocalL2_involutive] at moved
  have field : F (test c h)=D (Real.log 16) (T (movedTest c h)) :=
    actual_shifted_test_fourier c h
  rw [←field] at moved
  change inner ℂ (F (test c h)) constantField=inner ℂ (movedTest c h) ConstantDual.value at moved
  rw [←moved,L2.inner_def,integral_congr_ae (contact_integrand c h nonnegative bound),
    integral_add (f:=fun x=>-massRaw c h x) (g:=fun x=>(1/4:ℂ)*inverseBandRaw c h x)
      (mass_integrable c h).neg ((inverse_band_integrable c h nonnegative bound).const_mul _),
    integral_neg,integral_const_mul]
  rfl

end OriginalKElementaryArithmeticAction.FreeParameter.SourceWindow.ConstantContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
