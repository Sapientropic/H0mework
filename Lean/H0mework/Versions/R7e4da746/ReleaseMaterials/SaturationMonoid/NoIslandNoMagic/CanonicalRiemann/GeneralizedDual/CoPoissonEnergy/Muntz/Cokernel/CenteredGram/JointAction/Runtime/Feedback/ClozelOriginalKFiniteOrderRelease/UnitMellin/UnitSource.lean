import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.UnitMellin.FourierSource
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalUnitMellinSource.Unit
open Complex Filter MeasureTheory Set
open scoped Topology InnerProductSpace
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalUnitMellinSource.Sawtooth OriginalUnitMellinSource.Resolvent OriginalUnitMellinSource.Fourier
local notation "q"=>(1/4:ℝ)
private theorem actual_tate_mellin (v : BurnolL2) (z m : ℂ)
    (source : HasMellin (v:ℝ→ℂ) z m) :
    HasMellin (burnolTateReciprocalL2 v:ℝ→ℂ) (1-z) m := by
  have inverse : MellinConvergent (fun x : ℝ=>v x⁻¹) (-z) := by
    have generated := (MellinConvergent.comp_rpow (f:=(v:ℝ→ℂ)) (s:=-z)
      (by norm_num : (-1:ℝ)≠0)).mpr
      (by simpa only [Complex.ofReal_neg,Complex.ofReal_one,div_neg,div_one,neg_neg] using source.1)
    simpa only [Real.rpow_neg_one] using generated
  have shifted : MellinConvergent (fun x : ℝ=>(x:ℂ)^(-1:ℂ) • v x⁻¹) (1-z) := by
    apply MellinConvergent.cpow_smul.mpr
    simpa only [show (1-z)+(-1)=-z by ring] using inverse
  have raw : (burnolTateReciprocalL2 v:ℝ→ℂ)=ᵐ[volume.restrict (Ioi 0)] fun x : ℝ=>(x:ℂ)^(-1:ℂ) • v x⁻¹ := by
    filter_upwards [ae_restrict_of_ae (burnolTateReciprocalL2_coeFn v),ae_restrict_mem measurableSet_Ioi] with x actual positive
    rw [actual,burnolTateReciprocalRaw,abs_of_pos positive]
    simp only [Complex.cpow_neg,Complex.cpow_one,smul_eq_mul]
  constructor
  · apply shifted.congr
    filter_upwards [raw] with x actual
    rw [actual]
  · have price : mellin (fun x : ℝ=>(x:ℂ)^(-1:ℂ) • v x⁻¹) (1-z)=m := by
      rw [mellin_cpow_smul,show (1-z)+(-1)=-z by ring,mellin_comp_inv,neg_neg,source.2]
    rw [←price]
    unfold mellin
    apply integral_congr_ae
    filter_upwards [raw] with x actual
    rw [actual]

private theorem source_ae (f g:ℝ→ℂ) (z m:ℂ)
    (same:f=ᵐ[volume.restrict (Ioi 0)]g) (source:HasMellin g z m):HasMellin f z m:=by
  have weighted:(fun x:ℝ=>(x:ℂ)^(z-1)*f x)=ᵐ[volume.restrict (Ioi 0)]
      fun x:ℝ=>(x:ℂ)^(z-1)*g x:=by
    filter_upwards [same] with x actual
    rw [actual]
  exact ⟨source.1.congr weighted.symm,(integral_congr_ae weighted).trans source.2⟩

private theorem actual_smul_mellin (v:BurnolL2) (z m a:ℂ) (source:HasMellin (v:ℝ→ℂ) z m):
    HasMellin (a • v:BurnolL2) z (a*m):=by
  have scaled:=hasMellin_const_smul source.1 a
  rw [source.2] at scaled
  apply source_ae _ _ z _ (ae_restrict_of_ae (Lp.coeFn_smul a v))
  change HasMellin (fun x:ℝ=>a*v x) z (a*m)
  simpa only [smul_eq_mul] using scaled

/-- Free read parameter and original action parameter; the whole Fourier unit is retained. -/
theorem actual_unit_quarter_mellin (c:BurnolCompletedMellinCoordinate) (w:ℂ)
    (positive:0<w.re) (below:w.re<1) (between:w.re<c.value.re):
    HasMellin (fourierL2 (burnolUnitTailResponse c q):ℝ→ℂ) (1-w)
      ((q:ℂ)^(w-c.value)*riemannZeta w/(w-c.value)):=by
  have original:=actual_original_d_mellin w positive below
  have acted:=actual_R_mellin c ConstantDual.value w _ original between
  have scaled:=hasMellin_const_smul acted.1 (c.value/2)
  rw [acted.2] at scaled
  have sum:=hasMellin_add original.1 scaled.1
  rw [original.2,scaled.2] at sum
  let v:BurnolL2:=ConstantDual.value+(c.value/2) • burnolDirectRightResolvent (c.value/2) ConstantDual.value
  have asField:(v:ℝ→ℂ)=ᵐ[volume.restrict (Ioi 0)]
      fun x:ℝ=>ConstantDual.value x+(c.value/2) • burnolDirectRightResolvent (c.value/2) ConstantDual.value x:=by
    filter_upwards [ae_restrict_of_ae (Lp.coeFn_add ConstantDual.value
      ((c.value/2) • burnolDirectRightResolvent (c.value/2) ConstantDual.value)),
      ae_restrict_of_ae (Lp.coeFn_smul (c.value/2) (burnolDirectRightResolvent (c.value/2) ConstantDual.value))]
        with x added scalar
    change (ConstantDual.value+(c.value/2) • burnolDirectRightResolvent (c.value/2) ConstantDual.value:BurnolL2) x=_
    rw [added,Pi.add_apply,scalar,Pi.smul_apply]
  have wn:w≠0:=by intro zero;rw [zero] at positive;norm_num at positive
  have dn:w-c.value≠0:=by
    intro zero
    have realPart:=congrArg Complex.re zero
    simp only [sub_re,zero_re] at realPart
    linarith
  have scalar:(q:ℂ)^w*(riemannZeta w/w)+(c.value/2) •
      (2/(w-c.value)*((q:ℂ)^w*(riemannZeta w/w)))=
      (q:ℂ)^w*riemannZeta w/(w-c.value):=by
    rw [smul_eq_mul]
    field_simp [wn,dn]
    ring
  rw [scalar] at sum
  have fieldSource:=source_ae _ _ w _ asField sum
  have reflected:=actual_tate_mellin v w _ fieldSource
  have paid:=actual_smul_mellin _ _ _ ((q:ℂ)^(-c.value)) reflected
  rw [←actual_unit_quarter_fourier c] at paid
  have phase:(q:ℂ)^(-c.value)*(q:ℂ)^w=(q:ℂ)^(w-c.value):=by
    rw [←Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0)]
    congr 1
    ring
  convert paid using 1
  rw [←mul_div_assoc,←mul_assoc,phase]

private theorem actual_dilation_mellin (v:BurnolL2) (w m:ℂ) (shift:ℝ)
    (source:HasMellin (v:ℝ→ℂ) (1-w) m):
    HasMellin (burnolMultiplicativeDilation shift v:ℝ→ℂ) (1-w)
      (Complex.exp ((w-1/2)*(shift:ℂ))*m):=by
  have raw:HasMellin (fun x:ℝ=>(Real.exp (shift/2):ℂ) • v (Real.exp shift*x)) (1-w)
      ((Real.exp (shift/2):ℂ)*(Real.exp shift:ℂ)^(-(1-w))*m):=by
    constructor
    · exact ((MellinConvergent.comp_mul_left (Real.exp_pos shift)).mpr source.1).const_smul _
    · rw [mellin_const_smul,mellin_comp_mul_left _ _ (Real.exp_pos shift),source.2]
      simp only [smul_eq_mul]
      ring
  have phase:(Real.exp (shift/2):ℂ)*(Real.exp shift:ℂ)^(-(1-w))=
      Complex.exp ((w-1/2)*(shift:ℂ)):=by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
      ←Complex.ofReal_log (Real.exp_pos _).le,Real.log_exp,Complex.ofReal_exp,←Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [phase] at raw
  exact source_ae _ _ _ _ (ae_restrict_of_ae (burnolMultiplicativeDilation_coeFn shift v)) raw

/-- Radius transport acts on the original unit source; the physical q window remains fixed. -/
theorem actual_unit_four_mellin (c:BurnolCompletedMellinCoordinate) (w:ℂ)
    (positive:0<w.re) (below:w.re<1) (between:w.re<c.value.re):
    HasMellin (fourierL2 (burnolUnitTailResponse c 4):ℝ→ℂ) (1-w)
      ((4:ℂ)^(w-c.value)*riemannZeta w/(w-c.value)):=by
  have original:=actual_unit_quarter_mellin c w positive below between
  have moved: q*Real.exp (-(-Real.log 16))=4:=by
    rw [neg_neg,Real.exp_log (by norm_num:(0:ℝ)<16)]
    norm_num
  have radius:=burnolUnitTailResponse_radius_dilation c q (by norm_num) (by norm_num)
    (-Real.log 16) (by rw [moved];norm_num)
  rw [moved] at radius
  have flipped:=congrArg fourierL2 radius
  rw [fourierL2_burnolMultiplicativeDilation,map_smul,neg_neg] at flipped
  let character:=fullMellinTranslationCharacter c.value (-Real.log 16)
  have unit:fourierL2 (burnolUnitTailResponse c 4)=character⁻¹ •
      burnolMultiplicativeDilation (Real.log 16) (fourierL2 (burnolUnitTailResponse c q)):=by
    rw [flipped]
    exact (inv_smul_smul₀ (Complex.exp_ne_zero _) _).symm
  have translated:=actual_dilation_mellin _ w _ (Real.log 16) original
  have paid:=actual_smul_mellin _ _ _ character⁻¹ translated
  rw [←unit] at paid
  have phase:character⁻¹*Complex.exp ((w-1/2)*(Real.log 16:ℂ))=(16:ℂ)^(w-c.value):=by
    have logarithm:Complex.log (16:ℂ)=(Real.log 16:ℂ):=by
      have native:=(Complex.ofReal_log (by norm_num:(0:ℝ)≤16)).symm
      simpa only [Complex.ofReal_ofNat] using native
    unfold character fullMellinTranslationCharacter
    rw [←Complex.exp_neg,←Complex.exp_add,Complex.cpow_def_of_ne_zero (by norm_num:(16:ℂ)≠0),logarithm]
    congr 1
    push_cast
    ring
  have combined:(16:ℂ)^(w-c.value)*(q:ℂ)^(w-c.value)=(4:ℂ)^(w-c.value):=by
    have native:=Complex.mul_cpow_ofReal_nonneg (by norm_num:(0:ℝ)≤16)
      (by norm_num:(0:ℝ)≤q) (w-c.value)
    norm_num at native
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using native.symm
  convert paid using 1
  calc
    _=((16:ℂ)^(w-c.value)*(q:ℂ)^(w-c.value))*riemannZeta w/(w-c.value):=by rw [combined]
    _=(character⁻¹*Complex.exp ((w-1/2)*(Real.log 16:ℂ)))*
        (q:ℂ)^(w-c.value)*riemannZeta w/(w-c.value):=by rw [phase]
    _=_:=by ring

end OriginalUnitMellinSource.Unit
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
