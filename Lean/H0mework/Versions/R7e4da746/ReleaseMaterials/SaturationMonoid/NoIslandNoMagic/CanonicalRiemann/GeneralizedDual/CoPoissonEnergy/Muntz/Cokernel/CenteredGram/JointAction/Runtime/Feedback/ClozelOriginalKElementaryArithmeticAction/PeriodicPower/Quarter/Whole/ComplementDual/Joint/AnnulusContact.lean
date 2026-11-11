import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusCross
import H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.GapTailDilation

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusContact
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
open scoped Topology InnerProductSpace
open private evenPart_left native_even_tail covector_step outgoing_as_adjoint
  covector_raw logFactor logFactor_nonzero even_half_integral native_even from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
open private realExp_cpow_halfDensity from
  H0mework.Versions.R7e4da746.Arithmetic.MellinProjection.GapTailDilation
local notation "q"=>(1/4:ℝ)
local notation "A"=>sourceAnnulusCut
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

private def shift:ℝ:=Real.log 16
private def scale (d:BurnolCompletedMellinCoordinate):ℂ:=
  fullMellinTranslationCharacter (star d.value) shift

private theorem stretch:Real.exp shift=16:=Real.exp_log (by norm_num)
private theorem landingRadius:(4:ℝ)*Real.exp (-shift)=q:=by
  rw [Real.exp_neg,stretch]
  norm_num

def quarterCovector (d:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolL2:=
  (scale d)⁻¹ • burnolMultiplicativeDilation shift (tailCovector d j)

private theorem quarter_zero (d:BurnolCompletedMellinCoordinate):
    burnolAmbientEvenPart (burnolRadiusMellinTailKernelL2 q (by norm_num) d.value d.rightHalf)=
      quarterCovector d 0:=by
  have moved:=congrArg burnolAmbientEvenPart
    (burnolRadiusMellinTail_dilation (by norm_num:(0:ℝ)<4) d shift)
  have evenDilation (v:BurnolL2):burnolAmbientEvenPart (burnolMultiplicativeDilation shift v)=
      burnolMultiplicativeDilation shift (burnolAmbientEvenPart v):=by
    unfold burnolAmbientEvenPart
    rw [reflectL2_burnolMultiplicativeDilation,map_smul,map_add]
  have evenScalar (a:ℂ) (v:BurnolL2):burnolAmbientEvenPart (a • v)=a • burnolAmbientEvenPart v:=by
    unfold burnolAmbientEvenPart
    rw [map_smul]
    module
  rw [evenDilation,evenScalar,native_even_tail] at moved
  simp only [landingRadius] at moved
  change burnolMultiplicativeDilation shift (tailCovector d 0)=scale d • _ at moved
  unfold quarterCovector
  rw [moved,inv_smul_smul₀ (show scale d≠0 from Complex.exp_ne_zero _)]

private theorem quarter_step (d:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolDirectRightResolventCLM (barC d) (quarterCovector d j)=quarterCovector d (j+1):=by
  rw [quarterCovector,map_smul]
  change (scale d)⁻¹ • burnolDirectRightResolvent ((barC d).value/2)
    (burnolMultiplicativeDilation shift (tailCovector d j))=_
  rw [burnolDirectRightResolvent_dilation]
  change (scale d)⁻¹ • burnolMultiplicativeDilation shift
    (burnolDirectRightResolventCLM (barC d) (tailCovector d j))=_
  rw [covector_step]
  rfl

theorem actual_quarter_tail_price (d:BurnolCompletedMellinCoordinate) (j:ℕ)
    (value:BurnolL2) (even:reflectL2 value=value):
    burnolRadiusMellinTailEvaluator q (by norm_num) d.value d.rightHalf
      (((sourceVolterraResolvent d)^j) value)=inner ℂ (quarterCovector d j) value:=by
  induction j generalizing value with
  | zero =>
    change inner ℂ (burnolRadiusMellinTailKernelL2 q (by norm_num) d.value d.rightHalf) value=_
    rw [←evenPart_left _ value even,quarter_zero]
  | succ j previous =>
    rw [pow_succ,mul_apply_eq_comp]
    have parity:reflectL2 (sourceVolterraResolvent d value)=sourceVolterraResolvent d value:=by
      rw [sourceVolterraResolvent_reflect,even]
    rw [previous _ parity,outgoing_as_adjoint,ContinuousLinearMap.adjoint_inner_right,quarter_step]

def quarterLogRaw (d:BurnolCompletedMellinCoordinate) (j:ℕ) (x:ℝ):ℂ:=
  if q < |x| then ((|x|:ℝ):ℂ)^(-d.value)*(Real.log (|x|/q):ℂ)^j else 0

private theorem quarter_raw (d:BurnolCompletedMellinCoordinate) (j:ℕ):
    (fun x:ℝ=>star (quarterCovector d j x))=ᵐ[volume]
      fun x:ℝ=>logFactor j*quarterLogRaw d j x:=by
  have dilation:Measure.QuasiMeasurePreserving (fun x:ℝ=>Real.exp shift*x) volume volume:=by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ:=(volume:Measure ℝ))
        (r:=Real.exp shift) (Real.exp_ne_zero shift))
  have conjugateScale:star (scale d)=fullMellinTranslationCharacter d.value shift:=by
    change (starRingEnd ℂ) (Complex.exp (((1/2:ℂ)-(starRingEnd ℂ) d.value)*(shift:ℂ)))=_
    rw [←Complex.exp_conj]
    congr 1
    norm_num [map_ofNat]
  filter_upwards [Lp.coeFn_smul (scale d)⁻¹ (burnolMultiplicativeDilation shift (tailCovector d j)),
    burnolMultiplicativeDilation_coeFn shift (tailCovector d j),dilation.ae (covector_raw d j)]
    with x scalar moved raw
  change star (((scale d)⁻¹ • burnolMultiplicativeDilation shift (tailCovector d j):BurnolL2) x)=_
  rw [scalar,Pi.smul_apply,smul_eq_mul,moved]
  change star ((scale d)⁻¹*((Real.exp (shift/2):ℂ)*(tailCovector d j (Real.exp shift*x))))=_
  rw [star_mul,star_mul,raw]
  have absolute:|Real.exp shift*x|=Real.exp shift*|x|:=by
    rw [abs_mul,abs_of_pos (Real.exp_pos shift)]
  have landing:4 < |Real.exp shift*x| ↔ q < |x|:=by
    rw [absolute,stretch]
    constructor <;> intro h <;> linarith
  by_cases outside:q < |x|
  · rw [logTailRaw,if_pos (landing.mpr outside),quarterLogRaw,if_pos outside,absolute]
    have halfDensity:=realExp_cpow_halfDensity (by linarith : 0 < |x|) (barC d).value shift
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at halfDensity
    have logArgument:Real.exp shift*|x|/4=|x|/q:=by rw [stretch];ring
    rw [logArgument]
    simp only [star_inv₀,conjugateScale,star_def,Complex.conj_ofReal]
    calc
      _=logFactor j*(fullMellinTranslationCharacter d.value shift)⁻¹*
          ((Real.exp (shift/2):ℂ)*((Real.exp shift*|x|:ℝ):ℂ)^(-d.value))*
          (Real.log (|x|/q):ℂ)^j:=by ring
      _=_:=by
        rw [halfDensity]
        calc
          _=logFactor j*((fullMellinTranslationCharacter d.value shift)⁻¹*
              fullMellinTranslationCharacter d.value shift)*((|x|:ℝ):ℂ)^(-d.value)*
              (Real.log (|x|/q):ℂ)^j:=by ring
          _=_:=by
            rw [inv_mul_cancel₀ (show fullMellinTranslationCharacter d.value shift≠0
              from Complex.exp_ne_zero _),mul_one]
            ring
  · rw [logTailRaw,if_neg (fun h=>outside (landing.mp h)),quarterLogRaw,if_neg outside]
    ring

private theorem quarter_log_domain (d:BurnolCompletedMellinCoordinate) (j:ℕ) (value:BurnolL2):
    Integrable (fun x:ℝ=>quarterLogRaw d j x*value x) volume:=by
  have paired:Integrable (fun x:ℝ=>star (quarterCovector d j x)*value x):=
    (Lp.memLp (quarterCovector d j)).star.integrable_mul (Lp.memLp value)
  apply (paired.const_mul (logFactor j)⁻¹).congr
  filter_upwards [quarter_raw d j] with x raw
  rw [raw]
  simp only [←mul_assoc,inv_mul_cancel₀ (logFactor_nonzero j),one_mul]

theorem actual_quarter_log_integrable (d:BurnolCompletedMellinCoordinate) (j:ℕ) (value:BurnolL2):
    IntegrableOn (fun x:ℝ=>(x:ℂ)^(-d.value)*(Real.log (x/q):ℂ)^j*value x) (Ioi q):=by
  apply (quarter_log_domain d j value).integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x outside
  change q<x at outside
  have positive:0<x:=by linarith
  rw [quarterLogRaw,abs_of_pos positive,if_pos outside]

theorem actual_quarter_log_bank (d:BurnolCompletedMellinCoordinate) (j:ℕ)
    (value:BurnolL2) (even:reflectL2 value=value):
    burnolRadiusMellinTailEvaluator q (by norm_num) d.value d.rightHalf
      (((sourceVolterraResolvent d)^j) value)=
      ((-2:ℂ)^j/(j.factorial:ℂ))*
        (∫x:ℝ in Ioi q,(x:ℂ)^(-d.value)*(Real.log (x/q):ℂ)^j*value x):=by
  rw [actual_quarter_tail_price d j value even,L2.inner_def]
  have integral:(∫x:ℝ,inner ℂ (quarterCovector d j x) (value x))=
      logFactor j*(∫x:ℝ,quarterLogRaw d j x*value x):=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [quarter_raw d j] with x raw
    simp only [RCLike.inner_apply,starRingEnd_apply]
    rw [raw]
    ring
  rw [integral]
  have valueEven:∀ᵐx:ℝ∂volume,value (-x)=value x:=by
    filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving] with x reflection
    change reflectL2 value x=value (-x) at reflection
    rw [even] at reflection
    exact reflection.symm
  have half:=even_half_integral (fun x:ℝ=>quarterLogRaw d j x*value x) (quarter_log_domain d j value) (by
    filter_upwards [valueEven] with x parity
    simp only [quarterLogRaw,abs_neg,parity])
  have positive:(∫x:ℝ in Ioi (0:ℝ),quarterLogRaw d j x*value x)=
      ∫x:ℝ in Ioi q,(x:ℂ)^(-d.value)*(Real.log (x/q):ℂ)^j*value x:=by
    have cutoff:EqOn (fun x:ℝ=>quarterLogRaw d j x*value x)
        ((Ioi q).indicator (fun x:ℝ=>(x:ℂ)^(-d.value)*(Real.log (x/q):ℂ)^j*value x)) (Ioi 0):=by
      intro x positive
      change 0<x at positive
      dsimp only
      rw [quarterLogRaw,abs_of_pos positive]
      by_cases outside:q<x
      · rw [if_pos outside,indicator_of_mem (show x∈Ioi q from outside)]
      · rw [if_neg outside,indicator_of_notMem (show x∉Ioi q from outside),zero_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi cutoff,integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤q))]
  rw [half,positive]
  unfold logFactor
  ring

private theorem cut_tail (d:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    burnolRadiusMellinTailEvaluator q (by norm_num) d.value d.rightHalf (A value)=
      burnolRadiusMellinTailEvaluator q (by norm_num) d.value d.rightHalf value-
      burnolRadiusMellinTailEvaluator 4 (by norm_num) d.value d.rightHalf value:=by
  rw [burnolRadiusMellinTailEvaluator_eq_integral,burnolRadiusMellinTailEvaluator_eq_integral,
    burnolRadiusMellinTailEvaluator_eq_integral,
    ←integral_indicator measurableSet_Ioi,←integral_indicator measurableSet_Ioi,
    ←integral_indicator measurableSet_Ioi,
    ←integral_sub (integrable_indicator_iff measurableSet_Ioi |>.mpr
      (burnolRadiusMellinWeight_integrableOn_tail q (by norm_num) d.value d.rightHalf value))
      (integrable_indicator_iff measurableSet_Ioi |>.mpr
        (burnolRadiusMellinWeight_integrableOn_tail 4 (by norm_num) d.value d.rightHalf value))]
  apply integral_congr_ae
  filter_upwards [sourceAnnulusCut_coeFn value] with x cut
  by_cases beyond:q<x
  · have positive:0<x:=by linarith
    rw [indicator_of_mem (show x∈Ioi q from beyond),indicator_of_mem (show x∈Ioi q from beyond),
      cut,abs_of_pos positive]
    by_cases outside:4<x
    · rw [indicator_of_mem (show x∈Ioi (4:ℝ) from outside),if_neg (fun h=>not_le.mpr outside h.2)]
      ring
    · rw [indicator_of_notMem (show x∉Ioi (4:ℝ) from outside),if_pos ⟨beyond,le_of_not_gt outside⟩]
      ring
  · have belowFour:¬4<x:=by intro h;exact beyond (lt_trans (by norm_num) h)
    rw [indicator_of_notMem (show x∉Ioi q from beyond),indicator_of_notMem (show x∉Ioi q from beyond),
      indicator_of_notMem (show x∉Ioi (4:ℝ) from belowFour),sub_zero]

/-- Both original cut stocks come from the same native source; the external log differences survive. -/
theorem actual_native_lower_contact (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolRadiusMellinTailEvaluator q (by norm_num) (barC c).value (barC c).rightHalf
      (A (((sourceVolterraResolvent (barC c))^j) (nativeReturn c)))=
      ((-2:ℂ)^j/(j.factorial:ℂ))*
        ((∫x:ℝ in Ioi q,(x:ℂ)^(-star c.value)*(Real.log (x/q):ℂ)^j*nativeReturn c x)-
         (∫x:ℝ in Ioi 4,(x:ℂ)^(-star c.value)*(Real.log (x/4):ℂ)^j*nativeReturn c x)):=by
  rw [cut_tail,actual_quarter_log_bank _ _ _ (native_even c),
    actual_outgoing_log_bank _ _ _ (native_even c)]
  change _=((-2:ℂ)^j/(j.factorial:ℂ))*
    ((∫x:ℝ in Ioi q,(x:ℂ)^(-(barC c).value)*(Real.log (x/q):ℂ)^j*nativeReturn c x)-
      (∫x:ℝ in Ioi 4,(x:ℂ)^(-(barC c).value)*(Real.log (x/4):ℂ)^j*nativeReturn c x))
  ring

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.AnnulusContact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
