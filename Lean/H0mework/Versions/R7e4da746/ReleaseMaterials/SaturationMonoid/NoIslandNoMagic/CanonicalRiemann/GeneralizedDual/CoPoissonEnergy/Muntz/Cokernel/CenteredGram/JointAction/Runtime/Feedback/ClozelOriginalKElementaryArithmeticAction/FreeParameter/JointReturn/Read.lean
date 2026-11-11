import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Program
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Read
open Complex Filter MeasureTheory Set BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Weight OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Program
open scoped InnerProductSpace Topology SchwartzMap
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
open private tate_mean from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.AmbientFourier

def sourceRaw (c:BurnolCompletedMellinCoordinate) : ℝ→ℂ :=
 (symmetricInterval q).indicator (burnolRieszReturnRaw c)

theorem sourceRaw_read (c:BurnolCompletedMellinCoordinate) :
 (E (Constructor.returnState c:Hq):ℝ→ℂ)=ᵐ[volume]sourceRaw c := by
 have localRead:=(ae_restrict_iff' (measurableSet_symmetricInterval q)).mp (Constructor.returnState_read c)
 filter_upwards [burnolQuarterZeroExtension_coe (Constructor.returnState c:Hq),localRead] with x extension read
 rw [extension]
 by_cases inside:x∈symmetricInterval q
 · simp only [sourceRaw,indicator_of_mem inside,read inside]
 · simp only [sourceRaw,indicator_of_notMem inside]

theorem sourceRaw_even (c:BurnolCompletedMellinCoordinate) (x:ℝ) : sourceRaw c (-x)=sourceRaw c x := by
 have same:-x∈symmetricInterval q↔x∈symmetricInterval q:=by
  change -q≤ -x∧ -x≤q↔-q≤x∧x≤q
  constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
 unfold sourceRaw
 by_cases inside:x∈symmetricInterval q
 · rw [indicator_of_mem inside,indicator_of_mem (same.mpr inside),return_raw_even]
 · rw [indicator_of_notMem inside,indicator_of_notMem (fun negInside=>inside (same.mp negInside))]

theorem sourceRaw_integrable (c:BurnolCompletedMellinCoordinate) : Integrable (sourceRaw c) :=
 (burnolQuarterZeroExtensionRaw_integrable (Constructor.returnState c:Hq)).congr
  ((burnolQuarterZeroExtension_coe _).symm.trans (sourceRaw_read c))

theorem sourceRaw_positive_mean_zero (c:BurnolCompletedMellinCoordinate) :
 (∫x:ℝ in Ioi 0,sourceRaw c x)=0 := by
 have fullZero:(∫x:ℝ,sourceRaw c x)=0:=by
  rw [sourceRaw,integral_indicator (measurableSet_symmetricInterval q),
   ←integral_congr_ae (Constructor.returnState_read c)]
  have original:=Constructor.mean_zero (Constructor.returnState c)
  rw [Constructor.mean_integral] at original
  exact (mul_eq_zero.mp original).resolve_left (by norm_num)
 have negative:(∫x:ℝ in Iic 0,sourceRaw c x)=(∫x:ℝ in Ioi 0,sourceRaw c x):=by
  calc
   _=∫x:ℝ in Iic 0,sourceRaw c (-x):=setIntegral_congr_fun measurableSet_Iic (fun x _=>(sourceRaw_even c x).symm)
   _=_:=by simpa only [neg_zero] using integral_comp_neg_Iic 0 (sourceRaw c)
 have split:=setIntegral_union (Iic_disjoint_Ioi (a:=(0:ℝ)) le_rfl) measurableSet_Ioi
  (sourceRaw_integrable c).integrableOn (sourceRaw_integrable c).integrableOn
 rw [Iic_union_Ioi,setIntegral_univ,fullZero,negative] at split
 linear_combination -(1/2:ℂ)*split

private theorem tate_gap (c:BurnolCompletedMellinCoordinate) {x:ℝ} (small:|x|≤q) :
 burnolTateReciprocalRaw (sourceRaw c) x=0 := by
 by_cases zero:x=0
 · simp [burnolTateReciprocalRaw,zero]
 have large:(4:ℝ)≤|x⁻¹|:=by
  rw [abs_inv]
  exact (le_inv_comm₀ (by norm_num:(0:ℝ)<4) (abs_pos.mpr zero)).mpr (by simpa using small)
 have outside:x⁻¹∉symmetricInterval q:=fun inside=>by linarith [abs_le.mpr inside]
 rw [burnolTateReciprocalRaw,sourceRaw,indicator_of_notMem outside,mul_zero]

/-- The return's own two original means pay its complete Fourier-side normalization. -/
theorem actual_fourier_coSum (c:BurnolCompletedMellinCoordinate) :
 (fourierL2 (ReturnCounting.forwardValue c):ℝ→ℂ)=ᵐ[volume]
  burnolInnerGapForward (burnolTateReciprocalRaw (sourceRaw c)) := by
 let source:=E (Constructor.returnState c:Hq)
 let dual:=burnolTateReciprocalL2 source
 let value:=fourierL2 (ReturnCounting.forwardValue c)
 have rawMem:MemLp (sourceRaw c) 2 volume:=(Lp.memLp source).ae_eq (sourceRaw_read c)
 have dualRead:(dual:ℝ→ℂ)=ᵐ[volume]burnolTateReciprocalRaw (sourceRaw c):=
  (burnolTateReciprocalL2_coeFn source).trans
   (burnolTateReciprocalRaw_ae_congr (Lp.memLp source) rawMem (sourceRaw_read c))
 have dualEven:reflectL2 dual=dual:=burnolReflectL2_eq_of_even_raw dual _ dualRead (fun x=>by
  simp only [burnolTateReciprocalRaw,abs_neg,inv_neg,sourceRaw_even])
 have dualGap:(dual:ℝ→ℂ)=ᵐ[volume.restrict (symmetricInterval q)]fun _=>0:=by
  filter_upwards [ae_restrict_of_ae dualRead,ae_restrict_mem (measurableSet_symmetricInterval q)] with x read inside
  rw [read,tate_gap c (abs_le.mpr inside)]
 have realizes (test:SchwartzMap ℝ ℂ):burnolRemainderSourceRead dual test=∫x:ℝ,test x*value x:=by
  simpa only [Lp.toTemperedDistributionCLM_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] using
   burnolRemainderRealization_fourier source (ReturnCounting.forwardValue c) (actual_forward_realizes c) test
 obtain ⟨raw,represents,_,valueRep⟩:=burnolRemainderSourceRead_realization_ae dual value dualEven dualGap realizes
 have same:=represents.symm.trans dualRead
 have meanZero:(∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*raw u)=0:=by
  calc
   _=∫u:ℝ in Ioi 0,(u:ℂ)⁻¹*burnolTateReciprocalRaw (sourceRaw c) u:=by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae same] with u read
    rw [read]
   _=_:=(tate_mean (sourceRaw c)).trans (sourceRaw_positive_mean_zero c)
 have sumRead:=burnolInnerGapForward_ae_congr raw (burnolTateReciprocalRaw (sourceRaw c)) same
 filter_upwards [valueRep,sumRead] with x read counted
 rw [read,meanZero,sub_zero,counted]

/-- Literal reciprocal sampling of the same original return source. -/
def reciprocalRaw (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ := if 4≤|x| then weight c |x| else 0

theorem reciprocalRaw_original (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
 burnolTateReciprocalRaw (sourceRaw c) x=reciprocalRaw c x := by
 by_cases zero:x=0
 · simp [burnolTateReciprocalRaw,reciprocalRaw,zero]
 have positive:0 < |x|:=abs_pos.mpr zero
 have incidence:x⁻¹∈symmetricInterval q↔4≤|x|:=by
  change -q≤x⁻¹∧x⁻¹≤q↔4≤|x|
  rw [←abs_le,abs_inv,inv_le_comm₀ positive (by norm_num:(0:ℝ)<q)]
  norm_num
 unfold burnolTateReciprocalRaw reciprocalRaw sourceRaw
 by_cases active:4≤|x|
 · rw [indicator_of_mem (incidence.mpr active),if_pos active]
   have even:burnolRieszReturnRaw c |x⁻¹|=burnolRieszReturnRaw c x⁻¹:=by
    rcases le_total 0 x⁻¹ with nonnegative | nonpositive
    · rw [abs_of_nonneg nonnegative]
    · rw [abs_of_nonpos nonpositive,return_raw_even]
   rw [←even,abs_inv,weight]
   ring
 · rw [indicator_of_notMem (fun inside=>active (incidence.mp inside)),if_neg active,mul_zero]

def reciprocalCount (c:BurnolCompletedMellinCoordinate) (x:ℝ) : ℂ :=
 ((|x|:ℝ):ℂ)⁻¹*∑n∈AmbientFourierRaw.channels x,burnolRieszReturnRaw c ((n:ℝ)/|x|)

theorem reciprocal_channel (c:BurnolCompletedMellinCoordinate) (x:ℝ) (nonzero:x≠0) (n:ℕ+) :
 (((n:ℕ):ℂ)⁻¹)*reciprocalRaw c (x/(n:ℕ))=
  if (n:ℕ)∈AmbientFourierRaw.channels x then ((|x|:ℝ):ℂ)⁻¹*burnolRieszReturnRaw c ((n:ℕ)/|x|) else 0 := by
 have positive:(0:ℝ)<(n:ℕ):=by exact_mod_cast n.pos
 have absolute:0 < |x|:=abs_pos.mpr nonzero
 have incidence:4≤|x/(n:ℕ)|↔(n:ℕ)∈AmbientFourierRaw.channels x:=by
  simp only [AmbientFourierRaw.channels,Finset.mem_Icc,show 1≤(n:ℕ) from n.pos,true_and,abs_div,abs_of_pos positive,
   Nat.le_floor_iff' n.pos.ne',le_div_iff₀ positive,le_div_iff₀ (by norm_num:(0:ℝ)<4)]
  exact mul_comm (4:ℝ) (n:ℕ) ▸ Iff.rfl
 unfold reciprocalRaw
 simp only [incidence]
 split_ifs
 · rw [weight,abs_div,abs_of_pos positive,inv_div,Complex.ofReal_div]
   field_simp [Complex.ofReal_ne_zero.mpr absolute.ne',show ((n:ℕ):ℂ)≠0 by exact_mod_cast n.pos.ne']
   push_cast
   ring
 · exact mul_zero _

theorem coSum_eq_reciprocalCount (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
 burnolInnerGapForward (reciprocalRaw c) x=reciprocalCount c x := by
 classical
 by_cases zero:x=0
 · subst x
   simp only [burnolInnerGapForward,reciprocalRaw,zero_div,abs_zero,show ¬(4:ℝ)≤0 by norm_num,if_false,mul_zero,
    tsum_zero,reciprocalCount,Complex.ofReal_zero,inv_zero,zero_mul]
 let term:ℕ→ℂ:=fun n=>if n∈AmbientFourierRaw.channels x then
  ((|x|:ℝ):ℂ)⁻¹*burnolRieszReturnRaw c ((n:ℝ)/|x|) else 0
 have support:Function.support term⊆{n:ℕ|0<n}:=by
  intro n active
  have belongs:n∈AmbientFourierRaw.channels x:=by
   by_contra outside
   exact active (if_neg outside)
  exact (Finset.mem_Icc.mp belongs).1
 calc
  _=∑'n:ℕ+,term (n:ℕ):=by apply tsum_congr;exact reciprocal_channel c x zero
  _=∑'n:ℕ,term n:=tsum_subtype_eq_of_support_subset support
  _=∑n∈AmbientFourierRaw.channels x,term n:=tsum_eq_sum (fun n outside=>if_neg outside)
  _=_:=by simp only [term,Finset.sum_ite_mem,Finset.inter_self,reciprocalCount,Finset.mul_sum]

theorem actual_fourier_native_read (c:BurnolCompletedMellinCoordinate) :
 (fourierL2 (ReturnCounting.forwardValue c):ℝ→ℂ)=ᵐ[volume]reciprocalCount c := by
 have same:burnolTateReciprocalRaw (sourceRaw c)=reciprocalRaw c:=funext (reciprocalRaw_original c)
 have source:=actual_fourier_coSum c
 rw [same] at source
 exact source.trans (Eventually.of_forall (coSum_eq_reciprocalCount c))

theorem actual_tate_raw (c:BurnolCompletedMellinCoordinate) (x:ℝ) :
 burnolTateReciprocalRaw (reciprocalCount c) x=ReturnCounting.eventRaw c x := by
 by_cases zero:x=0
 · simp [zero,burnolTateReciprocalRaw,ReturnCounting.eventRaw,DualSourceRaw.channels]
 have absolute:((|x|:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr (abs_pos.mpr zero).ne'
 have channels:AmbientFourierRaw.channels x⁻¹=DualSourceRaw.channels x:=by
  unfold AmbientFourierRaw.channels DualSourceRaw.channels
  rw [abs_inv]
  congr 2
  ring
 unfold burnolTateReciprocalRaw reciprocalCount
 rw [channels,abs_inv,Complex.ofReal_inv,inv_inv,inv_mul_cancel_left₀ absolute]
 simp only [ReturnCounting.eventRaw,div_inv_eq_mul]

/-- The complete return reverse field is the Tate/Fourier read of its original forward programme. -/
theorem actual_return_tate_fourier (c:BurnolCompletedMellinCoordinate) :
 ReturnCounting.value c=burnolTateReciprocalL2 (fourierL2 (ReturnCounting.forwardValue c)) := by
 let actual:=fourierL2 (ReturnCounting.forwardValue c)
 have fourierRead:(actual:ℝ→ℂ)=ᵐ[volume]reciprocalCount c:=actual_fourier_native_read c
 have pulled:=burnolTateReciprocalRaw_ae_congr (Lp.memLp actual) ((Lp.memLp actual).ae_eq fourierRead) fourierRead
 have read:=(burnolTateReciprocalL2_coeFn actual).trans pulled
 have original:=read.trans (Eventually.of_forall (actual_tate_raw c))
 apply Lp.ext
 exact (ReturnCounting.value_coeFn c).trans original.symm

end OriginalKElementaryArithmeticAction.FreeParameter.JointReturn.Read
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
