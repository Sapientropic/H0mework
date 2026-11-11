import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCenteredMobiusRSource.UnitTailActionSource

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2800000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Pa OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Native
open scoped Topology InnerProductSpace
namespace Native
export OriginalKCenteredMobiusRSource.UnitTailActionSource
  (nativeUnitMuSource nativeUnitMuRaw native_unit_source_profile native_unit_source_action native_unit_source_zero)
end Native
local notation "barC"=>OriginalPrimitiveRankBalance.conjugateCoordinate

def tailCovector (d:BurnolCompletedMellinCoordinate) (j:ℕ):BurnolL2:=
  (-1/2:ℂ) • Native.nativeUnitMuSource (barC d) j

private theorem evenPart_left (left right:BurnolL2) (even:reflectL2 right=right):
    inner ℂ (burnolAmbientEvenPart left) right=inner ℂ left right:=by
  have reflected:=reflectL2.inner_map_map left right
  rw [even] at reflected
  unfold burnolAmbientEvenPart
  rw [inner_smul_left,inner_add_left,reflected]
  simp only [starRingEnd_apply,star_div₀,star_one,star_ofNat]
  norm_num
  ring

private theorem native_even_tail (d:BurnolCompletedMellinCoordinate):
    burnolAmbientEvenPart (burnolRadiusMellinTailKernelL2 4 (by norm_num) d.value d.rightHalf)=
      tailCovector d 0:=by
  let t:=burnolRadiusMellinTailKernelL2 4 (by norm_num) d.value d.rightHalf
  have raw:(t:ℝ→ℂ)=ᵐ[volume]burnolRadiusMellinTailKernelRaw 4 d.value:=
    MemLp.coeFn_toLp (burnolRadiusMellinTailKernelRaw_memLp (by norm_num) d.value d.rightHalf)
  have reflected:=negMeasurePreserving.quasiMeasurePreserving.ae raw
  have reflectRead:=Lp.coeFn_compMeasurePreserving t negMeasurePreserving
  change (reflectL2 t:ℝ→ℂ)=ᵐ[volume](t:ℝ→ℂ)∘(fun x=>-x) at reflectRead
  unfold burnolAmbientEvenPart
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (1/2:ℂ) (t+reflectL2 t),Lp.coeFn_add t (reflectL2 t),
    Lp.coeFn_smul (-1/2:ℂ) (Native.nativeUnitMuSource (barC d) 0),raw,reflected,reflectRead,
    Native.native_unit_source_zero (barC d)] with x scalar sumRead nativeScalar direct reverse reflection native
  change ((1/2:ℂ) • (t+reflectL2 t):BurnolL2) x=
    ((-1/2:ℂ) • Native.nativeUnitMuSource (barC d) 0:BurnolL2) x
  rw [scalar,Pi.smul_apply,smul_eq_mul,sumRead,Pi.add_apply,nativeScalar,Pi.smul_apply,smul_eq_mul,
    reflection,Function.comp_apply,direct,reverse,native]
  change (1/2:ℂ)*(burnolRadiusMellinTailKernelRaw 4 d.value x+burnolRadiusMellinTailKernelRaw 4 d.value (-x))=
    (-1/2:ℂ)*burnolRadiusUnitTailRaw (star d.value) 4 x
  by_cases positive:0≤x
  · have negativeTail:¬4 < -x:=by linarith
    simp only [burnolRadiusMellinTailKernelRaw,mem_Ioi,burnolRadiusUnitTailRaw,
      abs_of_nonneg positive,if_neg negativeTail]
    by_cases outside:4<x <;> simp [outside]
    ring
  · have negative:x<0:=lt_of_not_ge positive
    have positiveTail:¬4<x:=by linarith
    simp only [burnolRadiusMellinTailKernelRaw,mem_Ioi,burnolRadiusUnitTailRaw,
      abs_of_neg negative,if_neg positiveTail]
    by_cases outside:4 < -x <;> simp [outside]
    ring

private theorem covector_step (d:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolDirectRightResolventCLM (barC d) (tailCovector d j)=tailCovector d (j+1):=by
  rw [tailCovector,map_smul]
  change (-1/2:ℂ) • burnolDirectRightResolvent ((barC d).value/2)
    (Native.nativeUnitMuSource (barC d) j)=_
  rw [Native.native_unit_source_action]
  rfl

private theorem outgoing_as_adjoint (d:BurnolCompletedMellinCoordinate) (value:BurnolL2):
    sourceVolterraResolvent d value=(burnolDirectRightResolventCLM (barC d)).adjoint value:=by
  rw [sourceStep_actual]
  have same:barC (barC d)=d:=by cases d;simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  rw [sourceStep,same]

/-- The original divided-log unit source is the actual covector of every outward tail iterate. -/
theorem actual_outgoing_tail_price (d:BurnolCompletedMellinCoordinate) (j:ℕ)
    (value:BurnolL2) (even:reflectL2 value=value):
    burnolRadiusMellinTailEvaluator 4 (by norm_num) d.value d.rightHalf
      (((sourceVolterraResolvent d)^j) value)=inner ℂ (tailCovector d j) value:=by
  induction j generalizing value with
  | zero =>
    change inner ℂ (burnolRadiusMellinTailKernelL2 4 (by norm_num) d.value d.rightHalf) value=_
    rw [←evenPart_left _ value even]
    exact congrArg (fun v:BurnolL2=>inner ℂ v value) (native_even_tail d)
  | succ j previous =>
    rw [pow_succ,mul_apply_eq_comp]
    have parity:reflectL2 (sourceVolterraResolvent d value)=sourceVolterraResolvent d value:=by
      rw [sourceVolterraResolvent_reflect,even]
    rw [previous _ parity,outgoing_as_adjoint,ContinuousLinearMap.adjoint_inner_right,covector_step]

def logTailRaw (d:BurnolCompletedMellinCoordinate) (j:ℕ) (x:ℝ):ℂ:=
  if 4 < |x| then ((|x|:ℝ):ℂ)^(-d.value)*(Real.log (|x|/4):ℂ)^j else 0

private def logFactor (j:ℕ):ℂ:=(-2:ℂ)^j/(2*(j.factorial:ℂ))

private theorem logFactor_nonzero (j:ℕ):logFactor j≠0:=
  div_ne_zero (pow_ne_zero _ (by norm_num))
    (mul_ne_zero (by norm_num) (by exact_mod_cast Nat.factorial_ne_zero j))

private theorem covector_raw (d:BurnolCompletedMellinCoordinate) (j:ℕ):
    (fun x:ℝ=>star (tailCovector d j x))=ᵐ[volume]fun x:ℝ=>logFactor j*logTailRaw d j x:=by
  filter_upwards [Lp.coeFn_smul (-1/2:ℂ) (Native.nativeUnitMuSource (barC d) j),
    Native.native_unit_source_profile (barC d) j] with x scalar raw
  change star (((-1/2:ℂ) • Native.nativeUnitMuSource (barC d) j:BurnolL2) x)=_
  rw [scalar,Pi.smul_apply,smul_eq_mul,raw]
  by_cases outside:4 < |x|
  · have positive:0 < |x| :=lt_trans (by norm_num) outside
    have argNe:(((|x|:ℝ):ℂ)).arg≠Real.pi:=by
      rw [Complex.arg_ofReal_of_nonneg positive.le]
      exact ne_of_lt Real.pi_pos
    have power:star ((((|x|:ℝ):ℂ))^(-(barC d).value))=(((|x|:ℝ):ℂ))^(-d.value):=by
      simpa only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_def,map_neg,conj_conj,
        Complex.conj_ofReal] using
        (Complex.conj_cpow (((|x|:ℝ):ℂ)) (-d.value) argNe).symm
    rw [Native.nativeUnitMuRaw,if_pos outside,logTailRaw,if_pos outside]
    simp only [star_mul,star_div₀,star_neg,star_pow,star_ofNat,star_one,star_natCast,power,
      star_def,Complex.conj_ofReal]
    unfold logFactor
    ring
  · rw [Native.nativeUnitMuRaw,if_neg outside,mul_zero,star_zero,logTailRaw,if_neg outside,mul_zero]

private theorem complete_log_domain (d:BurnolCompletedMellinCoordinate) (j:ℕ) (value:BurnolL2):
    Integrable (fun x:ℝ=>logTailRaw d j x*value x) volume:=by
  have paired:Integrable (fun x:ℝ=>star (tailCovector d j x)*value x):=
    (Lp.memLp (tailCovector d j)).star.integrable_mul (Lp.memLp value)
  apply (paired.const_mul (logFactor j)⁻¹).congr
  filter_upwards [covector_raw d j] with x raw
  rw [raw]
  simp only [←mul_assoc,inv_mul_cancel₀ (logFactor_nonzero j),one_mul]

/-- Every incomplete external log moment has the actual native L2 covector domain. -/
theorem actual_external_log_integrable (d:BurnolCompletedMellinCoordinate) (j:ℕ) (value:BurnolL2):
    IntegrableOn (fun x:ℝ=>(x:ℂ)^(-d.value)*(Real.log (x/4):ℂ)^j*value x) (Ioi 4):=by
  apply (complete_log_domain d j value).integrableOn.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x outside
  change 4<x at outside
  have positive:0<x:=by linarith
  rw [logTailRaw,abs_of_pos positive,if_pos outside]

private theorem even_half_integral (f:ℝ→ℂ) (domain:Integrable f)
    (even:∀ᵐx:ℝ∂volume,f (-x)=f x):
    (∫x:ℝ,f x)=2*(∫x:ℝ in Ioi (0:ℝ),f x):=by
  have negative:(∫x:ℝ in Iic (0:ℝ),f x)=∫x:ℝ in Ioi (0:ℝ),f x:=by
    calc
      _=∫x:ℝ in Iic (0:ℝ),f (-x):=by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae even] with x parity
        exact parity.symm
      _=_:=by simpa only [neg_zero] using integral_comp_neg_Iic 0 f
  rw [←setIntegral_univ,←Iic_union_Ioi (a:=(0:ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi domain.integrableOn domain.integrableOn,negative]
  ring

/-- The upper contact is an exact external log bank, on the original positive half-axis. -/
theorem actual_outgoing_log_bank (d:BurnolCompletedMellinCoordinate) (j:ℕ)
    (value:BurnolL2) (even:reflectL2 value=value):
    burnolRadiusMellinTailEvaluator 4 (by norm_num) d.value d.rightHalf
      (((sourceVolterraResolvent d)^j) value)=
      ((-2:ℂ)^j/(j.factorial:ℂ))*
        (∫x:ℝ in Ioi 4,(x:ℂ)^(-d.value)*(Real.log (x/4):ℂ)^j*value x):=by
  rw [actual_outgoing_tail_price d j value even,L2.inner_def]
  have integral:(∫x:ℝ,inner ℂ (tailCovector d j x) (value x))=
      logFactor j*(∫x:ℝ,logTailRaw d j x*value x):=by
    rw [←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [covector_raw d j] with x raw
    simp only [RCLike.inner_apply,starRingEnd_apply]
    rw [raw]
    ring
  rw [integral]
  have valueEven:∀ᵐx:ℝ∂volume,value (-x)=value x:=by
    filter_upwards [Lp.coeFn_compMeasurePreserving value negMeasurePreserving] with x reflection
    change reflectL2 value x=value (-x) at reflection
    rw [even] at reflection
    exact reflection.symm
  have half:=even_half_integral (fun x:ℝ=>logTailRaw d j x*value x) (complete_log_domain d j value) (by
    filter_upwards [valueEven] with x parity
    simp only [logTailRaw,abs_neg,parity])
  have positive:(∫x:ℝ in Ioi (0:ℝ),logTailRaw d j x*value x)=
      ∫x:ℝ in Ioi 4,(x:ℂ)^(-d.value)*(Real.log (x/4):ℂ)^j*value x:=by
    have cutoff:EqOn (fun x:ℝ=>logTailRaw d j x*value x)
        ((Ioi (4:ℝ)).indicator (fun x:ℝ=>(x:ℂ)^(-d.value)*(Real.log (x/4):ℂ)^j*value x)) (Ioi 0):=by
      intro x positive
      change 0<x at positive
      dsimp only
      rw [logTailRaw,abs_of_pos positive]
      by_cases outside:4<x
      · rw [if_pos outside,indicator_of_mem (show x∈Ioi (4:ℝ) from outside)]
      · rw [if_neg outside,indicator_of_notMem (show x∉Ioi (4:ℝ) from outside),zero_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi cutoff,integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤4))]
  rw [half,positive]
  unfold logFactor
  ring

private theorem native_even (c:BurnolCompletedMellinCoordinate):reflectL2 (nativeReturn c)=nativeReturn c:=by
  have first:=OriginalKFiniteOrderRelease.UnitPowerJordanAction.log_B_even c 0
  have returned:sourceMeanZeroReflection (burnolMeanZeroTruncatedFourier (logBFirst c 0))=
      burnolMeanZeroTruncatedFourier (logBFirst c 0):=by
    rw [←sourceMeanZeroFourier_reflect,first]
  have quarter:reflectRestricted (1/4) (burnolMeanZeroTruncatedFourier (logBFirst c 0):BurnolQuarterIntervalL2)=
      (burnolMeanZeroTruncatedFourier (logBFirst c 0):BurnolQuarterIntervalL2):=
    congrArg (fun a:BurnolQuarterMeanZeroCarrier=>(a:BurnolQuarterIntervalL2)) returned
  have kernel:reflectL2 (burnolCompletedMellinRieszVector c:BurnolL2)=
      (burnolCompletedMellinRieszVector c:BurnolL2):=
    mem_evenL2ClosedFace_iff.mp (burnolCompletedMellinRieszVector c).property.2
  have extension:reflectL2 (burnolQuarterZeroExtension
      (burnolMeanZeroTruncatedFourier (logBFirst c 0):BurnolQuarterIntervalL2))=
      burnolQuarterZeroExtension (burnolMeanZeroTruncatedFourier (logBFirst c 0):BurnolQuarterIntervalL2):=by
    change reflectL2 (burnolRadiusZeroExtension (1/4) _)=_
    rw [burnolRadiusZeroExtension_reflect,quarter]
    rfl
  unfold nativeReturn
  rw [map_sub,map_smul,←fourierL2_reflectL2_commute,←fourierL2_reflectL2_commute,
    extension,kernel]

/-- The literal native K/log return supplies the complete original upper contact at every order. -/
theorem actual_native_tail_log_bank (c:BurnolCompletedMellinCoordinate) (j:ℕ):
    burnolRadiusMellinTailEvaluator 4 (by norm_num) (barC c).value (barC c).rightHalf (tateSource c j)=
      ((-2:ℂ)^j/(j.factorial:ℂ))*
        (∫x:ℝ in Ioi 4,(x:ℂ)^(-star c.value)*(Real.log (x/4):ℂ)^j*nativeReturn c x):=by
  rw [actual_native_upper_tail,actual_outgoing_log_bank _ _ _ (native_even c)]
  rfl

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.TailLog
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
