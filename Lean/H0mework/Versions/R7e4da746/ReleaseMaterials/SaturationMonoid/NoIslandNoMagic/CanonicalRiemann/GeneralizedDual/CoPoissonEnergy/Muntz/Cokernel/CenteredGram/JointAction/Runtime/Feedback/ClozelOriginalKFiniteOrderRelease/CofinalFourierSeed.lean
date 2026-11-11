import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalSourceProgramme
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletCoefficient
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCofinalFourierJet
open MeasureTheory Set Filter BurnolPhysicalState
open scoped BigOperators Topology
namespace Source
export OriginalKFiniteOrderRelease.CofinalMobiusL2Source (sourceField valueField source_realizes)
end Source
namespace J
export OriginalKFiniteOrderRelease.UnitPowerJordanSource (dividedLogColumn dividedLogRaw dividedLogColumn_profile)
end J
open OriginalKDirectRCofinalOutsideVolterraSource
open OriginalKCrossParameterRAdjointSource.SharedOutsideSource
open private original_seed_value seed_value_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalMobiusL2Source
open private source_mellin_eq_zeta floorDefect defect_mellin_eq error_integrable defect_mellinConvergent from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DirichletCoefficient
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Cq" => intervalConstant q
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

def seedFourierRaw (x:ℝ) : ℂ := 2*burnolReciprocalStepWaveRaw 1 (3/2) x

private theorem seed_fourier_read :
    (fourierL2 (burnolPaCombApproximation 0:BurnolL2):ℝ→ℂ)=ᵐ[volume]seedFourierRaw := by
  let count:=burnolReciprocalStepWaveL2 1 (3/2) (by norm_num) (by norm_num)
  have even:reflectL2 count=count:=mem_evenL2ClosedFace_iff.mp
    (burnolReciprocalStepWave_physical 1 (3/2) (by norm_num) (by norm_num) (by norm_num)).2
  rw [original_seed_value,map_smul,fourierL2_fourierL2,even]
  filter_upwards [Lp.coeFn_smul (2:ℂ) count,
    (burnolReciprocalStepWave_memLp 1 (3/2) (by norm_num) (by norm_num)).coeFn_toLp]
    with x scalar raw
  change (count:ℝ→ℂ) x=burnolReciprocalStepWaveRaw 1 (3/2) x at raw
  rw [scalar,Pi.smul_apply,smul_eq_mul,raw]
  rfl

private theorem seed_fourier_primitive (x:ℝ) :
    seedFourierRaw x=2*((3/2:ℂ)*burnolUnitCountingPrimitiveRaw ((3/2)*x)-burnolUnitCountingPrimitiveRaw x) := by
  have actual:=burnolUnitCountingPrimitive_difference 1 (3/2) x (by norm_num) (by norm_num)
  simpa [seedFourierRaw] using congrArg (fun z:ℂ=>2*z) actual.symm

private theorem seed_fourier_small {x:ℝ} (small:|x|≤q) : seedFourierRaw x= -1 := by
  have scaled:|(3/2:ℝ)*x|≤1 := by
    rw [abs_mul,abs_of_pos (by norm_num:(0:ℝ)<3/2)]
    linarith
  rw [seed_fourier_primitive,burnolUnitCountingPrimitive_small _ scaled,
    burnolUnitCountingPrimitive_small x (by linarith)]
  norm_num

private theorem original_seed_quarter :
    burnolQuarterRestriction (fourierL2 (burnolPaCombApproximation 0:BurnolL2))= -(Cq:Hq) := by
  apply Lp.ext
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (symmetricInterval q)
      (fourierL2 (burnolPaCombApproximation 0:BurnolL2)),
    ae_restrict_of_ae seed_fourier_read,ae_restrict_mem (measurableSet_symmetricInterval q),
    Lp.coeFn_neg (Cq:Hq),intervalConstant_coeFn q] with x restricted actual inside negative unit
  change burnolQuarterRestriction (fourierL2 (burnolPaCombApproximation 0:BurnolL2)) x=_ at restricted
  rw [restricted,actual,seed_fourier_small (abs_le.mpr inside),negative,Pi.neg_apply,unit]

/-- Its full unit subtraction is inherited from the original counted seed. -/
def arithmeticMoment (s:ℂ) : ℂ := 2*riemannZeta s*((((3/2:ℝ):ℂ)^s-1)/s)

private def primitiveSplit (x:ℝ) : ℂ :=
  -(Ioc (0:ℝ) 1).indicator (fun _=>(1:ℂ)) x-(x:ℂ)^(-1:ℂ)*floorDefect x

private theorem primitive_source_split :
    burnolUnitCountingPrimitiveRaw=ᵐ[volume.restrict (Ioi (0:ℝ))]primitiveSplit := by
  have integers:volume (Set.range ((↑):ℤ→ℝ))=0:=
    (Set.countable_range ((↑):ℤ→ℝ)).measure_zero volume
  have away:∀ᵐ x:ℝ ∂volume,x∉Set.range ((↑):ℤ→ℝ):=by
    simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using integers
  filter_upwards [ae_restrict_of_ae away,ae_restrict_mem measurableSet_Ioi] with x outside positive
  change 0<x at positive
  by_cases small:x≤1
  · rw [burnolUnitCountingPrimitive_small x (by rw [abs_of_pos positive];exact small)]
    simp only [primitiveSplit,indicator_of_mem (show x∈Ioc (0:ℝ) 1 from ⟨positive,small⟩),
      floorDefect,indicator_of_notMem (show x∉Ioi (1:ℝ) from not_lt.mpr small),mul_zero,sub_zero]
  · have large:1<x:=lt_of_not_ge small
    have ceiling:⌈x⌉=⌊x⌋+1:=(Int.ceil_eq_floor_add_one_iff_notMem x).mpr outside
    simp only [primitiveSplit,indicator_of_notMem (show x∉Ioc (0:ℝ) 1 from fun h=>small h.2),
      neg_zero,zero_sub,floorDefect,indicator_of_mem (show x∈Ioi (1:ℝ) from large),
      burnolUnitCountingPrimitiveRaw,if_neg positive.ne',abs_of_pos positive,
      natCast_ceil_eq_intCast_ceil positive.le,ceiling,Int.cast_add,Int.cast_one,Int.fract,
      Complex.cpow_neg_one]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr positive.ne']
    ring

private theorem primitive_mellin (c:BurnolCompletedMellinCoordinate) :
    HasMellin burnolUnitCountingPrimitiveRaw (1-c.value) (riemannZeta c.value/c.value) := by
  have low:0<(1-c.value).re:=by simpa using sub_pos.mpr c.belowOne
  have head:=hasMellin_one_Ioc low
  have tail:MellinConvergent (fun x:ℝ=>(x:ℂ)^(-1:ℂ)*floorDefect x) (1-c.value):=by
    have actual:MellinConvergent floorDefect (1-c.value+(-1:ℂ)):=by
      rw[show 1-c.value+(-1:ℂ)= -c.value by ring]
      exact defect_mellinConvergent c.value (by linarith[c.rightHalf])
    exact (MellinConvergent.cpow_smul (f:=floorDefect) (s:=1-c.value) (a:=(-1:ℂ))).mpr actual
  have combined:=hasMellin_sub (head.1.const_smul (-1:ℂ)) tail
  have firstValue:mellin (fun x:ℝ=>(-1:ℂ) • (Ioc (0:ℝ) 1).indicator (fun _=>(1:ℂ)) x)
      (1-c.value)= -(1/(1-c.value)):=by
    rw [(hasMellin_const_smul head.1 (-1:ℂ)).2,head.2]
    simp
  have tailValue:mellin (fun x:ℝ=>(x:ℂ)^(-1:ℂ)*floorDefect x) (1-c.value)=
      mellin floorDefect (-c.value):=by
    simpa only [smul_eq_mul,show 1-c.value+(-1:ℂ)= -c.value by ring] using
      mellin_cpow_smul floorDefect (1-c.value) (-1)
  have sourceEq:(fun x:ℝ=>(x:ℂ)^(1-c.value-1) • burnolUnitCountingPrimitiveRaw x)
      =ᵐ[volume.restrict (Ioi (0:ℝ))]
      (fun x:ℝ=>(x:ℂ)^(1-c.value-1) • primitiveSplit x):=by
    filter_upwards[primitive_source_split] with x hx
    rw[hx]
  have native:MellinConvergent burnolUnitCountingPrimitiveRaw (1-c.value):=by
    have splitNative:MellinConvergent primitiveSplit (1-c.value):=by
      simpa only[primitiveSplit,neg_one_smul] using! combined.1
    exact splitNative.congr sourceEq.symm
  refine ⟨native,?_⟩
  have scalar:-(1/(1-c.value))-mellin floorDefect (-c.value)=riemannZeta c.value/c.value:=by
    have notOne:c.value≠1:=by intro h;simpa[h] using c.belowOne
    have notZero:c.value≠0:=by intro h;have:=c.rightHalf;rw[h] at this;norm_num at this
    have zeta:=source_mellin_eq_zeta c.value (by linarith[c.rightHalf]) notOne
    apply (eq_div_iff notZero).mpr
    calc
      (-(1/(1-c.value))-mellin floorDefect (-c.value))*c.value=
          c.value/(c.value-1)-c.value*mellin floorDefect (-c.value):=by
        field_simp[sub_ne_zero.mpr notOne,sub_ne_zero.mpr notOne.symm]
        ring
      _=riemannZeta c.value:=zeta
  calc
    mellin burnolUnitCountingPrimitiveRaw (1-c.value)=mellin primitiveSplit (1-c.value):=
      integral_congr_ae sourceEq
    _= -(1/(1-c.value))-mellin floorDefect (-c.value):=by
      rw[firstValue,tailValue] at combined
      simpa only[primitiveSplit,neg_one_smul] using! combined.2
    _=riemannZeta c.value/c.value:=scalar

private theorem seed_mellin (c:BurnolCompletedMellinCoordinate) :
    HasMellin seedFourierRaw (1-c.value) (arithmeticMoment c.value) := by
  have primitive:=primitive_mellin c
  have scaled:MellinConvergent (fun x:ℝ=>burnolUnitCountingPrimitiveRaw ((3/2)*x)) (1-c.value):=
    (MellinConvergent.comp_mul_left (f:=burnolUnitCountingPrimitiveRaw) (s:=1-c.value)
      (by norm_num:(0:ℝ)<3/2)).mpr primitive.1
  have difference:=hasMellin_sub (scaled.const_smul (3/2:ℂ)) primitive.1
  have result:=hasMellin_const_smul difference.1 (2:ℂ)
  have actual:(fun x:ℝ=>(2:ℂ) • ((3/2:ℂ) • burnolUnitCountingPrimitiveRaw ((3/2)*x)-
      burnolUnitCountingPrimitiveRaw x))=seedFourierRaw:=by
    funext x
    exact (seed_fourier_primitive x).symm
  have scaledValue:mellin (fun x:ℝ=>burnolUnitCountingPrimitiveRaw ((3/2)*x)) (1-c.value)=
      (3/2:ℂ)^(-(1-c.value))*(riemannZeta c.value/c.value):=by
    rw[mellin_comp_mul_left _ _ (by norm_num:(0:ℝ)<3/2),primitive.2]
    norm_num only[Complex.ofReal_div,Complex.ofReal_ofNat,smul_eq_mul]
  rw[actual] at result
  refine ⟨result.1,?_⟩
  rw[result.2,difference.2,(hasMellin_const_smul scaled (3/2:ℂ)).2,scaledValue,primitive.2]
  have power:(3/2:ℂ)*(3/2:ℂ)^(-(1-c.value))=(3/2:ℂ)^c.value:=by
    rw[show -(1-c.value)=c.value-1 by ring]
    calc
      (3/2:ℂ)*(3/2:ℂ)^(c.value-1)=(3/2:ℂ)^(1+(c.value-1)):=by
        rw[Complex.cpow_add _ _ (by norm_num:(3/2:ℂ)≠0),Complex.cpow_one]
      _=(3/2:ℂ)^c.value:=by congr 1;ring
  change 2*((3/2:ℂ)*((3/2:ℂ)^(-(1-c.value))*(riemannZeta c.value/c.value))-
    riemannZeta c.value/c.value)=arithmeticMoment c.value
  rw[←mul_assoc,power]
  unfold arithmeticMoment
  norm_num only[Complex.ofReal_div,Complex.ofReal_ofNat]
  ring

private theorem seed_tail_moment (c:BurnolCompletedMellinCoordinate) :
    burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf
        (fourierL2 (burnolPaCombApproximation 0:BurnolL2))-
      (q:ℂ)^(1-c.value)/(1-c.value)=arithmeticMoment c.value := by
  let weighted:ℝ→ℂ:=fun x=>(x:ℂ)^(-c.value)*seedFourierRaw x
  have native:IntegrableOn weighted (Ioi (0:ℝ)):=by
    simpa only[MellinConvergent,weighted,show 1-c.value-1= -c.value by ring,smul_eq_mul]
      using! (seed_mellin c).1
  have whole:(∫x:ℝ in Ioi 0,weighted x)=arithmeticMoment c.value:=by
    simpa only[mellin,weighted,show 1-c.value-1= -c.value by ring,smul_eq_mul]
      using! (seed_mellin c).2
  have head:(∫x:ℝ in (0:ℝ)..q,weighted x)= -(q:ℂ)^(1-c.value)/(1-c.value):=by
    have body:(∫x:ℝ in (0:ℝ)..q,weighted x)= -(∫x:ℝ in (0:ℝ)..q,(x:ℂ)^(-c.value)):=by
      rw[←intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x inside
      rw[uIcc_of_le (by norm_num:(0:ℝ)≤q)] at inside
      dsimp only[weighted]
      rw[seed_fourier_small (by rw[abs_of_nonneg inside.1];exact inside.2),mul_neg,mul_one]
    rw[body,integral_cpow (Or.inl (by simp only[Complex.neg_re];linarith[c.belowOne])),
      show -c.value+1=1-c.value by ring,Complex.ofReal_zero,
      Complex.zero_cpow (by intro h;have:=congrArg Complex.re h;simp only[Complex.sub_re,Complex.one_re,Complex.zero_re] at this;linarith[c.belowOne]),
      sub_zero,neg_div]
  have tail:burnolRadiusMellinTailEvaluator q (by norm_num) c.value c.rightHalf
      (fourierL2 (burnolPaCombApproximation 0:BurnolL2))=∫x:ℝ in Ioi q,weighted x:=by
    rw[burnolRadiusMellinTailEvaluator_eq_integral]
    apply integral_congr_ae
    filter_upwards[ae_restrict_of_ae seed_fourier_read] with x hx
    rw[hx]
  have split:=intervalIntegral.integral_Ioi_sub_Ioi native (by norm_num:(0:ℝ)≤q)
  rw[whole,head,←tail] at split
  linear_combination -split

private theorem source_first_quarter (c:BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (fourierL2 (burnolDirectRightResolvent (c.value/2)
        (burnolPaCombApproximation 0:BurnolL2)))=
      (-2/(1-c.value)) • Cq+
      (-2*arithmeticMoment c.value) • J.dividedLogColumn (barC c) 0 := by
  have even:reflectL2 (fourierL2 (burnolPaCombApproximation 0:BurnolL2))=
      fourierL2 (burnolPaCombApproximation 0:BurnolL2):=by
    rw[←fourierL2_reflectL2_commute,seed_value_even]
  have source:=paidConjugateVolterraQuarter
    (barC c) (fourierL2 (burnolPaCombApproximation 0:BurnolL2)) (-1)
    (by simpa only[neg_one_smul] using original_seed_quarter) even
  change burnolQuarterRestriction (OriginalPaPhysicalGreen.sourceVolterraResolvent (barC (barC c))
    (fourierL2 (burnolPaCombApproximation 0:BurnolL2)))=_ at source
  have barBar:barC (barC c)=c:=by cases c;simp[OriginalPrimitiveRankBalance.conjugateCoordinate]
  rw[barBar] at source
  change burnolQuarterRestriction (sourceFourierInput c (burnolPaCombApproximation 0:BurnolL2))=_ at source
  rw[source_fourier_input] at source
  change _=(2*(-1)/(1-star (barC c).value)) • Cq+
    (-2*(burnolRadiusMellinTailEvaluator q (by norm_num) (star (barC c).value)
      (by simpa only[Complex.star_def,Complex.conj_re] using (barC c).rightHalf)
      (fourierL2 (burnolPaCombApproximation 0:BurnolL2))+
      (-1)*(q:ℂ)^(1-star (barC c).value)/(1-star (barC c).value))) • J.dividedLogColumn (barC c) 0 at source
  simpa only[OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,mul_neg_one,neg_one_mul,
    neg_div,←sub_eq_add_neg,seed_tail_moment] using source

open private source_extension source_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

private theorem bar_bar (c:BurnolCompletedMellinCoordinate) : barC (barC c)=c := by
  cases c;simp[OriginalPrimitiveRankBalance.conjugateCoordinate]

private def unitSeed:BurnolL2:=fourierL2.symm (burnolQuarterZeroExtension Cq)

private def quarterPower (c:BurnolCompletedMellinCoordinate) (j:Nat):Hq:=
  ((OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep (barC c))^j) Cq

private theorem unit_power_source (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    fourierL2 (((burnolDirectRightResolventCLM c)^j) unitSeed)=
      burnolQuarterZeroExtension (quarterPower c j) := by
  induction j with
  | zero => simp[unitSeed,quarterPower]
  | succ j previous =>
    have step:=source_fourier (barC c) (((burnolDirectRightResolventCLM c)^j) unitSeed)
    rw[bar_bar] at step
    rw[pow_succ',mul_apply_eq_comp,←step,previous,source_extension]
    simp only[quarterPower,pow_succ',mul_apply_eq_comp]

private def unitQuarterFamily (s:ℂ):Hq:=
  burnolQuarterRestriction (fourierL2 (burnolDirectRightResolvent (s/2) unitSeed))

private theorem unit_quarter_source (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    burnolQuarterRestriction (fourierL2 (((burnolDirectRightResolventCLM c)^j) unitSeed))=
      quarterPower c j := by
  rw[unit_power_source,burnolQuarterRestriction_zeroExtension]

def arithmeticConstant (s:ℂ):ℂ:= -2/(1-s)-2*arithmeticMoment s*(q:ℂ)^(s-1)
def arithmeticUnit (s:ℂ):ℂ:= (1-s)*arithmeticMoment s*(q:ℂ)^(s-1)

private theorem source_first_unit (c:BurnolCompletedMellinCoordinate) :
    burnolQuarterRestriction (fourierL2 (burnolDirectRightResolvent (c.value/2)
      (burnolPaCombApproximation 0:BurnolL2)))=
      arithmeticConstant c.value • Cq+arithmeticUnit c.value • unitQuarterFamily c.value := by
  have unit:unitQuarterFamily c.value=quarterPower c 1:=unit_quarter_source c 1
  rw[source_first_quarter,unit]
  simp only[quarterPower,pow_one,OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep_constant,
    OriginalPrimitiveRankBalance.conjugateCoordinate,star_star,smul_sub,smul_smul,J.dividedLogColumn]
  have denominator:1-c.value≠0:=by
    intro h
    have real:=congrArg Complex.re h
    simp only[Complex.sub_re,Complex.one_re,Complex.zero_re] at real
    linarith[c.belowOne]
  have inverse:(q:ℂ)^(c.value-1)*(q:ℂ)^(1-c.value)=1:=by
    rw[←Complex.cpow_add _ _ (by norm_num:(q:ℂ)≠0),
      show (c.value-1)+(1-c.value)=0 by ring,Complex.cpow_zero]
  have meanCoeff:arithmeticConstant c.value+arithmeticUnit c.value*(2/(1-c.value))=
      -2/(1-c.value):=by
    unfold arithmeticConstant arithmeticUnit
    field_simp[denominator]
    ring
  have logCoeff:arithmeticUnit c.value*(2*(q:ℂ)^(1-c.value)/(1-c.value))=
      2*arithmeticMoment c.value:=by
    unfold arithmeticUnit
    calc
      (1-c.value)*arithmeticMoment c.value*(q:ℂ)^(c.value-1)*
          (2*(q:ℂ)^(1-c.value)/(1-c.value))=
          2*arithmeticMoment c.value*((q:ℂ)^(c.value-1)*(q:ℂ)^(1-c.value)):=by
        field_simp[denominator]
      _=2*arithmeticMoment c.value:=by rw[inverse,mul_one]
  rw[logCoeff]
  have coefficient:=congrArg (fun z:ℂ=>z • (Cq:Hq)) meanCoeff
  simp only[add_smul] at coefficient
  rw[←coefficient]
  module


end OriginalCofinalFourierJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
