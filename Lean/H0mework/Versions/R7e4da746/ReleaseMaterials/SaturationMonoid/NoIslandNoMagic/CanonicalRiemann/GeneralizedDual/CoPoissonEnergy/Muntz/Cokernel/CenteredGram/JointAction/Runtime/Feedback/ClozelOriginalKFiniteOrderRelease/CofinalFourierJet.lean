import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalFourierSeed
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Source.ModifiedWeakFE.Localization.Physical.Division.SourceRealization.Complete.First.UnitResponse.Resolvent.ParameterJet
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
local notation "q" => (1/4:ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "Cq" => intervalConstant q
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
open private original_seed_quarter source_first_unit unitSeed quarterPower unitQuarterFamily unit_quarter_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.CofinalFourierSeed

private def finiteLogUnit (c:BurnolCompletedMellinCoordinate) (j:Nat):Hq:=
  (2/(1-c.value))^j • Cq-
    (2*(q:ℂ)^(1-c.value)/(1-c.value)) •
      (∑k∈Finset.range j,
        ((2/(1-c.value))^(j-1-k)*(-2:ℂ)^k) • J.dividedLogColumn (barC c) k)

private theorem finite_log_unit_step (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep (barC c) (finiteLogUnit c j)=
      finiteLogUnit c (j+1) := by
  let a:ℂ:=2/(1-c.value)
  let b:ℂ:=2*(q:ℂ)^(1-c.value)/(1-c.value)
  let column:=J.dividedLogColumn (barC c)
  have divide:
      (∑k∈Finset.range (j+1),(a^((j+1)-1-k)*(-2:ℂ)^k) • column k)=
        a^j • column 0+
        (-2:ℂ) • (∑k∈Finset.range j,(a^(j-1-k)*(-2:ℂ)^k) • column (k+1)):=by
    rw[Finset.sum_range_succ']
    simp only[Nat.add_sub_cancel,pow_zero,mul_one,Nat.sub_zero,Finset.smul_sum,smul_smul]
    rw[add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k inside
    have degree:j-(k+1)=j-1-k:=by omega
    rw[degree,pow_succ]
    module
  have shifted:
      (∑k∈Finset.range j,(a^(j-1-k)*(-2:ℂ)^k) • ((-2:ℂ) • column (k+1)))=
        (-2:ℂ) • (∑k∈Finset.range j,(a^(j-1-k)*(-2:ℂ)^k) • column (k+1)):=by
    rw[Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k inside
    module
  unfold finiteLogUnit
  rw[map_sub,map_smul,map_smul,map_sum]
  simp only[map_smul,OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep_log_column,
    OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep_constant,
    OriginalPrimitiveRankBalance.conjugateCoordinate,star_star]
  change a^j • (a • Cq-b • column 0)-b •
    (∑k∈Finset.range j,(a^(j-1-k)*(-2:ℂ)^k) • ((-2:ℂ) • column (k+1)))=
    a^(j+1) • Cq-b •
      (∑k∈Finset.range (j+1),(a^((j+1)-1-k)*(-2:ℂ)^k) • column k)
  rw[shifted,divide,pow_succ]
  module

private theorem quarter_power_logs (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    quarterPower c j=finiteLogUnit c j := by
  induction j with
  | zero => simp[quarterPower,finiteLogUnit]
  | succ j previous =>
    change ((OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep (barC c))^(j+1)) Cq=_
    rw[pow_succ',mul_apply_eq_comp]
    change OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep (barC c) (quarterPower c j)=_
    rw[previous,finite_log_unit_step]

private theorem moment_analytic (c:BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ arithmeticMoment c.value := by
  have nonzero:c.value≠0:=by
    intro h;have:=c.rightHalf;rw[h] at this;norm_num at this
  have notOne:c.value≠1:=by intro h;have:=c.belowOne;rw[h] at this;norm_num at this
  have zeta:AnalyticAt ℂ riemannZeta c.value:=analyticOn_riemannZeta c.value (by simpa using notOne)
  let _:NeZero (3/2:ℂ):=⟨by norm_num⟩
  have powAnalytic:AnalyticAt ℂ (fun s:ℂ=>(3/2:ℂ)^s) c.value:=
    (differentiable_const_cpow_of_neZero (3/2:ℂ)).analyticAt c.value
  unfold arithmeticMoment
  simpa only[Complex.ofReal_div,Complex.ofReal_ofNat,Pi.mul_apply,Pi.sub_apply,Pi.div_apply,id_eq]
    using! ((analyticAt_const (v:=(2:ℂ))).mul zeta).mul
      ((powAnalytic.sub (analyticAt_const (v:=(1:ℂ)))).div analyticAt_id nonzero)

private theorem source_coefficients_analytic (c:BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ arithmeticConstant c.value ∧ AnalyticAt ℂ arithmeticUnit c.value := by
  have nonzero:1-c.value≠0:=by
    intro h;have real:=congrArg Complex.re h
    simp only[Complex.sub_re,Complex.one_re,Complex.zero_re] at real
    linarith[c.belowOne]
  have qPower:AnalyticAt ℂ (fun s:ℂ=>(q:ℂ)^(s-1)) c.value:=by
    have native:Differentiable ℂ (fun s:ℂ=>(q:ℂ)^(s-1)):=
      (differentiable_id.sub_const 1).const_cpow (.inl (by norm_num:(q:ℂ)≠0))
    exact native.analyticAt c.value
  constructor
  · exact (analyticAt_const.div (analyticAt_const.sub analyticAt_id) nonzero).sub
      ((analyticAt_const.mul (moment_analytic c)).mul qPower)
  · exact ((analyticAt_const.sub analyticAt_id).mul (moment_analytic c)).mul qPower

private theorem finite_scalar_vector_jet {scalar:ℂ→ℂ} {vector:ℂ→Hq} {s:ℂ}
    (hs:AnalyticAt ℂ scalar s) (hv:AnalyticAt ℂ vector s) (j:Nat) :
    iteratedDeriv j (fun z=>scalar z • vector z) s=
      ∑k∈Finset.range (j+1),j.choose k •
        (iteratedDeriv k scalar s • iteratedDeriv (j-k) vector s) := by
  simpa only[iteratedDerivWithin_univ,Pi.smul_apply,smul_assoc] using!
    iteratedDerivWithin_smul (Set.mem_univ s) uniqueDiffOn_univ
      (hs.contDiffAt.contDiffWithinAt (n:=j)) (hv.contDiffAt.contDiffWithinAt (n:=j))

private def sourceQuarterFamily (s:ℂ):Hq:=
  burnolQuarterRestriction (fourierL2 (burnolDirectRightResolvent (s/2)
    (burnolPaCombApproximation 0:BurnolL2)))

private theorem source_unit_neighborhood (c:BurnolCompletedMellinCoordinate) :
    sourceQuarterFamily=ᶠ[𝓝 c.value]
      (fun s:ℂ=>arithmeticConstant s • Cq+arithmeticUnit s • unitQuarterFamily s) := by
  have right:{s:ℂ|(1/2:ℝ)<s.re}∈𝓝 c.value:=
    (isOpen_Ioi.preimage Complex.continuous_re).mem_nhds c.rightHalf
  have below:{s:ℂ|s.re<1}∈𝓝 c.value:=
    (isOpen_Iio.preimage Complex.continuous_re).mem_nhds c.belowOne
  filter_upwards[right,below] with s hs ht
  exact source_first_unit ⟨s,hs,ht⟩

def finiteQuarterJet (c:BurnolCompletedMellinCoordinate):Nat→Hq
  | 0=> -Cq
  | j+1=>((2:ℂ)^j/(j.factorial:ℂ)) •
      (iteratedDeriv j arithmeticConstant c.value • Cq+
        ∑k∈Finset.range (j+1),j.choose k •
          (iteratedDeriv k arithmeticUnit c.value •
            (((j-k).factorial:ℂ)/(2:ℂ)^(j-k)) • finiteLogUnit c (j-k+1)))

private def quarterRead:BurnolL2→L[ℂ]Hq:=
  burnolQuarterRestriction.comp fourierL2.toContinuousLinearEquiv.toContinuousLinearMap

private theorem quarter_read_jet {family:ℂ→BurnolL2} {s:ℂ}
    (native:AnalyticAt ℂ family s) (j:Nat) :
    iteratedDeriv j (fun z=>quarterRead (family z)) s=
      quarterRead (iteratedDeriv j family s) := by
  change (iteratedFDeriv ℂ j (quarterRead ∘ family) s) (fun _=>1)=_
  rw[quarterRead.iteratedFDeriv_comp_left (native.contDiffAt (n:=j)) le_rfl]
  rfl

open private quarter_adjoint from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.QuarterSourceCommutator

private theorem quarter_mean_read (value:Hq) :
    burnolQuarterMeanCoefficient value=2*inner ℂ (Cq:Hq) value := by
  unfold burnolQuarterMeanCoefficient
  rw[Complex.ofReal_pow,burnolIntervalConstant_norm_sq (by norm_num:(0:ℝ)<q)]
  norm_num
  ring

private theorem quarter_step_mean (c:BurnolCompletedMellinCoordinate) (value:Hq) :
    burnolQuarterMeanCoefficient
      (OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep (barC c) value)=
        (-2/c.value)*burnolQuarterMeanCoefficient value := by
  have right:1/4<((barC c).value/2).re:=by
    rw[Complex.div_re];norm_num[OriginalPrimitiveRankBalance.conjugateCoordinate];linarith[c.rightHalf]
  have gap:burnolQuarterRestriction (burnolQuarterZeroExtension Cq)=(1:ℂ) • Cq:=by
    rw[burnolQuarterRestriction_zeroExtension,one_smul]
  have actual:=OriginalKForcingGapAction.right_resolvent_quarter_constant
    ((barC c).value/2) right (burnolQuarterZeroExtension Cq) 1 gap
  change OriginalKFiniteOrderRelease.QuarterSourceCommutator.inwardQuarter (barC c) Cq=_ at actual
  rw[quarter_mean_read,quarter_mean_read,quarter_adjoint,actual,inner_smul_left]
  simp only[starRingEnd_apply,OriginalPrimitiveRankBalance.conjugateCoordinate,star_div₀,star_neg,star_one,star_star,star_ofNat]
  ring

private theorem finite_log_unit_mean (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    burnolQuarterMeanCoefficient (finiteLogUnit c j)=(-2/c.value)^j := by
  rw[←quarter_power_logs]
  induction j with
  | zero =>
    have constantSquare:((‖(Cq:Hq)‖:ℂ)^2)=(1/2:ℂ):=by
      norm_num only[show (2*q:ℝ)=1/2 by norm_num,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
        at ⊢
      simpa only[show (2*q:ℝ)=1/2 by norm_num,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
        using! burnolIntervalConstant_norm_sq (by norm_num:(0:ℝ)<q)
    simp only[quarterPower,pow_zero,one_apply_eq_self]
    have fact:=congrArg (fun z:ℂ=>2*z) constantSquare
    norm_num at fact
    simpa only[quarter_mean_read,inner_self_eq_norm_sq_to_K] using! fact
  | succ j previous =>
    change burnolQuarterMeanCoefficient
      (((OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep (barC c))^(j+1)) Cq)=_
    rw[pow_succ',mul_apply_eq_comp]
    change burnolQuarterMeanCoefficient
      (OriginalKFiniteOrderRelease.UnitPowerJordanSource.quarterStep (barC c) (quarterPower c j))=_
    rw[quarter_step_mean,previous,pow_succ']

private theorem native_quarter_jet (c:BurnolCompletedMellinCoordinate) (value:BurnolL2) (j:Nat) :
    iteratedDeriv j (fun s:ℂ=>quarterRead (burnolDirectRightResolvent (s/2) value)) c.value=
      ((j.factorial:ℂ)/(2:ℂ)^j) • quarterRead (((burnolDirectRightResolventCLM c)^(j+1)) value) := by
  have projected:=quarter_read_jet (OriginalRResolventParameterJet.parameter_analytic c value) j
  rw[OriginalRResolventParameterJet.parameter_jet,map_smul] at projected
  exact projected

private theorem unit_quarter_analytic (c:BurnolCompletedMellinCoordinate) :
    AnalyticAt ℂ unitQuarterFamily c.value := by
  change AnalyticAt ℂ (quarterRead ∘ (fun s:ℂ=>burnolDirectRightResolvent (s/2) unitSeed)) c.value
  exact (quarterRead.analyticAt _).comp (OriginalRResolventParameterJet.parameter_analytic c unitSeed)

private theorem unit_quarter_jet (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    iteratedDeriv j unitQuarterFamily c.value=
      ((j.factorial:ℂ)/(2:ℂ)^j) • finiteLogUnit c (j+1) := by
  have projected:=native_quarter_jet c unitSeed j
  change iteratedDeriv j unitQuarterFamily c.value=
    ((j.factorial:ℂ)/(2:ℂ)^j) • burnolQuarterRestriction
      (fourierL2 (((burnolDirectRightResolventCLM c)^(j+1)) unitSeed)) at projected
  rw[unit_quarter_source,quarter_power_logs] at projected
  exact projected

private theorem power_quarter_programme (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    burnolQuarterRestriction (fourierL2 (((burnolDirectRightResolventCLM c)^j)
      (burnolPaCombApproximation 0:BurnolL2)))=finiteQuarterJet c j := by
  cases j with
  | zero => simpa only[pow_zero,one_apply_eq_self,finiteQuarterJet] using original_seed_quarter
  | succ j =>
    have ha:AnalyticAt ℂ arithmeticConstant c.value:=(source_coefficients_analytic c).1
    have hb:AnalyticAt ℂ arithmeticUnit c.value:=(source_coefficients_analytic c).2
    have hu:=unit_quarter_analytic c
    have derived:=(source_unit_neighborhood c).iteratedDeriv_eq j
    have headSmooth:ContDiffAt ℂ j (fun s:ℂ=>arithmeticConstant s • (Cq:Hq)) c.value:=
      (ha.smul (analyticAt_const (v:=(Cq:Hq)))).contDiffAt
    have unitSmooth:ContDiffAt ℂ j (fun s:ℂ=>arithmeticUnit s • unitQuarterFamily s) c.value:=
      (hb.smul hu).contDiffAt
    change iteratedDeriv j sourceQuarterFamily c.value=
      iteratedDeriv j ((fun s:ℂ=>arithmeticConstant s • (Cq:Hq))+
        (fun s:ℂ=>arithmeticUnit s • unitQuarterFamily s)) c.value at derived
    rw[iteratedDeriv_add headSmooth unitSmooth,iteratedDeriv_smul_const (ha.contDiffAt (n:=j)),
      finite_scalar_vector_jet hb hu j] at derived
    have actual:=native_quarter_jet c (burnolPaCombApproximation 0:BurnolL2) j
    change iteratedDeriv j sourceQuarterFamily c.value=
      ((j.factorial:ℂ)/(2:ℂ)^j) • burnolQuarterRestriction
        (fourierL2 (((burnolDirectRightResolventCLM c)^(j+1)) (burnolPaCombApproximation 0:BurnolL2))) at actual
    rw[actual] at derived
    simp_rw[unit_quarter_jet] at derived
    have paid:=congrArg (fun v:Hq=>((2:ℂ)^j/(j.factorial:ℂ)) • v) derived
    have inverse:((2:ℂ)^j/(j.factorial:ℂ))*((j.factorial:ℂ)/(2:ℂ)^j)=1:=by
      field_simp[Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)]
    rw[smul_smul,inverse,one_smul] at paid
    exact paid

/-- The Fourier quarter is executed from the same original counted seed at every source power. -/
theorem value_quarter_programme (c:BurnolCompletedMellinCoordinate) (j:Nat) :
    burnolQuarterRestriction (fourierL2 (Source.valueField c j))=finiteQuarterJet c j := by
  unfold Source.valueField
  rw[OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial.actual_iterate_power]
  exact power_quarter_programme c j

open private position_gap_zero fourier_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction

private theorem B_consumes_generated_quarter (value:BurnolL2) (even:reflectL2 value=value)
    (gap:value∈locallyConstantFace q) (quarter:Hq)
    (generated:burnolQuarterRestriction (fourierL2 value)=quarter) :
    burnolAmbientMeanZeroSecondCorrection value=
      burnolMeanZeroBlockSecond (0,OriginalRieszSource.Constructor.zeroMean quarter) := by
  unfold burnolAmbientMeanZeroSecondCorrection burnolAmbientMeanZeroBlockRhs
  rw [position_gap_zero value even gap,fourier_read value even,generated]

namespace CM
export OriginalKFiniteOrderRelease.CofinalCanonicalSourceMaterial (sourceIndex actual_raw_field)
end CM
namespace Physical
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.OriginalTotalSourcePhysicalConsumer (originalPoint)
end Physical
namespace Recurrence
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Recurrence
  (physicalUpdated original_updated_total)
end Recurrence
open private input_even input_gap from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.Word.Reentry.Action.Pa.Block.TotalSource.RCurrentBSourceConsumer
open private actual_raw_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalOutsideVolterraSource.Source

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬∃n:Nat,observation.coordinate= -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat)
local notation "c₀"=>burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "p₀"=>Physical.originalPoint observation nontrivial half depth ordinal
local notation "g₀"=>Recurrence.physicalUpdated observation nontrivial half depth ordinal

def pointQuarterJet:Hq:=
  finiteQuarterJet c₀ (CM.sourceIndex observation (ordinal+4))-
    finiteQuarterJet c₀ (CM.sourceIndex observation (ordinal+2))

def inputQuarterJet:Hq:=
  finiteQuarterJet c₀ (CM.sourceIndex observation (ordinal+3))-
    finiteQuarterJet c₀ (CM.sourceIndex observation (ordinal+1))

def pointBJet:BurnolQuarterMeanZeroCarrier:=
  burnolMeanZeroBlockSecond (0,OriginalRieszSource.Constructor.zeroMean (pointQuarterJet observation half ordinal))

def inputBJet:BurnolQuarterMeanZeroCarrier:=
  burnolMeanZeroBlockSecond (0,OriginalRieszSource.Constructor.zeroMean (inputQuarterJet observation half ordinal))

private theorem point_even:reflectL2 p₀=p₀ := by
  rw[OriginalRSourceCoupledChannels.actual_point_source,map_sub,
    actual_raw_even observation nontrivial half depth ((ordinal+3)+1),
    actual_raw_even observation nontrivial half depth ((ordinal+1)+1)]

private theorem point_gap:p₀∈locallyConstantFace q := by
  rw[OriginalRSourceCoupledChannels.actual_point_source]
  exact (locallyConstantFace q).sub_mem
    (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ((ordinal+3)+1))
    (OriginalKCombCofinalRAction.actual_source_gap observation nontrivial half depth ((ordinal+1)+1))

theorem original_point_quarter_jet : burnolQuarterRestriction (fourierL2 p₀)=pointQuarterJet observation half ordinal := by
  rw[OriginalRSourceCoupledChannels.actual_point_source,CM.actual_raw_field,CM.actual_raw_field]
  change burnolQuarterRestriction (fourierL2
    (Source.valueField c₀ (CM.sourceIndex observation ((ordinal+3)+1))-
      Source.valueField c₀ (CM.sourceIndex observation ((ordinal+1)+1))))=_
  rw[show (ordinal+3)+1=ordinal+4 by omega,show (ordinal+1)+1=ordinal+2 by omega,
    map_sub,map_sub,value_quarter_programme,value_quarter_programme]
  rfl

theorem original_input_quarter_jet : burnolQuarterRestriction (fourierL2 g₀)=inputQuarterJet observation half ordinal := by
  rw[Recurrence.original_updated_total,CM.actual_raw_field,CM.actual_raw_field]
  change burnolQuarterRestriction (fourierL2
    (Source.valueField c₀ (CM.sourceIndex observation (ordinal+3))-
      Source.valueField c₀ (CM.sourceIndex observation (ordinal+1))))=_
  rw[map_sub,map_sub,value_quarter_programme,value_quarter_programme]
  rfl

/-- The original point's B column is computed from its own two executed word indices. -/
theorem original_point_B_jet : burnolAmbientMeanZeroSecondCorrection p₀=pointBJet observation half ordinal :=
  B_consumes_generated_quarter p₀ (point_even observation nontrivial half depth ordinal)
    (point_gap observation nontrivial half depth ordinal) _
    (original_point_quarter_jet observation nontrivial half depth ordinal)

/-- The registered input uses its original word, preserving its distinct occurrence. -/
theorem input_B_jet : burnolAmbientMeanZeroSecondCorrection g₀=inputBJet observation half ordinal :=
  B_consumes_generated_quarter g₀ (input_even observation nontrivial half depth ordinal)
    (input_gap observation nontrivial half depth ordinal) _
    (original_input_quarter_jet observation nontrivial half depth ordinal)

end OriginalCofinalFourierJet
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
