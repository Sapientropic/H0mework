import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.Sawtooth

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3400000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.SameN
open Complex MeasureTheory Set Filter BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKElementaryArithmeticAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.Sawtooth
open scoped Topology InnerProductSpace
open private power_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.FixedShell
open private reverse_resolvent from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent
local notation "q" => (1/4 : ℝ)
local notation "R" => burnolDirectRightResolventCLM
local notation "D" => burnolMultiplicativeDilation
local notation "seed" => ConstantDual.seed
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate

private theorem elementary_tail_source (c : BurnolCompletedMellinCoordinate) :
    elementarySource (barC c) = GapEuler.gapMean q (barC c) • seed-
      (1/2 : ℂ) • burnolRadiusNormalizedUnitTail c q (by norm_num) := by
  have gap : GapEuler.gapMean q (barC c) • seed =
      star (burnolRadiusMellinGapMoment q (barC c).value) • burnolAmbientGapRieszVector q := by
    unfold GapEuler.gapMean burnolAmbientGapRieszVector
    rw [burnolIntervalConstant_norm_sq (by norm_num : (0 : ℝ)<q)]
    norm_num
    change (_*2) • seed = _ • ((2 : ℂ) • seed)
    rw [smul_smul]
  have raw : burnolAmbientCompletedMellinKernelFormula (barC c) =
      GapEuler.gapMean q (barC c) • seed+
        burnolRadiusMellinTailKernelL2 q (by norm_num) (barC c).value (barC c).rightHalf := by
    change star (burnolRadiusMellinGapMoment q (barC c).value) • burnolAmbientGapRieszVector q+_ = _
    rw [gap]
    simp only [burnolUnscaledCommonGapRadius]
  unfold elementarySource
  rw [raw]
  unfold burnolAmbientEvenPart
  rw [map_add,map_smul,OriginalKSectorEulerMixedSource.actual_seed_source_qualification.2.1]
  change (1/2 : ℂ) • ((GapEuler.gapMean q (barC c) • seed+_)+
    (GapEuler.gapMean q (barC c) • seed+_)) = _
  unfold burnolRadiusNormalizedUnitTail
  dsimp only [OriginalPrimitiveRankBalance.conjugateCoordinate]
  module

/-- The original constant source generates the negative power tail, including its full inside cancellation. -/
theorem actual_seed_quarter_tail (c : BurnolCompletedMellinCoordinate) :
    burnolRadiusNormalizedUnitTail c q (by norm_num) =
      (q : ℂ)^(-c.value) • (seed+(c.value/2) • R c seed) := by
  have source := elementary_unit_resolvent (barC c)
  rw [elementary_tail_source] at source
  unfold unitResolventSource OriginalKSourceResolventReconstruction.sourceResolvent at source
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] at source
  change (c.value*GapEuler.gapMean q (barC c)) •
    (seed-((1-c.value)/2) • R c seed) = GapEuler.gapMean q (barC c) • seed-
      (1/2 : ℂ) • burnolRadiusNormalizedUnitTail c q (by norm_num) at source
  have gap := GapEuler.gapMean_primitive q (by norm_num) (barC c)
  change (1-star (star c.value))*GapEuler.gapMean q (barC c) = (1/2 : ℂ)*(q : ℂ)^(-star (star c.value)) at gap
  rw [star_star] at gap
  have tail : burnolRadiusNormalizedUnitTail c q (by norm_num) =
      (2*(1-c.value)*GapEuler.gapMean q (barC c)) • seed+
        (c.value*(1-c.value)*GapEuler.gapMean q (barC c)) • R c seed := by
    linear_combination (norm := module) (2 : ℂ) • source
  rw [show 2*(1-c.value)*GapEuler.gapMean q (barC c) = (q : ℂ)^(-c.value) by linear_combination 2*gap,
    show c.value*(1-c.value)*GapEuler.gapMean q (barC c) = (q : ℂ)^(-c.value)*(c.value/2) by linear_combination c.value*gap] at tail
  rw [tail]
  module

/-- This is the actual source-level radius-four identity, before applying any finite count. -/
theorem actual_seed_unit_four (c : BurnolCompletedMellinCoordinate) :
    burnolRadiusNormalizedUnitTail c 4 (by norm_num) = sawtoothUnitWord c 0 seed := by
  have radius : q*Real.exp (-(-Real.log 16)) = 4 := by
    rw [neg_neg,Real.exp_log (by norm_num : (0 : ℝ)<16)]
    norm_num
  have moved := burnolRadiusNormalizedUnitTail_dilation c q (by norm_num) (-Real.log 16)
  have movedFour : D (-Real.log 16) (burnolRadiusNormalizedUnitTail c q (by norm_num)) =
      fullMellinTranslationCharacter c.value (-Real.log 16) • burnolRadiusNormalizedUnitTail c 4 (by norm_num) := by
    simpa only [radius] using moved
  rw [actual_seed_quarter_tail,map_smul] at movedFour
  have nonzero : fullMellinTranslationCharacter c.value (-Real.log 16) ≠ 0 := Complex.exp_ne_zero _
  have inverted := congrArg (fun value : BurnolL2 => (fullMellinTranslationCharacter c.value (-Real.log 16))⁻¹ • value) movedFour
  rw [smul_smul,smul_smul,inv_mul_cancel₀ nonzero,one_smul] at inverted
  change bridgeFactor c • D (-Real.log 16) (seed+(c.value/2) • R c seed) = _ at inverted
  simpa only [sawtoothUnitWord,pow_zero,one_apply_eq_self,Nat.zero_add,pow_one] using inverted.symm

private theorem dual_R (c : BurnolCompletedMellinCoordinate) (N : ℕ) (value : BurnolL2) :
    DualSource.source N (R c value) = R c (DualSource.source N value) := by
  change DualSource.source N (burnolDirectRightResolvent (c.value/2) value) =
    burnolDirectRightResolvent (c.value/2) (DualSource.source N value)
  simpa only [OriginalKSourceResolventReconstruction.sourceResolvent,OriginalPrimitiveRankBalance.conjugateCoordinate,star_star] using
    reverse_resolvent N (barC c) value

private theorem dual_power (c : BurnolCompletedMellinCoordinate) (N j : ℕ) (value : BurnolL2) :
    DualSource.source N (((R c)^j) value) = ((R c)^j) (DualSource.source N value) := by
  induction j with
  | zero => rfl
  | succ j previous =>
    rw [pow_succ',mul_apply_eq_comp,dual_R,previous]
    rfl

private theorem dual_dilation (N : ℕ) (h : ℝ) (value : BurnolL2) :
    DualSource.source N (D h value) = D h (DualSource.source N value) := by
  have channel (a : ℝ) : ContinuousChannels.channel 1 a (D h value) = D h (ContinuousChannels.channel 1 a value) := by
    unfold ContinuousChannels.channel
    rw [map_smul,burnolMultiplicativeDilation_add,burnolMultiplicativeDilation_add,add_comm]
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub,map_sum]
  congr 1
  exact (D h).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable 1 N value)

/-- Every power is generated before counting, with the entire high sawtooth column retained. -/
theorem actual_seed_unit_power (c : BurnolCompletedMellinCoordinate) (j : ℕ) :
    ((R c)^j) (burnolRadiusNormalizedUnitTail c 4 (by norm_num)) = sawtoothUnitWord c j seed := by
  rw [actual_seed_unit_four]
  unfold sawtoothUnitWord
  simp only [pow_zero,one_apply_eq_self,Nat.zero_add,pow_one]
  rw [map_smul,power_dilation,map_add,map_smul,pow_succ,mul_apply_eq_comp]

/-- Literal same N: integer stock and the complete continuous 0..N stock follow the same true R word. -/
theorem actual_same_N_unit_source (c : BurnolCompletedMellinCoordinate) (j N : ℕ) :
    DualSource.source N (((R c)^j) (burnolRadiusNormalizedUnitTail c 4 (by norm_num))) =
      sawtoothUnitWord c j (DualSource.source N seed) := by
  rw [actual_seed_unit_power]
  unfold sawtoothUnitWord
  rw [CountingDual.dual_eq_adjoint,map_smul]
  simp only [←CountingDual.dual_eq_adjoint]
  rw [dual_dilation,CountingDual.dual_eq_adjoint,map_add,map_smul]
  simp only [←CountingDual.dual_eq_adjoint]
  rw [dual_power,dual_power]

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.SameN
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
