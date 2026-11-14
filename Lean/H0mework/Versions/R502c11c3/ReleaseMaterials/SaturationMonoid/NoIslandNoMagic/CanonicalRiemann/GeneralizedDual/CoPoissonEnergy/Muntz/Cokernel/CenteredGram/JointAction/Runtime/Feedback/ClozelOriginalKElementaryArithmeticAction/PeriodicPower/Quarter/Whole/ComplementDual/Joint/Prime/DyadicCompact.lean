import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PrimeDual
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.OriginalH

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.DyadicCompact
open Complex Filter MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszSource OriginalRieszSource.Translator OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCoefficientBFiniteAction OriginalKFiniteOrderRelease.UnitPowerJordanSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Fields OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Prices
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.OriginalH OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Paired OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Realized
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Realizer OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.JointSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.CoPoisson.Whole
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKPairedBEulerJunctionSource OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward
open scoped Topology InnerProductSpace
open private halfPower_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.UnitDual
open private native_inverse_source from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Ward.PrimeDual
open private dual_dilation from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.CountingCut
local notation "q" => (1 / 4 : ℝ)
local notation "D" => burnolMultiplicativeDilation
local notation "F" => fourierL2
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "R" => burnolDirectRightResolventCLM
local notation "AN" => FiniteForcing.source
local notation "DN" => DualSource.source
local notation "h₀" => Real.log stageZeroSonineQ
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "order" => generatedRiemannXiZeroOrder ActualAnalyticOwner

def nativeInverseSource (c : BurnolCompletedMellinCoordinate) : BurnolL2 := fourierL2.symm (nativeSource c)

def contractionCharacter (c : BurnolCompletedMellinCoordinate) (h : ℝ) : ℂ :=
  fullMellinTranslationCharacter (star c.value) h

def regularizedSource (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 :=
  D h (nativeInverseSource c) - contractionCharacter c h • nativeInverseSource c

def regularizedCount (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) : BurnolL2 :=
  D h (fullFloorValue c zero) - contractionCharacter c h • fullFloorValue c zero

def regularizedRaw (c : BurnolCompletedMellinCoordinate) (h x : ℝ) : ℂ :=
  (Real.exp (h / 2) : ℂ) * (symmetricInterval q).indicator (dualRaw c.value c.belowOne) (Real.exp h * x) -
    contractionCharacter c h * (symmetricInterval q).indicator (dualRaw c.value c.belowOne) x

private theorem raw_character (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (Real.exp (h / 2) : ℂ) * Complex.exp (-star c.value * (h : ℂ)) = contractionCharacter c h := by
  rw [contractionCharacter, fullMellinTranslationCharacter, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The resonant power cancels inside a genuine whole L2 difference, before the compact dual source is separated. -/
theorem actual_regularized_raw (c : BurnolCompletedMellinCoordinate) (h : ℝ) :
    (regularizedSource c h : ℝ → ℂ) =ᵐ[volume] regularizedRaw c h := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  filter_upwards [Lp.coeFn_sub (D h (nativeInverseSource c)) (contractionCharacter c h • nativeInverseSource c),
    Lp.coeFn_smul (contractionCharacter c h) (nativeInverseSource c),
    burnolMultiplicativeDilation_coeFn h (nativeInverseSource c),
    actual_native_inverse_source_raw c, qmp.ae (actual_native_inverse_source_raw c)]
      with x subtracted scaled dilated direct moved
  rw [regularizedSource, subtracted]
  change D h (nativeInverseSource c) x - (contractionCharacter c h • nativeInverseSource c) x = _
  rw [scaled, dilated]
  change (Real.exp (h / 2) : ℂ) * (nativeInverseSource c) (Real.exp h * x) -
    contractionCharacter c h * (nativeInverseSource c) x = _
  change (nativeInverseSource c) x = _ at direct
  change (nativeInverseSource c) (Real.exp h * x) = _ at moved
  rw [direct, moved, halfPower_dilation]
  unfold regularizedRaw
  rw [mul_sub, mul_sub, ← mul_assoc, raw_character]
  ring

theorem actual_regularized_raw_outside (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (x : ℝ) (outside : q < |x|) : regularizedRaw c h x = 0 := by
  have scale : 1 ≤ Real.exp h := by simpa using Real.exp_le_exp.mpr nonnegative
  have first : x ∉ symmetricInterval q := fun inside => (not_le_of_gt outside) (abs_le.mpr inside)
  have second : Real.exp h * x ∉ symmetricInterval q := by
    intro inside
    have bound : |Real.exp h * x| ≤ q := abs_le.mpr inside
    rw [abs_mul, abs_of_pos (Real.exp_pos h)] at bound
    nlinarith [abs_nonneg x]
  rw [regularizedRaw, indicator_of_notMem first, indicator_of_notMem second]
  ring

private theorem compact_of_raw (value : BurnolL2) (raw : ℝ → ℂ)
    (source : (value : ℝ → ℂ) =ᵐ[volume] raw) (outside : ∀ x, q < |x| → raw x = 0) :
    E (Rq value) = value := by
  have cut := OriginalPaPhysicalGreen.originalPhysicalCutoff_coeFn q value
  change (E (Rq value) : ℝ → ℂ) =ᵐ[volume] (symmetricInterval q).indicator value at cut
  apply Lp.ext
  filter_upwards [cut, source] with x cropped actual
  rw [cropped]
  by_cases inside : x ∈ symmetricInterval q
  · rw [indicator_of_mem inside]
  · rw [indicator_of_notMem inside]
    exact (actual.trans (outside x (lt_of_not_ge (fun small => inside (abs_le.mp small))))).symm

/-- This compact quarter carrier is generated from the actual native source; dualRaw never receives L2 as a premise. -/
theorem actual_regularized_compact (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    E (Rq (regularizedSource c h)) = regularizedSource c h :=
  compact_of_raw _ _ (actual_regularized_raw c h) (actual_regularized_raw_outside c h nonnegative)

private theorem actual_native_forward (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => AN N (nativeSource c)) atTop (𝓝 (F (fullFloorValue c zero))) := by
  have joint := actual_joint_forward_graph c zero
  rw [actual_original_joint_forward_value c zero h₀ junctionShift_pos] at joint
  have head := actual_original_H_forward c zero h₀ junctionShift_pos
  have difference := joint.sub head
  change Tendsto (fun N : ℕ => AN N (jointSource c) - AN N (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave c))
    atTop (𝓝 ((wholeValue c zero h₀ junctionShift_pos + F (fullFloorValue c zero)) - wholeValue c zero h₀ junctionShift_pos)) at difference
  rw [add_sub_cancel_left] at difference
  have finite (N : ℕ) : AN N (nativeSource c) = AN N (jointSource c) - AN N (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Wave.Source.quarterWave c) := by
    change CountingDual.sourceCLM N (nativeSource c) = _
    rw [nativeSource, map_sub]
    rfl
  exact difference.congr' (Eventually.of_forall (fun N => (finite N).symm))

private theorem inverse_dilation (h : ℝ) (v : BurnolL2) :
    fourierL2.symm (D h v) = D (-h) (fourierL2.symm v) := by
  have source := congrArg fourierL2.symm (fourierL2_burnolMultiplicativeDilation (-h) (fourierL2.symm v))
  rw [fourierL2.symm_apply_apply, fourierL2.apply_symm_apply, neg_neg] at source
  exact source.symm

private theorem inverse_fourier_finite (N : ℕ) (v : BurnolL2) :
    DN N (fourierL2.symm v) = fourierL2.symm (AN N v) := by
  have channel (a : ℝ) : ContinuousChannels.channel 1 a (fourierL2.symm v) =
      fourierL2.symm (ContinuousChannels.channel (-1) a v) := by
    simp only [ContinuousChannels.channel, one_mul, neg_one_mul, map_smul]
    rw [inverse_dilation, neg_neg]
  have integer (n : ℕ) : ContinuousChannels.channel 1 n (fourierL2.symm v) =
      fourierL2.symm (Channels.sourceChannel n v) := by
    simpa only [ContinuousChannels.channel, Channels.sourceChannel, one_mul, neg_one_mul] using channel n
  unfold DualSource.source FiniteForcing.source ContinuousChannels.normalization
  simp_rw [integer, channel]
  rw [map_sub, map_sum]
  congr 1
  exact fourierL2.symm.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (ContinuousChannels.channel_integrable (-1) N v)

/-- The original whole graph generates C from the joint L2 inverse source, including the full finite normalization. -/
theorem actual_native_inverse_reverse (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Tendsto (fun N : ℕ => DN N (nativeInverseSource c)) atTop (𝓝 (fullFloorValue c zero)) := by
  have source := (fourierL2.symm.continuous.tendsto _).comp (actual_native_forward c zero)
  rw [fourierL2.symm_apply_apply] at source
  exact source.congr' (Eventually.of_forall (fun N => (inverse_fourier_finite N (nativeSource c)).symm))

theorem actual_regularized_reverse (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) :
    Tendsto (fun N : ℕ => DN N (regularizedSource c h)) atTop (𝓝 (regularizedCount c zero h)) := by
  have base := actual_native_inverse_reverse c zero
  have moved := ((D h).continuous.tendsto _).comp base
  have source := moved.sub (base.const_smul (contractionCharacter c h))
  have finite (N : ℕ) : DN N (regularizedSource c h) =
      D h (DN N (nativeInverseSource c)) - contractionCharacter c h • DN N (nativeInverseSource c) := by
    rw [regularizedSource, CountingDual.dual_eq_adjoint, map_sub, map_smul,
      ← CountingDual.dual_eq_adjoint, ← CountingDual.dual_eq_adjoint, dual_dilation]
  exact source.congr' (Eventually.of_forall (fun N => (finite N).symm))

private theorem reverse_R (N : ℕ) (d : BurnolCompletedMellinCoordinate) (v : BurnolL2) :
    DN N (R d v) = R d (DN N v) := by
  have channel (a : ℝ) : ContinuousChannels.channel 1 a (R d v) = R d (ContinuousChannels.channel 1 a v) := by
    simp only [ContinuousChannels.channel, one_mul, map_smul]
    change _ = (Real.sqrt a : ℂ)⁻¹ •
      burnolDirectRightResolvent (d.value / 2) (D (Real.log a) v)
    rw [burnolDirectRightResolvent_dilation]
    rfl
  unfold DualSource.source
  simp_rw [channel]
  rw [map_sub, map_sum]
  congr 1
  exact (R d).integral_comp_comm (ContinuousChannels.channel_integrable 1 N v)

private theorem reverse_power (N : ℕ) (d : BurnolCompletedMellinCoordinate) (j : ℕ) (v : BurnolL2) :
    DN N (((R d)^j) v) = ((R d)^j) (DN N v) := by
  induction j with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ j previous => rw [pow_succ', mul_apply_eq_comp, reverse_R, previous, mul_apply_eq_comp]

/-- Every original R iterate acts on the genuine compact source before its same-N reverse graph is read. -/
theorem actual_acted_regularized_reverse (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (d : BurnolCompletedMellinCoordinate) (j : ℕ) :
    Tendsto (fun N : ℕ => DN N (((R d)^j) (regularizedSource c h))) atTop
      (𝓝 (((R d)^j) (regularizedCount c zero h))) := by
  have source := (((R d)^j).continuous.tendsto _).comp (actual_regularized_reverse c zero h)
  exact source.congr' (Eventually.of_forall (fun N => (reverse_power N d j (regularizedSource c h)).symm))

private def quarterCut : BurnolL2 →L[ℂ] BurnolL2 := burnolQuarterZeroExtension.comp burnolQuarterRestriction

private theorem contracted_extension (state : BurnolQuarterIntervalL2) (h : ℝ) (nonnegative : 0 ≤ h) :
    quarterCut (D h (E state)) = D h (E state) := by
  have qmp : Measure.QuasiMeasurePreserving (fun x : ℝ => Real.exp h * x) volume volume := by
    simpa only [smul_eq_mul] using
      (Measure.quasiMeasurePreserving_smul (μ := (volume : Measure ℝ))
        (r := Real.exp h) (Real.exp_ne_zero h))
  have raw : (D h (E state) : ℝ → ℂ) =ᵐ[volume]
      fun x => (Real.exp (h / 2) : ℂ) * (symmetricInterval q).indicator state (Real.exp h * x) := by
    filter_upwards [burnolMultiplicativeDilation_coeFn h (E state),
      qmp.ae (burnolQuarterZeroExtension_coe state)] with x dilated source
    rw [dilated]
    change (Real.exp (h / 2) : ℂ) * (E state) (Real.exp h * x) = _
    rw [source]
  exact compact_of_raw _ _ raw (fun x outside => by
    have scale : 1 ≤ Real.exp h := by simpa using Real.exp_le_exp.mpr nonnegative
    have notInside : Real.exp h * x ∉ symmetricInterval q := by
      intro inside
      have small := abs_le.mpr inside
      rw [abs_mul, abs_of_pos (Real.exp_pos h)] at small
      nlinarith [abs_nonneg x]
    rw [indicator_of_notMem notInside, mul_zero])

def contractionAction (c : BurnolCompletedMellinCoordinate) (h : ℝ) : BurnolL2 →L[ℂ] BurnolL2 :=
  (D h).toContinuousLinearEquiv.toContinuousLinearMap - contractionCharacter c h • ContinuousLinearMap.id ℂ BurnolL2

private theorem contraction_extension (c : BurnolCompletedMellinCoordinate) (h : ℝ)
    (nonnegative : 0 ≤ h) (state : BurnolQuarterIntervalL2) :
    quarterCut (contractionAction c h (E state)) = contractionAction c h (E state) := by
  change quarterCut (D h (E state) - contractionCharacter c h • E state) = _
  rw [map_sub, map_smul, contracted_extension state h nonnegative]
  have base : quarterCut (E state) = E state := by
    change E (Rq (E state)) = E state
    rw [burnolQuarterRestriction_zeroExtension]
  rw [base]
  rfl

private theorem contraction_elementary (c : BurnolCompletedMellinCoordinate) (h : ℝ) (nonnegative : 0 ≤ h) :
    quarterCut (contractionAction c h (elementarySource c)) = contractionAction c h (elementarySource c) := by
  have original := native_inverse_source c
  change nativeInverseSource c = E (correction c.value c.belowOne : BurnolQuarterIntervalL2) - elementarySource c at original
  have inventory := congrArg (contractionAction c h) original
  rw [map_sub] at inventory
  change regularizedSource c h = contractionAction c h (E (correction c.value c.belowOne : BurnolQuarterIntervalL2)) -
    contractionAction c h (elementarySource c) at inventory
  have cut := congrArg quarterCut inventory
  rw [map_sub, contraction_extension c h nonnegative,
    show quarterCut (regularizedSource c h) = regularizedSource c h from actual_regularized_compact c h nonnegative] at cut
  linear_combination (norm := module) cut - inventory

private theorem R_power_dilation (d : BurnolCompletedMellinCoordinate) (j : ℕ) (h : ℝ) (v : BurnolL2) :
    ((R d)^j) (D h v) = D h (((R d)^j) v) := by
  induction j with
  | zero => simp only [pow_zero, one_apply_eq_self]
  | succ j previous =>
    rw [pow_succ', mul_apply_eq_comp, previous, mul_apply_eq_comp]
    exact burnolDirectRightResolvent_dilation (d.value / 2) h (((R d)^j) v)

def actedCount (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) (h : ℝ) : BurnolL2 :=
  ((R (barC c))^(order c.value)) (regularizedCount c zero h)

/-- The original exact-m full C field is acted first; its new Euler difference removes the entire genuine exterior column. -/
theorem actual_original_order_count_compact (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) :
    E (Rq (actedCount c zero h)) = actedCount c zero h := by
  have inventory : actedCount c zero h =
      contractionAction c h (OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field.powerValue c zero) := by
    rw [actedCount, regularizedCount, map_sub, map_smul, R_power_dilation]
    rfl
  rw [inventory]
  have full := OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Power.Field.actual_power_full_field c zero
  rw [full, map_add, map_smul]
  change quarterCut (_ + _) = _ + _
  rw [map_add, map_smul, contraction_elementary c h nonnegative, contraction_extension c h nonnegative]

/-- The complete same-N adjoint calculation consumes the new compact source at the original m. -/
theorem actual_original_order_compact_price (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (h : ℝ) (nonnegative : 0 ≤ h) :
    inner ℂ (nativeOutgoingCotest c (order c.value)) (regularizedSource c h) =
      burnolQuarterMeanCoefficient (Rq (actedCount c zero h)) *
        inner ℂ (physicalCotest c : BurnolL2) (originalUnit : BurnolL2) := by
  have adjoint : (R (barC c)).adjoint = sourceStep (barC c) := by
    apply ContinuousLinearMap.ext
    intro v
    exact sourceStep_actual (barC c) v
  have sourcePrice : inner ℂ (nativeOutgoingCotest c (order c.value)) (regularizedSource c h) =
      inner ℂ (pairedCotestForward c) (((R (barC c))^(order c.value)) (regularizedSource c h)) := by
    rw [nativeOutgoingCotest, ← adjoint]
    change inner ℂ (((star (R (barC c)))^(order c.value)) (pairedCotestForward c)) (regularizedSource c h) = _
    rw [← star_pow]
    exact ContinuousLinearMap.adjoint_inner_left ((R (barC c))^(order c.value)) _ _
  have forward := (actual_paired_cotest_forward c zero).inner (𝕜 := ℂ)
    (tendsto_const_nhds (x := ((R (barC c))^(order c.value)) (regularizedSource c h)))
  have reverse := (tendsto_const_nhds (x := (physicalCotest c : BurnolL2))).inner (𝕜 := ℂ)
    (actual_acted_regularized_reverse c zero h (barC c) (order c.value))
  have same := forward.congr' (Eventually.of_forall (fun N => CountingDual.source_pairing N
    (physicalCotest c : BurnolL2) (((R (barC c))^(order c.value)) (regularizedSource c h))))
  have counted := tendsto_nhds_unique same reverse
  rw [sourcePrice, counted]
  change inner ℂ (physicalCotest c : BurnolL2) (actedCount c zero h) = _
  have projection := (evenBurnolClosedFace burnolUnscaledCommonGapRadius).toSubmodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (physicalCotest c) (actedCount c zero h)
  have field := OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.CompactPhysical.actual_compact_projection (Rq (actedCount c zero h))
  rw [actual_original_order_count_compact c zero h nonnegative] at field
  have fieldPrice := congrArg (fun v : BurnolPaAmbientCarrier => inner ℂ (physicalCotest c) v) field
  rw [inner_smul_right] at fieldPrice
  rw [← projection]
  exact fieldPrice

end OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Prime.DyadicCompact
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
