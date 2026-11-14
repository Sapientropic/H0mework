import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.DualSource.NormalizationResolvent
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.SameN
import H0mework.Versions.R7e4da746.Arithmetic.RiemannUnitShell.Algebra

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open OriginalKCoefficientBFiniteAction OriginalKCompactAdjointRSource
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Compact.ResolventTail
open scoped InnerProductSpace

open private compensated_even from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private moment from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private star_ne_one quarterExterior quarterTail from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation
open private native_return_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open private elementary_tail_source from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Unit.SameN
open private quarter_tail_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail

local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "Q" => burnolQuarterRestriction
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "Cut" => originalPhysicalCutoff q
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R₀" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "Rhalf" => burnolDirectRightResolvent (1/2)
local notation "returnField" => fun c => E (S (nativeSmooth c) : Hq)

private theorem first_coefficient : CoefficientJet.finite 0 = fun s : ℂ => (s-1)⁻¹ := by
  funext s
  simp only [CoefficientJet.finite, Nat.zero_add, FiniteForcing.coefficient, Finset.Ico_self,
    Finset.sum_empty, Nat.cast_one, Complex.one_cpow, zero_sub, one_div]
  rw [← inv_neg, neg_sub]

private theorem first_jet (s : ℂ) (live : s ≠ 1) :
    CoefficientJet.jet 1 0 s = -((s-1)⁻¹)^2 := by
  have derivative := ((hasDerivAt_id s).sub_const (1 : ℂ)).inv (sub_ne_zero.mpr live)
  change HasDerivAt (fun t : ℂ => (t-1)⁻¹) (-1/(s-1)^2) s at derivative
  rw [CoefficientJet.jet, iteratedDeriv_one, first_coefficient, derivative.deriv, neg_div, one_div, inv_pow]

private theorem first_count_source (c : BurnolCompletedMellinCoordinate) :
    compensated c 1 = (1/2 : ℂ) • Rhalf (input c) + (star c.value-1)⁻¹ • elementarySource c := by
  have coefficient : FiniteForcing.coefficient (star c.value) 1 = (star c.value-1)⁻¹ :=
    congrFun first_coefficient (star c.value)
  rw [compensated, DualSource.actual_first_source]
  change (1/2 : ℂ) • Rhalf (input c) + FiniteForcing.coefficient (star c.value) 1 • elementarySource c = _
  rw [coefficient]

/-- The two resolvents act on the literal first compensated cutoff and its continuous normalization. -/
theorem actual_first_count_action (c : BurnolCompletedMellinCoordinate) :
    (star c.value-1) • R₀ c (compensated c 1) =
      R₀ c (returnField c) - (2 : ℂ) • compensated c 1 +
        (2*(star c.value-1)⁻¹) • elementarySource c := by
  let s := star c.value
  let d := s-1
  let halfField := Rhalf (input c)
  have right : 1/4 < (s/2).re := by
    rw [Complex.div_re]
    norm_num [s, Complex.star_def, Complex.conj_re]
    linarith [c.rightHalf]
  have parameter : s/2 - 1/2 = d/2 := by dsimp only [d]; ring
  have original := burnolDirectRightResolvent_identity (s/2) (1/2) right (by norm_num) (input c)
  rw [parameter] at original
  change R₀ c (input c)-halfField = (d/2) • R₀ c halfField at original
  have inputAction : R₀ c (input c) = R₀ c (returnField c)-R₀ c (elementarySource c) := by
    rw [input, map_sub]
  rw [inputAction] at original
  have first : compensated c 1 = (1/2 : ℂ) • halfField + d⁻¹ • elementarySource c :=
    first_count_source c
  have applied := congrArg (R₀ c) first
  rw [map_add, map_smul, map_smul] at applied
  have live : d ≠ 0 := sub_ne_zero.mpr (star_ne_one c)
  change d • R₀ c (compensated c 1) = _
  calc
    _ = (d/2) • R₀ c halfField + R₀ c (elementarySource c) := by
      rw [applied, smul_add, smul_smul, smul_smul, mul_inv_cancel₀ live, one_smul]
      simp only [div_eq_mul_inv, one_mul]
    _ = R₀ c (returnField c)-halfField := by
      linear_combination (norm := module) -original
    _ = _ := by linear_combination (norm := module) (2 : ℂ) • first

private theorem actual_compact_R_exterior (c : BurnolCompletedMellinCoordinate) (value : BurnolL2)
    (compact : Cut value = value) (even : reflectL2 value = value) :
    quarterExterior (R₀ c value) = moment c value • quarterTail c := by
  have acted := actual_compact_R_rank_source (barC c) value compact even
  change R₀ c value = Cut (R₀ c value) +
    actualCompactTailCoefficient (barC c) value • quarterTail c at acted
  have pairing := (ContinuousLinearMap.adjoint_inner_left Q value (SingularCounting.powerL2 (barC c))).symm
  change inner ℂ (SingularCounting.powerL2 (barC c)) (Q value) = moment c value at pairing
  rw [actual_compact_tail_coefficient (barC c) value even, pairing] at acted
  change R₀ c value - Cut (R₀ c value) = _
  exact sub_eq_of_eq_add' acted

private theorem quarter_tail_cutoff (c : BurnolCompletedMellinCoordinate) : Cut (quarterTail c) = 0 := by
  let coord := star (barC c).value
  have right : 1/2 < coord.re := by
    simpa only [coord, Complex.star_def, Complex.conj_re] using (barC c).rightHalf
  let kernel := burnolRadiusMellinTailKernelL2 q (by norm_num) coord right
  have tail : quarterTail c = -(kernel+reflectL2 kernel) := rfl
  have raw : (kernel : ℝ → ℂ) =ᵐ[volume] burnolRadiusMellinTailKernelRaw q coord :=
    (burnolRadiusMellinTailKernelRaw_memLp (by norm_num) coord right).coeFn_toLp
  rw [tail]
  apply Lp.ext
  filter_upwards [originalPhysicalCutoff_coeFn q (-(kernel+reflectL2 kernel)),
    Lp.coeFn_neg (kernel+reflectL2 kernel), Lp.coeFn_add kernel (reflectL2 kernel),
    Lp.coeFn_compMeasurePreserving kernel negMeasurePreserving, raw,
    negMeasurePreserving.quasiMeasurePreserving.ae raw, Lp.coeFn_zero ℂ 2 volume]
      with x cut negative addition reflection here opposite empty
  rw [cut, empty]
  by_cases inside : x ∈ symmetricInterval q
  · have plus : ¬ x ∈ Ioi q := not_lt.mpr inside.2
    have minus : ¬ -x ∈ Ioi q := not_lt.mpr (neg_le.mp inside.1)
    have reflected : reflectL2 kernel x = kernel (-x) := reflection
    have other : kernel (-x) = burnolRadiusMellinTailKernelRaw q coord (-x) := opposite
    rw [indicator_of_mem inside, negative, Pi.neg_apply, addition, Pi.add_apply,
      reflected, here, other]
    simp only [burnolRadiusMellinTailKernelRaw, if_neg plus, if_neg minus, add_zero, neg_zero, Pi.zero_apply]
  · exact indicator_of_notMem inside _

private theorem elementary_exterior_price (c : BurnolCompletedMellinCoordinate) :
    quarterExterior (elementarySource c) = -(1/2 : ℂ) • quarterTail c := by
  have twice : barC (barC c) = c := by
    cases c
    simp only [OriginalPrimitiveRankBalance.conjugateCoordinate, star_star]
  have source := elementary_tail_source (barC c)
  rw [twice] at source
  change elementarySource c = _ - (1/2 : ℂ) • quarterTail c at source
  have seed : quarterExterior ConstantDual.seed = 0 := by
    change ConstantDual.seed - Cut ConstantDual.seed = 0
    rw [OriginalKSectorEulerMixedSource.actual_seed_source_qualification.1, sub_self]
  have tail : quarterExterior (quarterTail c) = quarterTail c := by
    change quarterTail c - Cut (quarterTail c) = _
    rw [quarter_tail_cutoff, sub_zero]
  rw [source, map_sub, map_smul, map_smul, seed, smul_zero, tail, zero_sub, neg_smul]

private theorem first_moment (c : BurnolCompletedMellinCoordinate) :
    moment c (compensated c 1) = countedJetPrice c 0 := by
  let d := star c.value-1
  have live : d ≠ 0 := sub_ne_zero.mpr (star_ne_one c)
  have initial : Cut (compensated c 1) = compensated c 1 := actual_compact c 1 Nat.one_pos
  have returned : Cut (returnField c) = returnField c := by
    change E (Q (returnField c)) = _
    rw [burnolQuarterRestriction_zeroExtension]
  have even : reflectL2 (returnField c) = returnField c := by
    change reflectL2 (burnolRadiusZeroExtension q (S (nativeSmooth c) : Hq)) =
      burnolRadiusZeroExtension q (S (nativeSmooth c) : Hq)
    rw [burnolRadiusZeroExtension_reflect, native_return_even]
  have empty : quarterExterior (compensated c 1) = 0 := by
    change compensated c 1 - Cut (compensated c 1) = 0
    rw [initial, sub_self]
  have acted := congrArg quarterExterior (actual_first_count_action c)
  rw [map_smul, map_add, map_sub, map_smul, map_smul,
    actual_compact_R_exterior c _ initial (compensated_even c 1),
    actual_compact_R_exterior c _ returned even, empty, smul_zero, sub_zero,
    elementary_exterior_price c] at acted
  have vanishes : (d * moment c (compensated c 1) - (moment c (returnField c)-d⁻¹)) • quarterTail c = 0 := by
    linear_combination (norm := module) acted
  have scalar : d * moment c (compensated c 1) = moment c (returnField c)-d⁻¹ :=
    sub_eq_zero.mp ((smul_eq_zero.mp vanishes).resolve_right (quarter_tail_ne_zero (barC c)))
  apply mul_left_cancel₀ live
  rw [scalar, countedJetPrice, first_coefficient, first_jet (star c.value) (star_ne_one c)]
  change moment c (returnField c)-d⁻¹ = d*(moment c (returnField c)*d⁻¹- (d⁻¹)^2)
  field_simp [live]

/-- The actual first cutoff contributes exactly the initial coefficient-and-jet price. -/
theorem actual_first_count_exterior (c : BurnolCompletedMellinCoordinate) :
    let acted := R₀ c (compensated c 1)
    acted - Cut acted = countedJetPrice c 0 • quarterTail c := by
  change quarterExterior (R₀ c (compensated c 1)) = _
  rw [actual_compact_R_exterior c _ (actual_compact c 1 Nat.one_pos) (compensated_even c 1), first_moment]

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
