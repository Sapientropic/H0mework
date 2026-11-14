import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.CoefficientJet.Cell
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex MeasureTheory Set BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth

open private compensated_even difference_support from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private moment from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private scaleWeight_cpow scaleWeight_integrable from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.SourceJet

local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R₀" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "tailCoeff" => fun c n =>
  OriginalKCompactAdjointRSource.actualCompactTailCoefficient (barC c) (difference c n)
local notation "m" => fun c => moment c (E (S (nativeSmooth c) : Hq))

private theorem star_ne_one (c : BurnolCompletedMellinCoordinate) : star c.value ≠ 1 := by
  intro equal
  have contradiction := congrArg Complex.re equal
  simp only [Complex.star_def, Complex.conj_re, Complex.one_re] at contradiction
  exact c.belowOne.ne contradiction

/-- The actual compact source moment and the first coefficient jet form the cumulative cell price. -/
def countedJetPrice (c : BurnolCompletedMellinCoordinate) (n : Nat) : ℂ :=
  m c * CoefficientJet.finite n (star c.value) + CoefficientJet.jet 1 n (star c.value)

/-- The exterior price emitted by the original R action is the adjacent price of the same cutoff. -/
theorem actual_tail_cell_jet (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    tailCoeff c (n+1) = countedJetPrice c (n+1) - countedJetPrice c n := by
  let s := star c.value
  let a : ℝ := (n+1 : ℕ)
  let b : ℝ := (n+1+1 : ℕ)
  let phase := fun x : ℝ => (x : ℂ)^(-s)
  let logWeight := fun x : ℝ => phase x * (Real.log x : ℂ)
  have lower : 1 ≤ a := by dsimp only [a]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have ordered : a ≤ b := by dsimp only [a,b]; exact_mod_cast Nat.le_succ (n+1)
  have segment := Ioc_subset_Ioc lower (le_refl b)
  have term (x : ℝ) (member : x ∈ Ioc a b) (j : Nat) :
      SourceJet.scaleWeight s j x = (-(Real.log x : ℂ))^j * phase x := by
    have live : 0 < x := zero_lt_one.trans_le (lower.trans member.1.le)
    rw [scaleWeight_cpow s j x live, Complex.ofReal_log live.le]
  have plain : IntegrableOn phase (Ioc a b) := by
    apply ((scaleWeight_integrable s 0 b).mono_set segment).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x member
    simp only [term x member 0, pow_zero, one_mul]
  have logarithmic : IntegrableOn logWeight (Ioc a b) := by
    apply ((scaleWeight_integrable s 1 b).mono_set segment).neg.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x member
    rw [Pi.neg_apply, term x member 1, pow_one, neg_mul, neg_neg, mul_comm]
  have segmentLog :
      (∫ x : ℝ in Ioc a b, SourceJet.scaleWeight s 1 x) = -(∫ x : ℝ in Ioc a b, logWeight x) := by
    rw [← integral_neg]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x member
    rw [term x member 1, pow_one, neg_mul, mul_comm (Real.log x : ℂ)]
  have error :
      (∫ x : ℝ in Ioc a b, phase x * ((Real.log x : ℂ)-(Real.log a : ℂ))) =
        (∫ x : ℝ in Ioc a b, logWeight x) -
          (∫ x : ℝ in Ioc a b, phase x) * (Real.log a : ℂ) := by
    simp_rw [mul_sub]
    rw [integral_sub logarithmic (plain.mul_const _), integral_mul_const]
  have first := CoefficientJet.actual_cell_jet s (star_ne_one c) 1 n
  have realCast : (((n+1 : ℕ) : ℂ)) = (a : ℂ) := by simp [a]
  rw [pow_one, realCast, ← Complex.ofReal_log (zero_le_one.trans lower)] at first
  change CoefficientJet.jet 1 (n+1) s - CoefficientJet.jet 1 n s =
    -(Real.log a : ℂ) * phase a - (∫ x : ℝ in Ioc a b, SourceJet.scaleWeight s 1 x) at first
  rw [segmentLog] at first
  have increment := actual_coefficient_step c (n+1) (Nat.succ_pos n)
  rw [intervalIntegral.integral_of_le ordered] at increment
  change coefficientStep c (n+1) = phase a - (∫ x : ℝ in Ioc a b, phase x) at increment
  have action := actual_tail_increment c (n+1) (Nat.succ_pos n)
  change tailCoeff c (n+1) = coefficientStep c (n+1) * (m c-(Real.log a : ℂ)) +
    (∫ x : ℝ in Ioc a b, phase x * ((Real.log x : ℂ)-(Real.log a : ℂ))) at action
  rw [error] at action
  have coefficient : coefficientStep c (n+1) = CoefficientJet.finite (n+1) s - CoefficientJet.finite n s := rfl
  have total : countedJetPrice c (n+1) - countedJetPrice c n =
      m c * coefficientStep c (n+1) + (CoefficientJet.jet 1 (n+1) s - CoefficientJet.jet 1 n s) := by
    rw [coefficient]
    unfold countedJetPrice
    change m c * CoefficientJet.finite (n+1) s + CoefficientJet.jet 1 (n+1) s -
      (m c * CoefficientJet.finite n s + CoefficientJet.jet 1 n s) = _
    ring
  rw [total]
  linear_combination action - (Real.log a : ℂ)*increment - first

private theorem accumulate_cells (c : BurnolCompletedMellinCoordinate) {H : Type*} [AddCommGroup H]
    [Module ℂ H] (out : BurnolL2 →ₗ[ℂ] H) (direction : H)
    (cell : ∀ n : Nat, out (difference c (n+1)) =
      (countedJetPrice c (n+1)-countedJetPrice c n) • direction) (n : Nat) :
    out (compensated c (n+1)-compensated c 1) =
      (countedJetPrice c n-countedJetPrice c 0) • direction := by
  induction n with
  | zero => simp only [Nat.zero_add, sub_self, map_zero, zero_smul]
  | succ n earlier =>
    have next : compensated c (n+1+1)-compensated c 1 =
        difference c (n+1)+(compensated c (n+1)-compensated c 1) := by
      rw [difference]
      abel
    rw [next, map_add, cell n, earlier, ← add_smul]
    congr 1
    ring

/-- The original compact increments accumulate in the original physical K direction. -/
theorem actual_counted_jet_action (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    P (R₀ c (compensated c (n+1)-compensated c 1)) =
      -(2*(countedJetPrice c n-countedJetPrice c 0)) • K c := by
  let out := ((P).comp (R₀ c)).toLinearMap
  have cell (j : Nat) : out (difference c (j+1)) =
      (countedJetPrice c (j+1)-countedJetPrice c j) • ((-2 : ℂ) • K c) := by
    change P (R₀ c (difference c (j+1))) = _
    rw [actual_resolvent_projection c (j+1) (Nat.succ_pos j), actual_tail_cell_jet, smul_smul]
    congr 1
    ring
  have price := accumulate_cells c out ((-2 : ℂ) • K c) cell n
  change P (R₀ c (compensated c (n+1)-compensated c 1)) = _ at price
  rw [price, smul_smul]
  congr 1
  ring

private def quarterExterior : BurnolL2 →L[ℂ] BurnolL2 :=
  ContinuousLinearMap.id ℂ BurnolL2 - (E).comp burnolQuarterRestriction

private def quarterTail (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  burnolRadiusNormalizedUnitTail (barC c) (1/4) (by norm_num)

/-- The exterior of the entire acted count uses the same accumulated jet before physical projection. -/
theorem actual_counted_jet_exterior (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    let acted := R₀ c (compensated c (n+1)-compensated c 1)
    acted - originalPhysicalCutoff (1/4) acted =
      (countedJetPrice c n-countedJetPrice c 0) • quarterTail c := by
  let out := (quarterExterior.comp (R₀ c)).toLinearMap
  have cell (j : Nat) : out (difference c (j+1)) =
      (countedJetPrice c (j+1)-countedJetPrice c j) • quarterTail c := by
    have even : reflectL2 (difference c (j+1)) = difference c (j+1) := by
      rw [difference, map_sub, compensated_even, compensated_even]
    have rank := OriginalKCompactAdjointRSource.actual_compact_R_rank_source (barC c) (difference c (j+1))
      (difference_support c (j+1) (Nat.succ_pos j)) even
    change R₀ c (difference c (j+1)) =
      originalPhysicalCutoff (1/4) (R₀ c (difference c (j+1))) + tailCoeff c (j+1) • quarterTail c at rank
    change R₀ c (difference c (j+1)) - originalPhysicalCutoff (1/4) (R₀ c (difference c (j+1))) = _
    rw [← actual_tail_cell_jet c j]
    exact (eq_sub_of_add_eq ((add_comm _ _).trans rank.symm)).symm
  exact accumulate_cells c out (quarterTail c) cell n

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
