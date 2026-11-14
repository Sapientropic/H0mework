import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit.Origin
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedSchur.LeadingJet

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent

open Complex Filter BurnolPhysicalState OriginalPaPhysicalGreen
open OriginalRieszFinitePairing.CoPoisson.Ward.CountedSchur OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Source
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open OriginalKCoupledPhysicalRFieldSource OriginalKCompactAdjointRSource OriginalKQuarterTailPhysicalSource
open scoped InnerProductSpace Topology

open private compensated_even conjugate_twice quarter_unit_cancellation from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical
open private moment from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private star_ne_one quarterExterior quarterTail from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation
open private price_limit whole_limit from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation.Limit
open private quarter_tail_ne_zero from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.ReverseSourceRTail

local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector
local notation "G" => OriginalRieszFiniteSynthesis.gapMeanVector
local notation "Cut" => originalPhysicalCutoff q
local notation "μ" => FiniteMobiusResolventFlux.actualMean
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R₀" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "completeCount" => fun c =>
  floorFromResponses c + riemannZeta (star (BurnolCompletedMellinCoordinate.value c)) • elementarySource c
local notation "wholePrice" => fun c =>
  moment c (E (S (nativeSmooth c) : Hq)) *
    riemannZeta (star (BurnolCompletedMellinCoordinate.value c)) +
    CoefficientJet.zetaJet 1 (star (BurnolCompletedMellinCoordinate.value c))

private theorem finite_count_mean (c : BurnolCompletedMellinCoordinate) (N : ℕ) (positive : 0 < N) :
    μ (compensated c N) = unitMean c := by
  have read (v : BurnolL2) : μ v = burnolQuarterMeanCoefficient (burnolQuarterRestriction v) := by
    change (((‖intervalConstant q‖ : ℂ)^2)⁻¹) * inner ℂ (intervalConstant q) (burnolQuarterRestriction v) =
      inner ℂ (intervalConstant q) (burnolQuarterRestriction v) / ((‖intervalConstant q‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.ofReal_pow]
    exact (mul_comm _ _).trans (div_eq_mul_inv _ _).symm
  rw [read, actual_compensated_mean c N positive]

/-- The original Unit stays in the complete count at its strong limit. -/
theorem actual_counted_unit_mean (c : BurnolCompletedMellinCoordinate) :
    μ (completeCount c) = unitMean c := by
  apply tendsto_nhds_unique (((μ).continuous.tendsto _).comp (whole_limit c))
  exact tendsto_const_nhds.congr' (Eventually.of_forall fun n =>
    (finite_count_mean c (n+1) (Nat.succ_pos n)).symm)

private theorem finite_R_exterior (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    quarterExterior (R₀ c (compensated c (n+1))) = countedJetPrice c n • quarterTail c := by
  have increment := actual_counted_jet_exterior c n
  change quarterExterior (R₀ c (compensated c (n+1)-compensated c 1)) = _ at increment
  have initial := actual_first_count_exterior c
  change quarterExterior (R₀ c (compensated c 1)) = _ at initial
  rw [map_sub, map_sub, initial] at increment
  linear_combination (norm := module) increment

private theorem unit_price (c : BurnolCompletedMellinCoordinate) (a : ℂ) :
    (1/2 : ℂ) * ((a * (((2*q : ℝ) : ℂ) * (q : ℂ)^(-(barC c).value)) - unitMean c) /
      ((barC c).value/2-1/2)) +
      (2 : ℂ) * a * star (burnolMellinGapMoment (actualStarSource (barC c)).value) =
    -(unitMean c/(star c.value-1)) := by
  let d := star c.value-1
  have live : d ≠ 0 := sub_ne_zero.mpr (star_ne_one c)
  have factor : (barC c).value/2-1/2 = d/2 := by
    change star c.value/2-1/2 = (star c.value-1)/2
    ring
  rw [sub_div, mul_sub, sub_add_eq_add_sub, quarter_unit_cancellation, zero_sub, factor]
  change -((1/2 : ℂ) * (unitMean c/(d/2))) = -(unitMean c/d)
  field_simp [live]

/-- Each actual whole cutoff supplies both the exterior and the original infinite physical projection. -/
theorem actual_compensated_R_fields (c : BurnolCompletedMellinCoordinate) (n : Nat) :
    let acted := R₀ c (compensated c (n+1))
    acted - Cut acted = countedJetPrice c n • quarterTail c ∧
    P acted = -(2*countedJetPrice c n) • K c + (-(unitMean c/(star c.value-1))) • G := by
  refine ⟨finite_R_exterior c n, ?_⟩
  let x := compensated c (n+1)
  have compact : Cut x = x := actual_compact c (n+1) (Nat.succ_pos n)
  have even : reflectL2 x = x := compensated_even c (n+1)
  have rank := actual_compact_R_rank_source (barC c) x compact even
  let coeff := actualCompactTailCoefficient (barC c) x
  change R₀ c x = Cut (R₀ c x) + coeff • quarterTail c at rank
  have exterior := finite_R_exterior c n
  change R₀ c x-Cut (R₀ c x) = countedJetPrice c n • quarterTail c at exterior
  have vanishes : (coeff-countedJetPrice c n) • quarterTail c = 0 := by
    linear_combination (norm := module) exterior - rank
  have price : actualCompactTailCoefficient (barC c) x = countedJetPrice c n :=
    sub_eq_zero.mp ((smul_eq_zero.mp vanishes).resolve_right (quarter_tail_ne_zero (barC c)))
  have projected := actual_compact_projected_R_source (barC c) x compact even
  change P (R₀ c x) = _
  change P (R₀ c x) = _ at projected
  rw [projected, actualCompactProjectedRField, price, finite_count_mean c (n+1) (Nat.succ_pos n),
    unit_price, conjugate_twice]

/-- The full acted limit has its absolute jet price, with the original Unit on the Pa face. -/
theorem actual_counted_R_fields (c : BurnolCompletedMellinCoordinate) :
    let acted := R₀ c (completeCount c)
    acted - Cut acted = wholePrice c • quarterTail c ∧
    P acted = -(2*wholePrice c) • K c + (-(unitMean c/(star c.value-1))) • G := by
  constructor
  · let exterior := quarterExterior.comp (R₀ c)
    apply tendsto_nhds_unique ((exterior.continuous.tendsto _).comp (whole_limit c))
    exact ((price_limit c).smul_const (quarterTail c)).congr' (Eventually.of_forall fun n =>
      (actual_compensated_R_fields c n).1.symm)
  · let physical := (P).comp (R₀ c)
    let unit : BurnolPaAmbientCarrier := (-(unitMean c/(star c.value-1))) • G
    have projected := (((price_limit c).const_mul (2 : ℂ)).neg.smul_const (K c)).add
      (tendsto_const_nhds (x := unit))
    apply tendsto_nhds_unique ((physical.continuous.tendsto _).comp (whole_limit c))
    exact projected.congr' (Eventually.of_forall fun n => (actual_compensated_R_fields c n).2.symm)

private theorem conjugate_zero_count (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    riemannZeta (star c.value) = 0 := by
  simpa only [Complex.star_def, zero, map_zero] using riemannZeta_conj c.value

/-- The independent original K reads the two actual components of the whole acted zero field. -/
theorem actual_zero_counted_R_K (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    inner ℂ (K c : BurnolL2) (R₀ c (floorFromResponses c)) =
      -(2*CoefficientJet.zetaJet 1 (star c.value))*inner ℂ (K c) (K c) -
        (unitMean c/(star c.value-1))*inner ℂ (K c) G := by
  have physical := (actual_counted_R_fields c).2
  simp only [conjugate_zero_count c zero, zero_smul, add_zero, mul_zero, zero_add] at physical
  have read := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K c) (R₀ c (floorFromResponses c))
  change inner ℂ (K c) (P (R₀ c (floorFromResponses c))) = _ at read
  rw [← read, physical, inner_add_right,
    inner_smul_right (K c) (K c) (-(2*CoefficientJet.zetaJet 1 (star c.value))),
    inner_smul_right (K c) G (-(unitMean c/(star c.value-1)))]
  ring

/-- At a simple original Xi zero the whole exterior reads the actual leading jet. -/
theorem actual_simple_counted_R_exterior (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) (simple : LeadingJet.multiplicity c = 1) :
    let acted := R₀ c (floorFromResponses c)
    acted - Cut acted = LeadingJet.leading c • quarterTail c := by
  have exterior := (actual_counted_R_fields c).1
  have price := LeadingJet.top_source c
  rw [simple] at price
  simpa only [conjugate_zero_count c zero, zero_smul, add_zero, mul_zero, zero_add, price] using exterior

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
