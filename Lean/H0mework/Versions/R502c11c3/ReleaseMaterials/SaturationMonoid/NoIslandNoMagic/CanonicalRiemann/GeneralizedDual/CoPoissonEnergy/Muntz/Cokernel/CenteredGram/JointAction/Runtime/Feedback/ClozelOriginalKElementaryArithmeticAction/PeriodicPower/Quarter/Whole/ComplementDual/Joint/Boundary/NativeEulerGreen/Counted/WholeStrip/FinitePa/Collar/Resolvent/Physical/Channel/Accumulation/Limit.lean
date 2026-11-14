import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation

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
open scoped InnerProductSpace Topology

open private moment from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel
open private star_ne_one quarterExterior quarterTail from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent.Physical.Channel.Accumulation

local notation "P" => burnolEvenAmbientProjection
local notation "K" => burnolCompletedMellinRieszVector
local notation "barC" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "R₀" => fun c => burnolDirectRightResolventCLM (barC c)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "m" => fun c => moment c (E (S (nativeSmooth c) : Hq))

private theorem star_positive (c : BurnolCompletedMellinCoordinate) : 0 < (star c.value).re := by
  simp only [Complex.star_def, Complex.conj_re]
  linarith [c.rightHalf]

private theorem coefficient_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n => CoefficientJet.finite n (star c.value)) atTop (𝓝 (riemannZeta (star c.value))) :=
  CoefficientJet.locally_uniform.tendsto_at ⟨star_positive c, star_ne_one c⟩

private theorem price_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (countedJetPrice c) atTop
      (𝓝 (m c * riemannZeta (star c.value) + CoefficientJet.zetaJet 1 (star c.value))) :=
  ((coefficient_limit c).const_mul (m c)).add
    (CoefficientJet.jet_tendsto (star c.value) (star_positive c) (star_ne_one c) 1)

private theorem whole_limit (c : BurnolCompletedMellinCoordinate) :
    Tendsto (fun n : Nat => compensated c (n+1)) atTop
      (𝓝 (floorFromResponses c + riemannZeta (star c.value) • elementarySource c)) := by
  have counts := (actual_floor_tendsto c).comp (tendsto_add_atTop_nat 1)
  have compensation := (coefficient_limit c).smul_const (elementarySource c)
  exact counts.add compensation

/-- The total original action consumes the same entire finite count and its actual first jet. -/
theorem actual_counted_jet_limit (c : BurnolCompletedMellinCoordinate) :
    P (R₀ c (floorFromResponses c + riemannZeta (star c.value) • elementarySource c-compensated c 1)) =
      -(2*(m c * riemannZeta (star c.value) + CoefficientJet.zetaJet 1 (star c.value)-countedJetPrice c 0)) • K c := by
  let act : BurnolL2 →L[ℂ] BurnolPaAmbientCarrier := (P).comp (R₀ c)
  have original := (act.continuous.tendsto _).comp ((whole_limit c).sub
    (tendsto_const_nhds (x := compensated c 1)))
  have generated := (((price_limit c).sub (tendsto_const_nhds (x := countedJetPrice c 0))).const_mul
    (2 : ℂ)).neg.smul_const (K c)
  apply tendsto_nhds_unique original
  exact generated.congr' (Eventually.of_forall fun n => (actual_counted_jet_action c n).symm)

/-- The same jet prices the complete exterior of the acted original limit. -/
theorem actual_counted_jet_limit_exterior (c : BurnolCompletedMellinCoordinate) :
    let acted := R₀ c (floorFromResponses c + riemannZeta (star c.value) • elementarySource c-compensated c 1)
    acted - originalPhysicalCutoff (1/4) acted =
      (m c * riemannZeta (star c.value) + CoefficientJet.zetaJet 1 (star c.value)-countedJetPrice c 0) • quarterTail c := by
  let act := quarterExterior.comp (R₀ c)
  have original := (act.continuous.tendsto _).comp ((whole_limit c).sub
    (tendsto_const_nhds (x := compensated c 1)))
  have generated := ((price_limit c).sub (tendsto_const_nhds (x := countedJetPrice c 0))).smul_const (quarterTail c)
  apply tendsto_nhds_unique original
  exact generated.congr' (Eventually.of_forall fun n => (actual_counted_jet_exterior c n).symm)

theorem actual_zero_counted_jet_action (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    P (R₀ c (floorFromResponses c-compensated c 1)) =
      -(2*(CoefficientJet.zetaJet 1 (star c.value)-countedJetPrice c 0)) • K c := by
  have conjugate : riemannZeta (star c.value) = 0 := by
    simpa only [Complex.star_def, zero, map_zero] using riemannZeta_conj c.value
  simpa only [conjugate, zero_smul, add_zero, mul_zero, zero_add] using actual_counted_jet_limit c

/-- The independent original K reads the accumulated action in the same physical space. -/
theorem actual_zero_counted_jet_K (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    inner ℂ (K c : BurnolL2) (R₀ c (floorFromResponses c-compensated c 1)) =
      -(2*(CoefficientJet.zetaJet 1 (star c.value)-countedJetPrice c 0)) * inner ℂ (K c) (K c) := by
  have projection := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (K c)
    (R₀ c (floorFromResponses c-compensated c 1))
  change inner ℂ (K c) (P (R₀ c (floorFromResponses c-compensated c 1))) = _ at projection
  rw [← projection, actual_zero_counted_jet_action c zero]
  exact inner_smul_right (K c) (K c) _

end OriginalCanonicalNativeEulerGreen.Counted.WholeStrip.FinitePa.Collar.Resolvent
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
