import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Consumer

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalCanonicalNativeEulerGreen.Counted

open Complex Filter MeasureTheory BurnolPhysicalState
open OriginalRieszSource OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKFiniteOrderRelease.UnitPowerJordanSource OriginalKSourceResolventReconstruction
open OriginalKCoefficientBFiniteAction
open OriginalKElementaryArithmeticAction
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Floor
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.Compact
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.CompactPaired
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Graph.OriginalK
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open scoped Topology InnerProductSpace

open private returned_euler mean_ward from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeEulerGreen.Green
open private native_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Boundary.NativeSmooth
open private constant_euler from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.SameNArithmeticGreenResolvent
open private reverse_resolvent from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.UnitResolvent

local notation "q" => (1/4 : ℝ)
local notation "Hq" => BurnolQuarterIntervalL2
local notation "TD" => TemperedDistribution ℝ ℂ
local notation "E" => burnolQuarterZeroExtension
local notation "S" => burnolMeanZeroTruncatedFourier
local notation "C" => ConstantDual.seed
local notation "D" => DualSource.source
local notation "R" => fun c : BurnolCompletedMellinCoordinate =>
  burnolDirectRightResolventCLM (OriginalPrimitiveRankBalance.conjugateCoordinate c)
local notation "g" => nativeSmooth
local notation "β" => nativeBeta
local notation "γ" => nativeGamma
local notation "A" => fun c : BurnolCompletedMellinCoordinate => nativeGamma c - originCoefficient c
local notation "leading" => ForcingPrimitive.leadingCoefficient

private theorem return_velocity (c : BurnolCompletedMellinCoordinate) :
    returnedEuler (g c) =
      -(rate c) • S (g c) + β c • Response.u - A c • Response.v := by
  have ward := mean_ward (g c) (nativeEuler c) (β c) (native_euler c)
  have response : Response.eta = Response.u - S Response.v := Response.u_equation.symm
  rw [response, nativeEuler] at ward
  simp only [map_add, map_sub, map_smul, show S Response.u = Response.v from rfl] at ward
  linear_combination (norm := module) ward

private theorem corrected_return_euler (c : BurnolCompletedMellinCoordinate) :
    GapEuler.euler ((E (S (g c) : Hq) - γ c • C : BurnolL2) : TD) +
      sourceRate c • ((E (S (g c) : Hq) - γ c • C : BurnolL2) : TD) =
    ((β c • Response.wholeU - A c • Response.wholeV +
      (γ c * (1 - star c.value)) • C : BurnolL2) : TD) := by
  have actual := returned_euler (g c) (native_even c)
  rw [return_velocity, ← show γ c = burnolMeanZeroFourierRaw (g c) q from rfl] at actual
  change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 _) +
    sourceRate c • Lp.toTemperedDistributionCLM ℂ volume 2 _ =
      Lp.toTemperedDistributionCLM ℂ volume 2 _
  simp only [map_add, map_sub, map_smul, Lp.toTemperedDistributionCLM_apply]
  rw [actual, constant_euler]
  simp only [Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul,
    ← Lp.toTemperedDistributionCLM_apply, map_add, map_sub, map_smul]
  unfold rate sourceRate
  change _ = β c • Lp.toTemperedDistributionCLM ℂ volume 2 (E (Response.u : Hq)) -
    A c • Lp.toTemperedDistributionCLM ℂ volume 2 (E (Response.v : Hq)) +
      (γ c * (1 - star c.value)) • Lp.toTemperedDistributionCLM ℂ volume 2 C
  module

private theorem resolve_euler (c : BurnolCompletedMellinCoordinate) (value drive : BurnolL2)
    (equation : GapEuler.euler (value : TD) + sourceRate c • (value : TD) = (drive : TD)) :
    value = (-1/2 : ℂ) • R c drive := by
  have acted := sourceResolvent_euler c drive
  change GapEuler.euler (R c drive : TD) + sourceRate c • (R c drive : TD) =
    -(2 : ℂ) • (drive : TD) at acted
  have law : GapEuler.euler ((value + (1/2 : ℂ) • R c drive : BurnolL2) : TD) +
      sourceRate c • ((value + (1/2 : ℂ) • R c drive : BurnolL2) : TD) = 0 := by
    change GapEuler.euler (Lp.toTemperedDistributionCLM ℂ volume 2 _) +
      sourceRate c • Lp.toTemperedDistributionCLM ℂ volume 2 _ = 0
    simp only [map_add, map_smul, Lp.toTemperedDistributionCLM_apply]
    linear_combination (norm := module) equation + (1/2 : ℂ) • acted
  have positive : 0 < (sourceRate c).re := by
    simp only [sourceRate, sub_re, star_def, conj_re]
    norm_num
    linarith [c.rightHalf]
  have gone := homogeneous_L2_unique (sourceRate c) positive _ law
  linear_combination (norm := module) gone

/-- The full unit factor acts on the actual seed and on its counted value. -/
def unitFactor (c : BurnolCompletedMellinCoordinate) (value : BurnolL2) : BurnolL2 :=
  value - ((1-star c.value)/2) • R c value

private theorem return_source (c : BurnolCompletedMellinCoordinate) :
    E (S (g c) : Hq) = γ c • unitFactor c C -
      (1/2 : ℂ) • R c (β c • Response.wholeU - A c • Response.wholeV) := by
  have actual := resolve_euler c _ _ (corrected_return_euler c)
  rw [map_add, map_smul] at actual
  unfold unitFactor
  linear_combination (norm := module) actual

/-- The counted floor uses the complete return and the original elementary source. -/
def input (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  E (S (g c) : Hq) - elementarySource c

private theorem input_equation (c : BurnolCompletedMellinCoordinate) :
    input c = A c • unitFactor c C -
      (1/2 : ℂ) • R c (β c • Response.wholeU - A c • Response.wholeV) := by
  have unit : elementarySource c = originCoefficient c • unitFactor c C :=
    (elementary_unit_resolvent c).symm
  rw [input, return_source, unit]
  module

/-- The original same N action transports the complete response before taking limits. -/
theorem actual_finite_floor_action (c : BurnolCompletedMellinCoordinate) (N : Nat) :
    D N (input c) = A c • unitFactor c (D N C) -
      (1/2 : ℂ) • R c (β c • D N Response.wholeU - A c • D N Response.wholeV) := by
  let count := (CountingDual.sourceCLM N).adjoint
  have commute (value : BurnolL2) : count (R c value) = R c (count value) := by
    change (CountingDual.sourceCLM N).adjoint (sourceResolvent c value) =
      sourceResolvent c ((CountingDual.sourceCLM N).adjoint value)
    simpa only [CountingDual.dual_eq_adjoint] using reverse_resolvent N c value
  simp only [CountingDual.dual_eq_adjoint]
  change count (input c) = A c • unitFactor c (count C) -
    (1/2 : ℂ) • R c (β c • count Response.wholeU - A c • count Response.wholeV)
  simp only [input_equation, unitFactor, map_sub count, map_smul count, commute]

theorem actual_floor_from_count (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    Tendsto (fun N => D N (input c)) atTop (𝓝 (fullFloorValue c zero)) := by
  have source : input c = leading c • E (S (logBFirst c 0) : Hq) -
      E (S (burnolRieszSingleFourierSource c) : Hq) - elementarySource c := by
    simp only [input, nativeSmooth, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul]
  have acted := (((actual_log_return_reverse c).const_smul (leading c)).sub
    (ReturnCounting.finite_tendsto c)).sub (elementary_reverse_tendsto c zero)
  change Tendsto (fun N => leading c • D N (E (S (logBFirst c 0) : Hq)) -
    D N (E (S (burnolRieszSingleFourierSource c) : Hq)) - D N (elementarySource c))
    atTop (𝓝 (leading c • poissonPair (logProgramme c) - ReturnCounting.value c -
      elementaryReverseSource c zero)) at acted
  have complete : leading c • poissonPair (logProgramme c) - ReturnCounting.value c -
      elementaryReverseSource c zero = fullFloorValue c zero := by
    rw [actual_original_C_position_count c zero, elementaryReverseSource]
    module
  rw [complete] at acted
  apply acted.congr'
  filter_upwards with N
  simp only [source, CountingDual.dual_eq_adjoint, map_sub, map_smul]

/-- The full original counted floor is generated by the original R response and complete Unit. -/
def floorFromResponses (c : BurnolCompletedMellinCoordinate) : BurnolL2 :=
  A c • unitFactor c ConstantDual.value -
    (1/2 : ℂ) • R c (β c • ResponseCounting.value false - A c • ResponseCounting.value true)

theorem actual_counted_floor_response (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) : fullFloorValue c zero = floorFromResponses c := by
  have count := ConstantDual.original_tendsto
  have acted := ((R c).continuous.tendsto ConstantDual.value).comp count
  have unit := count.sub (acted.const_smul ((1-star c.value)/2))
  have u := ResponseCounting.finite_tendsto false
  have v := ResponseCounting.finite_tendsto true
  have drive := (u.const_smul (β c)).sub (v.const_smul (A c))
  have response := ((R c).continuous.tendsto _).comp drive
  have all := (unit.const_smul (A c)).sub (response.const_smul (1/2 : ℂ))
  apply tendsto_nhds_unique (actual_floor_from_count c zero)
  apply all.congr'
  filter_upwards with N
  exact (actual_finite_floor_action c N).symm

/-- The independent original K counting consumer reads the full generated floor. -/
theorem actual_original_counted_K_response (c : BurnolCompletedMellinCoordinate)
    (zero : riemannZeta c.value = 0) :
    fourierL2 (KCountingGram.value c) = -burnolTateReciprocalL2 (floorFromResponses c) +
      leading c • fourierL2 (logProgramme c) - CountingDual.value c := by
  rw [← actual_counted_floor_response c zero]
  exact actual_original_K_counted_field c zero

end OriginalCanonicalNativeEulerGreen.Counted
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
