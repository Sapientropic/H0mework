import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.DirectedReadback
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondConductorAction
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.WidePositionGapAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock

open BurnolPhysicalState Filter
open scoped InnerProductSpace Topology

namespace SingleSlot

open private literal_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

namespace Gram
export SourceGeneratedFiniteGram (Coordinates)
export SourceGeneratedFiniteGram.Projection (rhs)
export SourceGeneratedFiniteGram.PrefixReadback (inverse inverse_tendsto_finset)
end Gram

local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "K" => burnolCompletedMellinRieszVector

local instance : InnerProductSpace ℂ Ambient :=
  WithLp.instProdInnerProductSpace (𝕜 := ℂ) (E := Base) (F := SecondSlots)
local instance wholeInner : InnerProductSpace ℂ Whole := Submodule.innerProductSpace carrier

private def fullRead : Ambient →L[ℂ] BurnolL2 :=
  LogStock.field.comp (WithLp.fstL 2 ℂ Base SecondSlots)

/-- Intersect the existing second conductor graph with its source's actual wider position gap. -/
def unitGap : Submodule ℂ Ambient :=
  carrier ⊓ (locallyConstantFace 1).comap fullRead.toLinearMap

abbrev Wide := ↥unitGap

local instance wideInner : InnerProductSpace ℂ Wide := Submodule.innerProductSpace unitGap

private theorem unit_gap_closed : IsClosed (unitGap : Set Ambient) :=
  carrier_closed.inter ((locallyConstantFace_isClosed 1).preimage fullRead.continuous)

instance : CompleteSpace Wide := unit_gap_closed.isComplete.completeSpace_coe

/-- Keep the existing stock and read its original fields through the inclusion. -/
def toWhole : Wide →L[ℂ] Whole :=
  unitGap.subtypeL.codRestrict carrier fun x => x.property.1

/-- The original Γ² write preserves the restricted stock by its actual raw R action. -/
def advanceWide (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) :
    Wide →L[ℂ] Wide :=
  (carrier.subtypeL.comp ((advance c zero).comp toWhole)).codRestrict unitGap fun x => by
    refine ⟨(advance c zero (toWhole x)).property, ?_⟩
    change LogStock.field (LogStock.advance c (base (toWhole x))) ∈ locallyConstantFace 1
    rw [LogStock.advance_field]
    exact WidePositionGap.original_R_preserves_position_radius c zero_lt_one _ x.property.2

/-- Only the current physical projection is observed. -/
def observe : Wide →L[ℂ] BurnolL2 := (P).comp (fullRead.comp unitGap.subtypeL)

theorem observe_injective : Function.Injective observe := by
  intro x y same
  suffices equal : toWhole x = toWhole y by
    exact Subtype.ext (congrArg (fun w : Whole => (w : Ambient)) equal)
  apply base_injective
  apply LogStock.field_injective
  exact WidePositionGap.physical_read_eq_of_unit_gap x.property.2 y.property.2
    (mem_evenL2ClosedFace_iff.mp (LogStock.field_mem (base (toWhole x))).2)
    (mem_evenL2ClosedFace_iff.mp (LogStock.field_mem (base (toWhole y))).2) same

abbrev Probe := {test : BurnolCompletedMellinCoordinate // test.value.re = 3/4}
local instance : DecidableEq Probe := Classical.decEq _

private def ambientCotest (test : Probe) : BurnolL2 :=
  ContinuousLinearMap.adjoint (𝕜 := ℂ) (P) (K test.1 : BurnolL2)

private def baseCotest (test : Probe) : Base :=
  LogStock.carrier.orthogonalProjectionOnto (WithLp.toLp 2 (ambientCotest test, (0 : LogStock.LogSlots)))

/-- Restrict the original physical adjoint cotest through the two closed graph projections. -/
def covector (test : Probe) : Wide :=
  unitGap.orthogonalProjectionOnto (WithLp.toLp 2 (baseCotest test, (0 : SecondSlots)))

theorem covector_read (test : Probe) (x : Wide) :
    inner ℂ (covector test) x = inner ℂ (K test.1 : BurnolL2) (observe x) := by
  let basis := base (toWhole x)
  have first := unitGap.inner_orthogonalProjectionOnto_eq_of_mem_right x
    (WithLp.toLp 2 (baseCotest test, (0 : SecondSlots)))
  change inner ℂ (covector test) x =
    inner ℂ (WithLp.toLp 2 (baseCotest test, (0 : SecondSlots))) (x : Ambient) at first
  have second := LogStock.carrier.inner_orthogonalProjectionOnto_eq_of_mem_right basis
    (WithLp.toLp 2 (ambientCotest test, (0 : LogStock.LogSlots)))
  change inner ℂ (baseCotest test) basis =
    inner ℂ (WithLp.toLp 2 (ambientCotest test, (0 : LogStock.LogSlots))) (basis : LogStock.AmbientStock)
    at second
  rw [first, WithLp.prod_inner_apply]
  change inner ℂ (baseCotest test) basis + inner ℂ (0 : SecondSlots) x.val.snd = _
  rw [inner_zero_left, add_zero, second, WithLp.prod_inner_apply]
  change inner ℂ (ambientCotest test) (LogStock.field basis) +
    inner ℂ (0 : LogStock.LogSlots) basis.val.snd = _
  rw [inner_zero_left, add_zero]
  exact ContinuousLinearMap.adjoint_inner_left (𝕜 := ℂ) (E := BurnolL2) (F := BurnolL2)
    (P) (LogStock.field basis) (K test.1 : BurnolL2)

private theorem original_K_separates (p : BurnolPaAmbientCarrier)
    (silent : ∀ test : Probe, inner ℂ (K test.1 : BurnolL2) (p : BurnolL2) = 0) :
    (p : BurnolL2) = 0 := by
  apply actual_mellin_separates_positionGap _ p.property.1.1
    (mem_evenL2ClosedFace_iff.mp p.property.2)
  intro test line
  have restrict := congrArg (fun f : BurnolPaAmbientCarrier →L[ℂ] ℂ => f p)
    (burnolAmbientCompletedMellinEvaluator_restrict test)
  change burnolAmbientCompletedMellinEvaluator test (p : BurnolL2) =
    burnolCompletedMellinEvaluator test p at restrict
  rw [restrict, ← burnolCompletedMellinRieszVector_readback]
  exact silent ⟨test,line⟩

theorem covectors_separate (x : Wide)
    (silent : ∀ test : Probe, inner ℂ (covector test) x = 0) : x = 0 := by
  apply observe_injective
  rw [map_zero]
  let p := burnolEvenAmbientProjection (fullRead (x : Ambient))
  change (p : BurnolL2) = 0
  apply original_K_separates p
  intro test
  exact (covector_read test x).symm.trans (silent test)

def priceInverse (tests : Finset Probe) (prices : Gram.Coordinates tests) : Wide :=
  Gram.inverse (fun i : tests => covector i) prices

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "actual" => actualAt observation nontrivial half depth

/-- The new restriction carries the same stored fields at the same literal ordinal. -/
def actualWide (ordinal : Nat) : Wide :=
  ⟨(actual ordinal : Ambient), (actual ordinal).property,
    WidePositionGap.actual_division_unit_position_gap observation nontrivial half depth ordinal⟩

local notation "stock" => actualWide observation nontrivial half depth

theorem actual_wide_next (ordinal : Nat) :
    advanceWide c observation.mathlibZero (stock ordinal) = stock (ordinal+1) :=
  Subtype.ext (congrArg (fun w : Whole => (w : Ambient))
    (actual_second_graph_next observation nontrivial half depth ordinal))

theorem actual_observation (ordinal : Nat) : observe (stock ordinal) = (input ordinal).1 :=
  congrArg Prod.fst (literal_split observation nontrivial half depth ordinal)

/-- Read the independent original K directly at the current literal physical slot. -/
def recorded (ordinal : Nat) (tests : Finset Probe) : Gram.Coordinates tests :=
  WithLp.toLp 2 fun i : tests => inner ℂ (K (i : Probe).1 : BurnolL2) (input ordinal).1

theorem actual_recorded (ordinal : Nat) (tests : Finset Probe) :
    recorded observation nontrivial half depth ordinal tests =
      Gram.rhs (fun i : tests => covector i) (stock ordinal) := by
  ext i
  change inner ℂ (K (i : Probe).1 : BurnolL2) (input ordinal).1 =
    inner ℂ (covector i) (stock ordinal)
  rw [covector_read, actual_observation]

/-- Finite prices from the same physical slot recover the complete current and native next graphs. -/
theorem actual_single_slot_price_recovery (ordinal : Nat) :
    let fit := fun tests : Finset Probe => priceInverse tests (recorded observation nontrivial half depth ordinal tests);
    Tendsto fit atTop (𝓝 (stock ordinal)) ∧
      Tendsto (fun tests => advanceWide c observation.mathlibZero (fit tests)) atTop (𝓝 (stock (ordinal+1))) := by
  let fit := fun tests : Finset Probe => priceInverse tests (recorded observation nontrivial half depth ordinal tests)
  have direct := @Gram.inverse_tendsto_finset Wide Probe
    (inferInstanceAs (NormedAddCommGroup Wide)) wideInner
    (inferInstanceAs (CompleteSpace Wide)) (inferInstanceAs (DecidableEq Probe))
    covector covectors_separate (stock ordinal)
  have recovery : Tendsto fit atTop (𝓝 (stock ordinal)) := by
    simpa only [fit, priceInverse, actual_recorded] using direct
  have next := ((advanceWide c observation.mathlibZero).continuous.tendsto (stock ordinal)).comp recovery
  rw [actual_wide_next] at next
  exact ⟨recovery, next⟩

/-- Every actual physical slot pays a nonzero price against an independent original K. -/
theorem actual_single_slot_price_nonzero (ordinal : Nat) :
    ∃ test : Probe, inner ℂ (K test.1 : BurnolL2) (input ordinal).1 ≠ 0 := by
  by_contra! silent
  apply WidePositionGap.actual_division_physical_ne_zero observation nontrivial half depth ordinal
  let p := burnolEvenAmbientProjection (raw ordinal)
  have read : (p : BurnolL2) = (input ordinal).1 :=
    congrArg Prod.fst (literal_split observation nontrivial half depth ordinal)
  rw [← read]
  exact original_K_separates p fun test => by rw [read]; exact silent test

end SingleSlot
end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
