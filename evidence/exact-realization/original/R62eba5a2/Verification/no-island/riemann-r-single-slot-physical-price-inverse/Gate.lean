import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.RelationInventory
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option maxErrors 1
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace SingleSlotPhysicalPriceCertificate

open BurnolPhysicalState Filter
open OriginalKFiniteOrderRelease.PositionGapCayley.WidePositionGap
open OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor (branchSecondAt)
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory (actual_relation_stock_next)
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKDirectRCofinalDivision.DirectRDivisionControls (actual_division_action_same_root)
open scoped InnerProductSpace Topology

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "stock" => actualWide observation nontrivial half depth
local notation "actual" => actualAt observation nontrivial half depth
local notation "second" => branchSecondAt observation nontrivial half depth
local notation "prices" => recorded observation nontrivial half depth

run_cmd IO.eprintln "CP577_CONTROL + original_current_physical_projection_is_faithful_on_the_unit_gap_stock"
theorem original_current_physical_projection_is_faithful_on_the_unit_gap_stock (ordinal : Nat) :
    raw ordinal ∈ locallyConstantFace 1 ∧
    Function.Injective observe ∧ observe (stock ordinal) = (input ordinal).1 :=
  ⟨actual_division_unit_position_gap observation nontrivial half depth ordinal,
    observe_injective, actual_observation observation nontrivial half depth ordinal⟩

run_cmd IO.eprintln "CP577_CONTROL + each_literal_physical_slot_pays_original_K_and_strict_second_energy"
theorem each_literal_physical_slot_pays_original_K_and_strict_second_energy (ordinal : Nat) :
    (input ordinal).1 ≠ 0 ∧
    0 < (inner ℂ (input ordinal).1 (second ordinal).1).re ∧
    (∃ test : Probe, inner ℂ (burnolCompletedMellinRieszVector test.1 : BurnolL2) (input ordinal).1 ≠ 0) :=
  ⟨actual_division_physical_ne_zero observation nontrivial half depth ordinal,
    actual_division_physical_energy_positive observation nontrivial half depth ordinal,
    actual_single_slot_price_nonzero observation nontrivial half depth ordinal⟩

private theorem literal_to_whole (ordinal : Nat) : toWhole (stock ordinal) = actual ordinal := rfl

run_cmd IO.eprintln "CP577_CONTROL + one_current_price_net_recovers_both_literal_complete_second_graphs"
set_option cleanup.letToHave false in
theorem one_current_price_net_recovers_both_literal_complete_second_graphs (ordinal : Nat) :
    let fit := fun tests : Finset Probe => priceInverse tests (prices ordinal tests);
    (∀ tests : Finset Probe, type_of% (actual_recorded observation nontrivial half depth ordinal tests)) ∧
    Tendsto (fun tests => toWhole (fit tests)) atTop (𝓝 (actual ordinal)) ∧
    Tendsto (fun tests => toWhole (advanceWide c observation.mathlibZero (fit tests))) atTop
      (𝓝 (actual (ordinal+1))) ∧
    type_of% (actual_second_fields observation nontrivial half depth ordinal) ∧
    type_of% (actual_second_fields observation nontrivial half depth (ordinal+1)) := by
  let paid := actual_single_slot_price_recovery observation nontrivial half depth ordinal
  have old := (toWhole.continuous.tendsto (stock ordinal)).comp paid.1
  have next := (toWhole.continuous.tendsto (stock (ordinal+1))).comp paid.2
  rw [literal_to_whole] at old next
  exact ⟨actual_recorded observation nontrivial half depth ordinal, old, next,
    actual_second_fields observation nontrivial half depth ordinal,
    actual_second_fields observation nontrivial half depth (ordinal+1)⟩

run_cmd IO.eprintln "CP577_CONTROL + the_original_same_step_keeps_relation_whole_and_native_next"
set_option cleanup.letToHave false in
theorem the_original_same_step_keeps_relation_whole_and_native_next (ordinal : Nat) :
    advanceWide c observation.mathlibZero (stock ordinal) = stock (ordinal+1) ∧
    advance c observation.mathlibZero (toWhole (stock ordinal)) = toWhole (stock (ordinal+1)) ∧
    type_of% (actual_relation_stock_next observation nontrivial half depth ordinal) ∧
    type_of% (actual_division_action_same_root observation nontrivial half depth ordinal) := by
  have written : advance c observation.mathlibZero (toWhole (stock ordinal)) =
      toWhole (stock (ordinal+1)) :=
    (congrArg (advance c observation.mathlibZero)
      (literal_to_whole observation nontrivial half depth ordinal)).trans
      ((actual_second_graph_next observation nontrivial half depth ordinal).trans
        (literal_to_whole observation nontrivial half depth (ordinal+1)).symm)
  exact ⟨actual_wide_next observation nontrivial half depth ordinal, written,
    actual_relation_stock_next observation nontrivial half depth ordinal,
    actual_division_action_same_root observation nontrivial half depth ordinal⟩

run_cmd IO.eprintln "CP577_CONTROL - no_literal_physical_slot_can_erase_every_original_K_price"
theorem no_literal_physical_slot_can_erase_every_original_K_price (ordinal : Nat) :
    ¬ ∀ test : Probe, inner ℂ (burnolCompletedMellinRieszVector test.1 : BurnolL2) (input ordinal).1 = 0 := by
  intro erased
  obtain ⟨test,visible⟩ := actual_single_slot_price_nonzero observation nontrivial half depth ordinal
  exact visible (erased test)

end SingleSlotPhysicalPriceCertificate
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
