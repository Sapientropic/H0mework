import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeRecovery

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletedInventory
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Mandate.Challenge

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  {base : RawLaw Party Good Port Technology Instrument}
  {scope : Mandate.Scope (Party := Party) (Good := Good) (Port := Port)}
  {Index : Type} (bound : ProgrammeFamily base scope Index) (inputs : Index)

def originals (count : Nat) := (List.range count).flatMap (claimsAt bound inputs)
def live (count : Nat) (claim : Claim bound inputs) := (through bound inputs claim count).isPending bound inputs
def pending (count : Nat) := ((originals bound inputs count).filter (live bound inputs count)).length
def closedOld (count : Nat) := ((originals bound inputs count).filter fun claim =>
  live bound inputs count claim && !(live bound inputs (count + 1) claim)).length
def openBorn (count : Nat) := ((claimsAt bound inputs count).filter (live bound inputs (count + 1))).length

theorem actual_records_are_the_complete_slice_with_their_own_histories (count : Nat) :
    recordsAt bound inputs count = (originals bound inputs count).map
      (fun claim => ⟨claim, through bound inputs claim count⟩) := by
  simp only [recordsAt, originals, List.map_flatMap]

private theorem filter_map_length {α β : Type} (values : List α) (f : α → β) (test : β → Bool) :
    ((values.map f).filter test).length = (values.filter fun value => test (f value)).length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    cases tested : test (f head) <;> simp_all

theorem pending_is_the_actual_census_pending_length (count : Nat) :
    pending bound inputs count = ((recordsAt bound inputs count).filter
      (fun row => row.2.isPending bound inputs)).length := by
  rw [actual_records_are_the_complete_slice_with_their_own_histories, filter_map_length]
  rfl

theorem originals_succ (count : Nat) : originals bound inputs (count + 1) =
    originals bound inputs count ++ claimsAt bound inputs count := by
  simp only [originals, List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem read_own_position (claim : Claim bound inputs) : Mandate.Challenge.read bound inputs claim.position = some claim := by
  simp only [Mandate.Challenge.read, dif_pos claim.signed, dif_pos claim.accepted, dif_pos claim.active]

theorem every_actual_old_claim_is_in_the_complete_slice (claim : Claim bound inputs) (count : Nat)
    (old : claim.position.ordinal < count) : claim ∈ originals bound inputs count := by
  apply List.mem_flatMap.mpr
  refine ⟨claim.position.ordinal, List.mem_range.mpr old, List.mem_filterMap.mpr ⟨claim.position, ?_, read_own_position bound inputs claim⟩⟩
  apply List.mem_map.mpr
  exact ⟨claim.position.index, List.mem_finRange _, by cases claim.position; rfl⟩

theorem no_old_terminal_claim_becomes_pending (claim : Claim bound inputs) (count : Nat)
    (after : live bound inputs (count + 1) claim = true) : live bound inputs count claim = true := by
  cases before : live bound inputs count claim with
  | true => rfl
  | false =>
    have terminal := WithdrawalHistory.terminal_through_persists bound inputs claim count (count + 1) before (by omega)
    change live bound inputs (count + 1) claim = false at terminal
    rw [terminal] at after
    contradiction

private theorem partition {α : Type} (values : List α) (before after : α → Bool)
    (retained : ∀ value ∈ values, after value = true → before value = true) :
    (values.filter before).length = (values.filter after).length +
      (values.filter fun value => before value && !(after value)).length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    have rest := ih (fun value member => retained value (List.mem_cons_of_mem _ member))
    have first := retained head List.mem_cons_self
    cases left : before head <;> cases right : after head <;> simp_all <;> omega

theorem every_completed_cut_has_exact_source_birth_and_disposition_balance (count : Nat) :
    pending bound inputs (count + 1) + closedOld bound inputs count =
      pending bound inputs count + openBorn bound inputs count := by
  have old := partition (originals bound inputs count) (live bound inputs count) (live bound inputs (count + 1))
    (fun claim _ => no_old_terminal_claim_becomes_pending bound inputs claim count)
  unfold pending closedOld openBorn
  rw [originals_succ, List.filter_append, List.length_append]
  omega

theorem an_actual_old_terminalization_is_counted (count : Nat) (claim : Claim bound inputs)
    (old : claim.position.ordinal < count) (before : live bound inputs count claim = true)
    (after : live bound inputs (count + 1) claim = false) : 0 < closedOld bound inputs count := by
  have member : claim ∈ (originals bound inputs count).filter (fun value =>
      live bound inputs count value && !(live bound inputs (count + 1) value)) :=
    List.mem_filter.mpr ⟨every_actual_old_claim_is_in_the_complete_slice bound inputs claim count old,
      by simp only [before, after, Bool.not_false, Bool.and_self]⟩
  unfold closedOld
  cases shape : (originals bound inputs count).filter (fun value =>
      live bound inputs count value && !(live bound inputs (count + 1) value)) with
  | nil => rw [shape] at member; contradiction
  | cons head tail => simp only [List.length_cons]; omega

theorem one_actual_old_terminalization_without_open_newborns_strictly_lowers_the_complete_inventory
    (count : Nat) (claim : Claim bound inputs) (old : claim.position.ordinal < count)
    (before : live bound inputs count claim = true) (after : live bound inputs (count + 1) claim = false)
    (newborns : openBorn bound inputs count = 0) : pending bound inputs (count + 1) < pending bound inputs count := by
  have balance := every_completed_cut_has_exact_source_birth_and_disposition_balance bound inputs count
  have spent := an_actual_old_terminalization_is_counted bound inputs count claim old before after
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.CompletedInventory
