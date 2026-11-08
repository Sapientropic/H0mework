import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.UnifiedServiceConsumer
import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.LocalLifecycle

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeInventoryPrefix
open Distributed Reaction Reaction.Feedback
open Institutions.Capitalism.Universal.Source.Program Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.ProgrammeFace Mandate.Challenge
open Feedback.Authority.Trace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (code : Code Party Good Port (Mandate.State Party Technology) Instrument)
  {base : RawLaw Party Good Port Technology Instrument} {scope : Mandate.Scope}
  {Index : Type} (family : ProgrammeFamily base scope Index)
  {inputs nextInputs : Index} (limit : Nat)
  (initial : (I family nextInputs).initial = (I family inputs).initial)
  (events : ∀ ordinal < limit,
    ProgrammeSource.rawEvent (I family nextInputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current =
      ProgrammeSource.rawEvent (I family inputs) (ProgrammeHistory.visitAt (I family inputs) ordinal).current)

include code initial events

theorem actual_pending_is_preserved (count : Nat) (bounded : count ≤ limit)
    (old : Claim family inputs) (new : Claim family nextInputs)
    (same : challengeImage code family nextInputs new = challengeImage code family inputs old) :
    CompletedInventory.live family nextInputs count new = CompletedInventory.live family inputs count old := by
  have matched := (LocalLifecycle.through_match code family limit initial events count bounded same).pending
  unfold CompletedInventory.live
  cases left : Mandate.Challenge.through family inputs old count <;>
    cases right : Mandate.Challenge.through family nextInputs new count <;>
    simp only [left, right, LocalLifecycle.pendingImage] at matched
  all_goals first | rfl | contradiction

private theorem filtered_lengths (count : Nat) (bounded : count ≤ limit)
    (oldClaims : List (Claim family inputs)) (newClaims : List (Claim family nextInputs))
    (same : newClaims.map (challengeImage code family nextInputs) = oldClaims.map (challengeImage code family inputs)) :
    (newClaims.filter (CompletedInventory.live family nextInputs count)).length =
      (oldClaims.filter (CompletedInventory.live family inputs count)).length := by
  induction oldClaims generalizing newClaims with
  | nil => cases newClaims with | nil => rfl | cons => cases same
  | cons old rest ih =>
    cases newClaims with
    | nil => cases same
    | cons new later =>
      have parts := List.cons.inj same
      have pending := actual_pending_is_preserved code family limit initial events count bounded old new parts.1
      simp only [List.filter_cons, pending]
      split
      · exact congrArg Nat.succ (ih later parts.2)
      · exact ih later parts.2

theorem the_complete_pending_inventory_is_preserved (count : Nat) (bounded : count ≤ limit) :
    CompletedInventory.pending family nextInputs count = CompletedInventory.pending family inputs count := by
  apply filtered_lengths code family limit initial events count bounded
  simp only [CompletedInventory.originals, List.map_flatMap]
  apply List.flatMap_congr
  intro ordinal member
  exact ChallengeTransport.claims_images code family limit initial events ordinal
    (Nat.lt_of_lt_of_le (List.mem_range.mp member) bounded)

theorem the_actual_open_birth_slice_is_preserved (count : Nat) (bounded : count + 1 ≤ limit) :
    CompletedInventory.openBorn family nextInputs count = CompletedInventory.openBorn family inputs count := by
  apply filtered_lengths code family limit initial events (count + 1) bounded
  exact ChallengeTransport.claims_images code family limit initial events count (by omega)

theorem the_actual_old_disposition_slice_is_preserved (count : Nat) (bounded : count + 1 ≤ limit) :
    CompletedInventory.closedOld family nextInputs count = CompletedInventory.closedOld family inputs count := by
  have old := CompletedInventory.every_completed_cut_has_exact_source_birth_and_disposition_balance family inputs count
  have new := CompletedInventory.every_completed_cut_has_exact_source_birth_and_disposition_balance family nextInputs count
  have before := the_complete_pending_inventory_is_preserved code family limit initial events count (by omega)
  have after := the_complete_pending_inventory_is_preserved code family limit initial events (count + 1) bounded
  have born := the_actual_open_birth_slice_is_preserved code family limit initial events count bounded
  omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.NativeInventoryPrefix
