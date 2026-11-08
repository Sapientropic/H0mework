import H0mework.Versions.R7e013edd.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.PhysicalOpportunityConsumer

set_option autoImplicit false
namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseClock
open Distributed Reaction Reaction.Feedback
open Distributed.Recall.Information.Agency.Protocol Continuation

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (model : Native.Authority.Bound (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (start : Cursor model.source.code)
  (vocabulary : OwnedAttestation.Vocabulary (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument))
  (encoding : StageTransport.Encoding (code := model.source.code)) (law : StageReception.Law model.source.code)

theorem actual_list_clocks (cursor : Cursor model.source.code) (stages : JointResponse.Stages model) :
    (EventStep.seed (EventHistory.execute cursor stages)).history.length = (EventStep.seed cursor).history.length + stages.length ∧
    (EventHistory.execute cursor stages).ownerStart = cursor.ownerStart := by
  induction stages generalizing cursor with
  | nil => exact ⟨rfl, rfl⟩
  | cons stage tail ih =>
    have next := ih (cursor.after stage.1 stage.2)
    have one := EventStep.actual_next_state cursor stage.1 stage.2
    refine ⟨?_, next.2⟩
    change (EventStep.seed (EventHistory.execute (cursor.after stage.1 stage.2) tail)).history.length = _
    rw [next.1, one]
    change ((EventStep.seed cursor).history ++ [_]).length + tail.length = _
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def width := start.ownerStart + 4 * model.source.code.sites

theorem every_actual_roster_block_has_the_original_receivers_slot
    (past more : JointResponse.Stages model) (receiver : Fin model.source.code.sites)
    (room : width model start ≤ more.length) :
    ∃ n < width model start, n < more.length ∧
      Distributed.Recall.Information.Agency.ownerAt model.source.code
        (EventHistory.execute start (past ++ more.take n)).ownerStart
        (EventStep.seed (EventHistory.execute start (past ++ more.take n))).history.length = some receiver := by
  let cursor := EventHistory.execute start past
  let delay := SilentWindow.delay cursor receiver
  have arrived := SilentWindow.the_actual_receiver_owns_the_generated_arrival cursor receiver
  have quiet := SilentWindow.preserves_the_actual_state cursor delay
  rw [quiet.roster, quiet.history] at arrived
  have bounded := SilentWindow.the_generated_delay_has_a_source_roster_bound cursor receiver
  have origin := (actual_list_clocks model start past).2
  have inside : delay < width model start := by
    change cursor.ownerStart = start.ownerStart at origin
    dsimp only [width]
    change delay < cursor.ownerStart - (EventStep.seed cursor).history.length + 4 * model.source.code.sites at bounded
    omega
  refine ⟨delay, inside, by omega, ?_⟩
  rw [StageQueue.execute_append]
  have clock := actual_list_clocks model cursor (more.take delay)
  rw [clock.2, clock.1, List.length_take, Nat.min_eq_left (by omega)]
  exact arrived

theorem one_eligible_actual_prefix_is_counted
    (past more : JointResponse.Stages model) (n : Nat) (inside : n < more.length)
    (eligible : ResponseEligibility.eligible model start vocabulary encoding law (past ++ more.take n) = true) :
    0 < PhysicalOpportunityClock.tally model start vocabulary encoding law past more := by
  induction more generalizing past n with
  | nil => cases inside
  | cons stage tail ih =>
    cases n with
    | zero =>
      simp only [List.take_zero, List.append_nil] at eligible
      simp only [PhysicalOpportunityClock.tally, eligible, if_true]
      omega
    | succ n =>
      have next : ResponseEligibility.eligible model start vocabulary encoding law ((past ++ [stage]) ++ tail.take n) = true := by
        simpa only [List.take_succ_cons, List.append_assoc, List.singleton_append] using eligible
      have counted := ih (past ++ [stage]) n (by simp only [List.length_cons] at inside; omega) next
      simp only [PhysicalOpportunityClock.tally]
      omega

theorem persistent_owned_cut_eligibility_generates_one_opportunity_per_source_roster_block
    (past more : JointResponse.Stages model) (receiver : Fin model.source.code.sites) (blocks : Nat)
    (room : width model start * blocks ≤ more.length)
    (eligible : ∀ n < more.length,
      Distributed.Recall.Information.Agency.ownerAt model.source.code
        (EventHistory.execute start (past ++ more.take n)).ownerStart
        (EventStep.seed (EventHistory.execute start (past ++ more.take n))).history.length = some receiver →
      ResponseEligibility.eligible model start vocabulary encoding law (past ++ more.take n) = true) :
    blocks ≤ PhysicalOpportunityClock.tally model start vocabulary encoding law past more := by
  induction blocks generalizing past more with
  | zero => exact Nat.zero_le _
  | succ blocks ih =>
    have firstRoom : width model start ≤ more.length := by rw [Nat.mul_succ] at room; omega
    obtain ⟨n, short, member, owner⟩ := every_actual_roster_block_has_the_original_receivers_slot model start past more receiver firstRoom
    have firstEligible : ResponseEligibility.eligible model start vocabulary encoding law (past ++ (more.take (width model start)).take n) = true := by
      simpa only [List.take_take, Nat.min_eq_left (Nat.le_of_lt short)] using eligible n member owner
    have first := one_eligible_actual_prefix_is_counted model start vocabulary encoding law past (more.take (width model start)) n
      (by simp only [List.length_take, Nat.min_eq_left firstRoom]; exact short) firstEligible
    have rest := ih (past ++ more.take (width model start)) (more.drop (width model start))
      (by simp only [List.length_drop]; rw [Nat.mul_succ] at room; omega) (by
        intro k bounded owner
        have index : width model start + k < more.length := by simp only [List.length_drop] at bounded; omega
        have same : past ++ more.take (width model start + k) =
            (past ++ more.take (width model start)) ++ (more.drop (width model start)).take k := by
          rw [List.take_add, List.append_assoc]
        rw [← same] at owner ⊢
        exact eligible _ index owner)
    have splitMore : more.take (width model start) ++ more.drop (width model start) = more := List.take_append_drop _ _
    rw [← splitMore, PhysicalOpportunityClock.tally_append]
    omega

end SaturationMonoid.ProcessGame.Society.PublicFunction.Protocol.SymbolicAuthentication.ForwardResponseClock
