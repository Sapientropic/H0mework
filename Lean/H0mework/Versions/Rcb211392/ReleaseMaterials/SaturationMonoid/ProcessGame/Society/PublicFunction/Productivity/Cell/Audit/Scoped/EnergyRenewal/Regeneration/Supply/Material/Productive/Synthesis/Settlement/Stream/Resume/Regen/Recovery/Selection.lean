import H0mework.Versions.Rcb211392.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Material.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery.Menu

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery

open Institutions.Capitalism.Universal.Source.Program

inductive Selection (scope : Scope) (permission : Material.Mode) (before : Current) where
  | original
  | repay (choice : OptionAt scope permission before)
  | blocked (exhausted : select? scope permission before = none)

def hasExpired {basis : State} (frame : Frame basis) : Bool :=
  frame.protocol.pending.any fun window => decide (window.task.deadline < frame.raw.clock)

def permissionAt (seed : Seed) (requests : Requests.Source) (registered : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis) : Material.Mode :=
  if Resume.due seed requests ordinal frame then registered else .withheld

theorem own_funded_feed_keeps_the_reserve_unoffered
    (seed : Seed) (requests : Requests.Source) (registered : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis) (enough : 1 ≤ frame.raw.stock customer .feed) :
    permissionAt seed requests registered ordinal frame = .withheld := by
  simp [permissionAt, Resume.due, not_lt.mpr enough]

theorem funded_customer_menu_is_exactly_the_local_menu
    (seed : Seed) (requests : Requests.Source) (registered : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis) (enough : 1 ≤ frame.raw.stock customer .feed)
    (route : Route) :
    Available seed.basis.origin.scope (permissionAt seed requests registered ordinal frame) frame.raw route ↔
      match route with
      | .local recipe => Available seed.basis.origin.scope registered frame.raw (.local recipe)
      | .reserve _ => False := by
  rw [own_funded_feed_keeps_the_reserve_unoffered seed requests registered ordinal frame enough]
  cases route
  · rfl
  · simp [Available, Offered]

def selection (seed : Seed) (permission : Material.Mode) (frame : Frame seed.basis) :
    Selection seed.basis.origin.scope permission frame.raw :=
  if 0 < owed frame.raw ∧ hasExpired frame = false then
    match selected : select? seed.basis.origin.scope permission frame.raw with
    | some choice => .repay choice
    | none => .blocked selected
  else .original

theorem an_available_route_forces_repayment
    (seed : Seed) (permission : Material.Mode) (frame : Frame seed.basis)
    (inTime : hasExpired frame = false) {route : Route}
    (available : Available seed.basis.origin.scope permission frame.raw route) :
    ∃ choice, selection seed permission frame = .repay choice := by
  cases chosen : select? seed.basis.origin.scope permission frame.raw with
  | none =>
    obtain ⟨blocked⟩ := no_choice_has_a_named_obstruction_for_each_route _ _ _ chosen route
    exact ((blocked.excludes _ _ _ _) available).elim
  | some choice =>
    refine ⟨choice, ?_⟩
    unfold selection
    rw [if_pos ⟨available.1, inTime⟩]
    split
    · rename_i actual read
      exact congrArg Selection.repay (Option.some.inj (read.symm.trans chosen))
    · rename_i absent
      rw [chosen] at absent
      cases absent

theorem expired_returns_to_the_original_protocol
    (seed : Seed) (permission : Material.Mode) (frame : Frame seed.basis)
    (expired : hasExpired frame = true) :
    selection seed permission frame = .original := by
  simp [selection, expired]

def word (seed : Seed) (requests : Requests.Source) (authority : Authority) (permission : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis) : List JointAction :=
  let admitted := permissionAt seed requests permission ordinal frame
  match selection seed admitted frame with
  | .original => Regen.word seed requests authority ordinal frame
  | .repay choice => routeWord seed.basis.origin.scope admitted frame.raw choice.val
  | .blocked _ => []

def step (seed : Seed) (requests : Requests.Source) (authority : Authority) (permission : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis) : Frame seed.basis :=
  let admitted := permissionAt seed requests permission ordinal frame
  match selection seed admitted frame with
  | .original => Regen.step seed requests authority ordinal frame
  | .repay choice =>
    ⟨Supply.initialMemo (quotedAfter seed.basis.origin.scope admitted frame.raw choice.val), frame.protocol⟩
  | .blocked _ => ⟨Supply.initialMemo ((law seed.basis.origin.scope).next frame.raw []), frame.protocol⟩

theorem paid_principal_returns_to_the_original_step
    (seed : Seed) (requests : Requests.Source) (authority : Authority) (permission : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis) (paid : owed frame.raw = 0) :
    step seed requests authority permission ordinal frame = Regen.step seed requests authority ordinal frame := by
  simp [step, selection, paid]

theorem step_uses_the_selected_word
    (seed : Seed) (requests : Requests.Source) (authority : Authority) (permission : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis) :
    (step seed requests authority permission ordinal frame).raw =
      (law seed.basis.origin.scope).next frame.raw (word seed requests authority permission ordinal frame) := by
  dsimp only [step, word]
  split
  · exact step_uses_the_selected_actual_word seed requests authority ordinal frame
  · exact Supply.initialMemo_exact _
  · exact Supply.initialMemo_exact _

theorem repayment_retires_the_original_principal_and_keeps_the_request
    (seed : Seed) (requests : Requests.Source) (authority : Authority) (permission : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis)
    (choice : OptionAt seed.basis.origin.scope (permissionAt seed requests permission ordinal frame) frame.raw)
    (selected : selection seed (permissionAt seed requests permission ordinal frame) frame = .repay choice) :
    owed (step seed requests authority permission ordinal frame).raw = 0 ∧
      (step seed requests authority permission ordinal frame).protocol = frame.protocol := by
  simp only [step, selected, Supply.initialMemo_exact, and_true]
  exact choice.property.2.2.2.2

theorem exhaustion_retains_the_entire_original_stock_claims_and_protocol
    (seed : Seed) (requests : Requests.Source) (authority : Authority) (permission : Material.Mode)
    (ordinal : Nat) (frame : Frame seed.basis)
    (exhausted : select? seed.basis.origin.scope (permissionAt seed requests permission ordinal frame) frame.raw = none)
    (selected : selection seed (permissionAt seed requests permission ordinal frame) frame = .blocked exhausted) :
    let after := step seed requests authority permission ordinal frame
    after.raw.stock = frame.raw.stock ∧ after.raw.claims = frame.raw.claims ∧ after.protocol = frame.protocol := by
  simp only [step, selected, Supply.initialMemo_exact]
  exact ⟨rfl, rfl, trivial⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Scoped.EnergyRenewal.Regeneration.Supply.Productive.Synthesis.Settlement.Stream.Resume.Regen.Recovery
