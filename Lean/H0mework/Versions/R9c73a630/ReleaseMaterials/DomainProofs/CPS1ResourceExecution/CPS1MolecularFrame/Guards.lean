import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Actual
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MolecularFrame.Good
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Guards

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1MolecularFrame
noncomputable section
open CPS1ResourceExecution
variable {frame : CPS1Recycling.Frame}

def ReactionFailure (reaction : Reaction frame) (failure : Failure) : Prop :=
  match reaction with
  | .adopt reference => adopt? reference = .error failure
  | .pulse state time => state.pulse? time = .error failure
  | .deposit state amount => state.deposit? amount = .error failure
  | _ => False

theorem reaction_guard_failure (reaction : Reaction frame) (failure : Failure)
    (member : Species.guard failure ∈ reaction.reactants frame) : ReactionFailure reaction failure := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  | adopt reference =>
    cases updated : adopt? reference with
    | ok next => simp [Reaction.reactants,guards,updated] at member
    | error missing =>
      have same : failure = missing := by simpa [Reaction.reactants,guards,updated] using member
      cases same
      exact updated
  | pulse state time =>
    cases updated : state.pulse? time with
    | ok next => simp [Reaction.reactants,guards,updated] at member
    | error missing =>
      have same : failure = missing := by simpa [Reaction.reactants,guards,updated] using member
      cases same
      exact updated
  | deposit state amount =>
    cases updated : state.deposit? amount with
    | ok next => simp [Reaction.reactants,guards,updated] at member
    | error missing =>
      have same : failure = missing := by simpa [Reaction.reactants,guards,updated] using member
      cases same
      exact updated
  | keepMolecular state => simp [Reaction.reactants] at member
  | requireCarrier => simp [Reaction.reactants] at member

theorem true_guard_cut (program : List (Reaction frame)) (stock : Stock frame) (failure : Failure)
    (cut : (execute frame program stock).missing = some (.guard failure)) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      ReactionFailure reaction failure ∧
      (execute frame program stock).stock.count (.guard failure) < (reaction.reactants frame).count (.guard failure) := by
  rcases actual_cut program stock (.guard failure) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  exact ⟨reaction,rest,remaining,reaction_guard_failure reaction failure (List.count_pos_iff.mp positive),shortage⟩

theorem reaction_old_guard (reaction : Reaction frame) (failure : CPS1Following.Failure)
    (member : Species.retained (.guard failure) ∈ reaction.reactants frame) :
    ∃ old, reaction = .retained old ∧ CPS1Following.ReactionFailure old failure := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact ⟨old,rfl,CPS1Following.reaction_guard_failure old failure present⟩
  | adopt reference => cases updated : adopt? reference <;> simp [Reaction.reactants,guards,updated] at member
  | pulse state time => cases updated : state.pulse? time <;> simp [Reaction.reactants,guards,updated] at member
  | deposit state amount => cases updated : state.deposit? amount <;> simp [Reaction.reactants,guards,updated] at member
  | keepMolecular state => simp [Reaction.reactants] at member
  | requireCarrier => simp [Reaction.reactants] at member

theorem inherited_guard_cut (program : List (Reaction frame)) (stock : Stock frame)
    (failure : CPS1Following.Failure)
    (cut : (execute frame program stock).missing = some (.retained (.guard failure))) :
    ∃ old rest, (execute frame program stock).remaining = Reaction.retained old :: rest ∧
      CPS1Following.ReactionFailure old failure := by
  rcases actual_cut program stock (.retained (.guard failure)) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  rcases reaction_old_guard reaction failure (List.count_pos_iff.mp positive) with ⟨old,same,failed⟩
  cases same
  exact ⟨old,rest,remaining,failed⟩

theorem reaction_missing_carrier (reaction : Reaction frame)
    (member : Species.missingCarrier ∈ reaction.reactants frame) : reaction = .requireCarrier := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  | adopt reference => cases updated : adopt? reference <;> simp [Reaction.reactants,guards,updated] at member
  | pulse state time => cases updated : state.pulse? time <;> simp [Reaction.reactants,guards,updated] at member
  | deposit state amount => cases updated : state.deposit? amount <;> simp [Reaction.reactants,guards,updated] at member
  | keepMolecular state => simp [Reaction.reactants] at member
  | requireCarrier => rfl

theorem missing_carrier_cut (program : List (Reaction frame)) (stock : Stock frame)
    (cut : (execute frame program stock).missing = some .missingCarrier) :
    ∃ rest, (execute frame program stock).remaining = Reaction.requireCarrier :: rest := by
  rcases actual_cut program stock .missingCarrier cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  have same := reaction_missing_carrier reaction (List.count_pos_iff.mp positive)
  cases same
  exact ⟨rest,remaining⟩

theorem reaction_failure_guard (reaction : Reaction frame) (failure : Failure)
    (failed : ReactionFailure reaction failure) : Species.guard failure ∈ reaction.reactants frame := by
  cases reaction with
  | retained old => cases failed
  | adopt reference => simp [Reaction.reactants,guards,ReactionFailure] at failed ⊢; rw [failed]; simp
  | pulse state time => simp [Reaction.reactants,guards,ReactionFailure] at failed ⊢; rw [failed]; simp
  | deposit state amount => simp [Reaction.reactants,guards,ReactionFailure] at failed ⊢; rw [failed]; simp
  | keepMolecular state => cases failed
  | requireCarrier => cases failed

theorem failed_reaction_cannot_fire (reaction : Reaction frame) (failure : Failure) (stock : Stock frame)
    (failed : ReactionFailure reaction failure) (safe : NoGuardStock stock) :
    ∀ next, Inventory.fire (Reaction.reactants frame) (Reaction.products frame) reaction stock ≠ .ok next := by
  intro next actual
  unfold Inventory.fire at actual
  cases consumed : Inventory.consume (reaction.reactants frame) stock with
  | error missing => simp [consumed] at actual
  | ok remainder =>
    have decomposition := Inventory.consume_perm _ _ _ consumed
    exact safe.1 failure (decomposition.mem_iff.mpr
      (List.mem_append_left _ (reaction_failure_guard reaction failure failed)))

theorem require_carrier_actual_cut (stock : Stock frame) (safe : NoGuardStock stock) :
    execute frame [.requireCarrier] stock = ⟨[],[.requireCarrier],stock,some .missingCarrier⟩ := by
  have unavailable : Species.missingCarrier ∉ stock := safe.2.1
  have failed : Inventory.fire (Reaction.reactants frame) (Reaction.products frame) .requireCarrier stock =
      .error .missingCarrier := by
    simp [Inventory.fire,Reaction.reactants,Inventory.consume,unavailable]
  rw [execute,Inventory.execute_cons,failed]

end
end CPS1MolecularFrame
