import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Following.Actual

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CPS1Following
noncomputable section
variable {frame : CPS1Recycling.Frame}

def ReactionFailure (reaction : Reaction frame) (failure : Failure) : Prop :=
  match reaction with
  | .relocate state => relocate? state = .error failure
  | .pulse state time => pulse? state time = .error failure
  | .deposit state amount => deposit? state amount = .error failure
  | _ => False

theorem reaction_guard_failure (reaction : Reaction frame) (failure : Failure)
    (member : Species.guard failure ∈ reaction.reactants frame) : ReactionFailure reaction failure := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,_,same⟩
    cases same
  | relocate state =>
    cases updated : relocate? state with
    | ok next => simp [Reaction.reactants,guards,updated] at member
    | error missing =>
      have same : failure = missing := by simpa [Reaction.reactants,guards,updated] using member
      cases same
      exact updated
  | pulse state time =>
    cases updated : pulse? state time with
    | ok next => simp [Reaction.reactants,guards,updated] at member
    | error missing =>
      have same : failure = missing := by simpa [Reaction.reactants,guards,updated] using member
      cases same
      exact updated
  | deposit state amount =>
    cases updated : deposit? state amount with
    | ok next => simp [Reaction.reactants,guards,updated] at member
    | error missing =>
      have same : failure = missing := by simpa [Reaction.reactants,guards,updated] using member
      cases same
      exact updated
  | keepFollowing state => simp [Reaction.reactants] at member

theorem true_guard_cut (program : List (Reaction frame)) (stock : Stock frame) (failure : Failure)
    (cut : (execute frame program stock).missing = some (.guard failure)) :
    ∃ reaction rest, (execute frame program stock).remaining = reaction :: rest ∧
      ReactionFailure reaction failure ∧
      (execute frame program stock).stock.count (.guard failure) < (reaction.reactants frame).count (.guard failure) := by
  rcases actual_cut program stock (.guard failure) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  exact ⟨reaction,rest,remaining,reaction_guard_failure reaction failure (List.count_pos_iff.mp positive),shortage⟩

theorem reaction_old_guard (reaction : Reaction frame) (failure : CPS1QuantumNuclear.Failure)
    (member : Species.retained (.guard failure) ∈ reaction.reactants frame) :
    ∃ old, reaction = .retained old ∧ CPS1QuantumNuclear.ReactionFailure old failure := by
  cases reaction with
  | retained old =>
    rcases List.mem_map.mp member with ⟨species,present,same⟩
    have identified := Species.retained.inj same
    rw [identified] at present
    exact ⟨old,rfl,CPS1QuantumNuclear.reaction_guard_failure old failure present⟩
  | relocate state => cases updated : relocate? state <;> simp [Reaction.reactants,guards,updated] at member
  | pulse state time => cases updated : pulse? state time <;> simp [Reaction.reactants,guards,updated] at member
  | deposit state amount => cases updated : deposit? state amount <;> simp [Reaction.reactants,guards,updated] at member
  | keepFollowing state => simp [Reaction.reactants] at member

theorem inherited_guard_cut (program : List (Reaction frame)) (stock : Stock frame)
    (failure : CPS1QuantumNuclear.Failure)
    (cut : (execute frame program stock).missing = some (.retained (.guard failure))) :
    ∃ old rest, (execute frame program stock).remaining = Reaction.retained old :: rest ∧
      CPS1QuantumNuclear.ReactionFailure old failure := by
  rcases actual_cut program stock (.retained (.guard failure)) cut with ⟨reaction,rest,remaining,shortage⟩
  have positive := (Nat.zero_le _).trans_lt shortage
  rcases reaction_old_guard reaction failure (List.count_pos_iff.mp positive) with ⟨old,same,failed⟩
  cases same
  exact ⟨old,rest,remaining,failed⟩

end
end CPS1Following
