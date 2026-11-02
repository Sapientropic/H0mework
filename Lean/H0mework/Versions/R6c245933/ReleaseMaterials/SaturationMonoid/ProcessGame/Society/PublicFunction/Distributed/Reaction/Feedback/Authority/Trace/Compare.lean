import H0mework.Versions.R6c245933.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Source

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]
  (old new : Manifest Party Good Port Technology Instrument)

inductive Difference where
  | world (index : Nat) (different : new.worlds[index]? ≠ old.worlds[index]?)
  | originalGrant (index : Nat) (different : new.originalGrants[index]? ≠ old.originalGrants[index]?)
  | originalChallenge (index : Nat) (different : new.originalChallenges[index]? ≠ old.originalChallenges[index]?)
  | candidateGrant (index : Nat) (different : new.candidateGrants[index]? ≠ old.candidateGrants[index]?)
  | candidateChallenge (index : Nat) (different : new.candidateChallenges[index]? ≠ old.candidateChallenges[index]?)

inductive Comparison where
  | matched (same : new = old)
  | different (evidence : Difference old new)

/-- Encoded trace equality proves neither root identity nor welfare dominance. -/
def compare : Comparison old new :=
  match Native.Coupling.compareLists old.worlds new.worlds with
  | .different index different => .different (.world index different)
  | .equal worlds => match Native.Coupling.compareLists old.originalGrants new.originalGrants with
    | .different index different => .different (.originalGrant index different)
    | .equal grants => match Native.Coupling.compareLists old.originalChallenges new.originalChallenges with
      | .different index different => .different (.originalChallenge index different)
      | .equal challenges => match Native.Coupling.compareLists old.candidateGrants new.candidateGrants with
        | .different index different => .different (.candidateGrant index different)
        | .equal candidateGrants => match Native.Coupling.compareLists old.candidateChallenges new.candidateChallenges with
          | .different index different => .different (.candidateChallenge index different)
          | .equal candidateChallenges => .matched (by cases old; cases new; congr 1)

def Comparison.accepted : Comparison old new → Bool
  | .matched _ => true | .different _ => false

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem Difference.excludes_equality (difference : Difference old new) : new ≠ old := by
  intro same
  cases difference with
  | world index different => exact different (congrArg (fun manifest => manifest.worlds[index]?) same)
  | originalGrant index different => exact different (congrArg (fun manifest => manifest.originalGrants[index]?) same)
  | originalChallenge index different => exact different (congrArg (fun manifest => manifest.originalChallenges[index]?) same)
  | candidateGrant index different => exact different (congrArg (fun manifest => manifest.candidateGrants[index]?) same)
  | candidateChallenge index different => exact different (congrArg (fun manifest => manifest.candidateChallenges[index]?) same)

def Difference.address : Difference old new → String × Nat
  | .world index _ => ("world", index)
  | .originalGrant index _ => ("originalGrant", index)
  | .originalChallenge index _ => ("originalChallenge", index)
  | .candidateGrant index _ => ("candidateGrant", index)
  | .candidateChallenge index _ => ("candidateChallenge", index)

def Comparison.address : Comparison old new → Option (String × Nat)
  | .matched _ => none | .different difference => some (difference.address old new)

theorem exact_comparison_iff : (compare old new).accepted = true ↔ new = old := by
  cases compare old new with
  | matched same => exact ⟨fun _ => same, fun _ => rfl⟩
  | different evidence => exact ⟨fun impossible => Bool.noConfusion impossible, fun same => False.elim (evidence.excludes_equality old new same)⟩

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace
