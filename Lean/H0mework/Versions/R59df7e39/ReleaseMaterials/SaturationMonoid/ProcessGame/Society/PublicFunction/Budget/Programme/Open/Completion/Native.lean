import H0mework.Versions.R59df7e39.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Lawful

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion

open Distributed.Reaction.Feedback.Authority.Trace

variable {Party Good Port Technology Instrument : Type}

def isGrant : Lawful.Key Party Good Port Technology Instrument → Bool
  | .originalGrant _ | .candidateGrant _ => true
  | _ => false

def grantDueOnly (manifest : Manifest Party Good Port Technology Instrument) : Prop :=
  ∀ key ∈ (Lawful.inventory manifest).due,isGrant key = true

instance [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
    [DecidableEq Technology] [DecidableEq Instrument]
    (manifest : Manifest Party Good Port Technology Instrument) : Decidable (grantDueOnly manifest) := by
  unfold grantDueOnly
  infer_instance

private theorem challenge_rows_are_not_grants
    (claim : ChallengeImage Party Good Port Technology Instrument)
    (state : ChallengeStateImage Party Good Port Technology Instrument) :
    ((Lawful.challengeRows (.originalChallenge claim) state).map Prod.fst).filter isGrant = [] ∧
    ((Lawful.challengeRows (.candidateChallenge claim) state).map Prod.fst).filter isGrant = [] := by
  constructor <;> simp only [Lawful.challengeRows, List.map_map, List.filter_eq_nil_iff,
    List.mem_map, Function.comp_apply] <;> intro key present <;>
    obtain ⟨slot,_,rfl⟩ := present <;> cases slot <;> simp [isGrant]

/-- A grant's original admission remains due even when its current bearer is released. -/
theorem every_admitted_grant_remains_in_the_original_due_inventory
    (manifest : Manifest Party Good Port Technology Instrument) :
    (Lawful.inventory manifest).due.filter isGrant =
      (Lawful.inventory manifest).admitted.filter isGrant := by
  have rows_paid : ∀ row ∈ Lawful.rows manifest,isGrant row.1 = true → row.2 = true := by
    intro row present grant
    simp only [Lawful.rows,List.mem_append,List.mem_map,List.mem_flatMap] at present
    rcases present with ((⟨_,_,rfl⟩ | ⟨_,_,rfl⟩) | ⟨claim,_,slot⟩) | ⟨claim,_,slot⟩
    · rfl
    · rfl
    · have empty := (challenge_rows_are_not_grants claim.1 claim.2.2).1
      have member : row.1 ∈ ((Lawful.challengeRows (.originalChallenge claim.1) claim.2.2).map Prod.fst).filter isGrant :=
        List.mem_filter.mpr ⟨List.mem_map.mpr ⟨row,slot,rfl⟩,grant⟩
      rw [empty] at member
      exact False.elim (List.not_mem_nil member)
    · have empty := (challenge_rows_are_not_grants claim.1 claim.2).2
      have member : row.1 ∈ ((Lawful.challengeRows (.candidateChallenge claim.1) claim.2).map Prod.fst).filter isGrant :=
        List.mem_filter.mpr ⟨List.mem_map.mpr ⟨row,slot,rfl⟩,grant⟩
      rw [empty] at member
      exact False.elim (List.not_mem_nil member)
  change (((Lawful.rows manifest).filter Prod.snd).map Prod.fst).filter isGrant = _
  rw [List.filter_map,List.filter_filter]
  have same : (Lawful.rows manifest).filter (fun row => isGrant row.1 && row.2) =
      (Lawful.rows manifest).filter (fun row => isGrant row.1) := by
    apply List.filter_congr
    intro row present
    by_cases grant : isGrant row.1 = true
    · simp [grant,rows_paid row present grant]
    · simp [grant]
  simp only [Function.comp_apply]
  rw [same]
  change _ = ((Lawful.rows manifest).map Prod.fst).filter isGrant
  rw [List.filter_map]
  rfl

private theorem filter_subperm {Key : Type} {old new : List Key} (p : Key → Bool)
    (preserved : old.Subperm new) : (old.filter p).Subperm (new.filter p) := by
  obtain ⟨middle,permuted,included⟩ := preserved
  exact ⟨middle.filter p,permuted.filter p,included.filter p⟩

theorem admitted_grants_generate_the_reverse_due_order
    (old new : Manifest Party Good Port Technology Instrument)
    (grants : grantDueOnly old)
    (admitted : (Lawful.inventory old).admitted.Subperm (Lawful.inventory new).admitted) :
    (Lawful.inventory old).due.Subperm (Lawful.inventory new).due := by
  have only : (Lawful.inventory old).due.filter isGrant = (Lawful.inventory old).due :=
    List.filter_eq_self.mpr grants
  rw [← only,every_admitted_grant_remains_in_the_original_due_inventory old]
  have filtered := filter_subperm isGrant admitted
  rw [← every_admitted_grant_remains_in_the_original_due_inventory new] at filtered
  exact filtered.trans List.filter_sublist.subperm

end SaturationMonoid.ProcessGame.Society.PublicFunction.Budget.Programme.Open.Completion
