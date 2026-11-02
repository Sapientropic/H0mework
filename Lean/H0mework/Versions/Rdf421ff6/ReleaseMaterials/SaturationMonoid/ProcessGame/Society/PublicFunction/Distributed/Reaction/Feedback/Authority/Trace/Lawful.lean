import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Source
import Mathlib.Data.List.Perm.Subperm

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Lawful

open Institutions.Capitalism.Universal.Root

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Technology] [DecidableEq Instrument]

structure GrantKey (Party Good Port Technology Instrument : Type) where
  birth : Nat
  proposal : ItemImage Party Good Port (Mandate.State Party Technology) Instrument
  acceptance : ItemImage Party Good Port (Mandate.State Party Technology) Instrument
  initial : GrantObligationImage Party Port
  deriving DecidableEq

def grantKey (grant : GrantImage Party Good Port Technology Instrument) : GrantKey Party Good Port Technology Instrument :=
  ⟨grant.birth, grant.proposal, grant.acceptance, grant.initial⟩

structure ChallengeKey (Party Good Port Technology Instrument : Type) where
  admission : ChallengeEventImage Party Good Port Technology Instrument
  admittedBearer : Identity.ActorImage Party Good Port (Mandate.State Party Technology) Instrument
  admittedScope : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument
  content : ChallengeImage Party Good Port Technology Instrument
  beneficiary : TaskImage Party Good
  scope : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument
  lineage : Identity.OriginImage Party Good Port (Mandate.State Party Technology) Instrument
  deriving DecidableEq

/-- Reaffirmation updates residual state; an accepted handoff may update the current bearer.
    Neither change creates a different original admission. -/
def challengeKey (obligation : ChallengeObligationImage Party Good Port Technology Instrument) :
    ChallengeKey Party Good Port Technology Instrument :=
  ⟨obligation.admission, obligation.admittedBearer, obligation.admittedScope, obligation.content,
    obligation.beneficiary, obligation.scope, obligation.lineage⟩

inductive Key (Party Good Port Technology Instrument : Type) where
  | originalGrant (key : GrantKey Party Good Port Technology Instrument)
  | candidateGrant (key : GrantKey Party Good Port Technology Instrument)
  | originalChallenge (claim : ChallengeImage Party Good Port Technology Instrument)
      (key : ChallengeKey Party Good Port Technology Instrument)
  | candidateChallenge (claim : ChallengeImage Party Good Port Technology Instrument)
      (key : ChallengeKey Party Good Port Technology Instrument)
  deriving DecidableEq

structure Inventory (Key : Type) where
  admitted : List Key
  due : List Key
  deriving DecidableEq

def Inventory.NoWorse {Key : Type} (new old : Inventory Key) : Prop :=
  old.admitted.Subperm new.admitted ∧ new.due.Subperm old.due

instance {Key : Type} [DecidableEq Key] (new old : Inventory Key) : Decidable (new.NoWorse old) := by
  unfold Inventory.NoWorse
  infer_instance

theorem Inventory.refl {Key : Type} (inventory : Inventory Key) : inventory.NoWorse inventory :=
  ⟨List.Subperm.refl _, List.Subperm.refl _⟩

theorem Inventory.trans {Key : Type} {first second third : Inventory Key}
    (left : first.NoWorse second) (right : second.NoWorse third) : first.NoWorse third :=
  ⟨right.1.trans left.1, left.2.trans right.2⟩

theorem Inventory.counts_iff {Key : Type} [DecidableEq Key] (new old : Inventory Key) :
    new.NoWorse old ↔ ∀ key, old.admitted.count key ≤ new.admitted.count key ∧
      new.due.count key ≤ old.due.count key := by
  simp only [Inventory.NoWorse, List.subperm_iff_count, forall_and]

def challengeRows (tag : ChallengeKey Party Good Port Technology Instrument → Key Party Good Port Technology Instrument)
    (state : ChallengeStateImage Party Good Port Technology Instrument) :
    List (Key Party Good Port Technology Instrument × Bool) :=
  state.slots.map fun slot => match slot with
    | .live obligation => (tag (challengeKey obligation), true)
    | .terminal obligation _ => (tag (challengeKey obligation), false)

/-- Both the original migration census and the candidate's full census participate.
    Grant bearer release retains its live obligation; terminal Challenges retain their archive key. -/
def rows (manifest : Manifest Party Good Port Technology Instrument) :
    List (Key Party Good Port Technology Instrument × Bool) :=
  manifest.originalGrants.map (fun row => (.originalGrant (grantKey row.2), true)) ++
  manifest.candidateGrants.map (fun row => (.candidateGrant (grantKey row), true)) ++
  manifest.originalChallenges.flatMap (fun row => challengeRows (.originalChallenge row.1) row.2.2) ++
  manifest.candidateChallenges.flatMap (fun row => challengeRows (.candidateChallenge row.1) row.2)

def inventory (manifest : Manifest Party Good Port Technology Instrument) : Inventory (Key Party Good Port Technology Instrument) :=
  ⟨(rows manifest).map Prod.fst, ((rows manifest).filter Prod.snd).map Prod.fst⟩

def NoWorse (new old : Manifest Party Good Port Technology Instrument) : Prop :=
  (inventory new).NoWorse (inventory old)

instance (new old : Manifest Party Good Port Technology Instrument) : Decidable (NoWorse new old) := by
  unfold NoWorse
  infer_instance

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem refl (manifest : Manifest Party Good Port Technology Instrument) : NoWorse manifest manifest := Inventory.refl _

omit [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Technology] [DecidableEq Instrument] in
theorem trans {first second third : Manifest Party Good Port Technology Instrument}
    (left : NoWorse first second) (right : NoWorse second third) : NoWorse first third :=
  Inventory.trans left right

theorem preserves_every_original_admission_and_bounds_each_residue
    (new old : Manifest Party Good Port Technology Instrument) : NoWorse new old ↔
    ∀ key, (inventory old).admitted.count key ≤ (inventory new).admitted.count key ∧
      (inventory new).due.count key ≤ (inventory old).due.count key := Inventory.counts_iff _ _

end SaturationMonoid.ProcessGame.Society.PublicFunction.Distributed.Reaction.Feedback.Authority.Trace.Lawful
