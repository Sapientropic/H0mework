import H0mework.Versions.R2.Physics.EmpiricalContact.Model

/-! A conservative empirical-contact epoch. The physical source and fields
are retained; the same live account gains its computed statistical residual.
No old quantum occurrence is reclassified and no U8 failure is assumed. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch

open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.RootInquiryCompletion
open Stage9C.Revision ProofFreeRicherAnholonomicSource StageNineEnrichedProofFreeSource
open StageNineDiracDualFormNativeFixedP506CartanECConstraintCauchyGravityTailRootNativeWrite

noncomputable section

/-- First occurrence following the already executed nineteen-tick prefix. -/
def sourceVisit := SpinPair.visit 13
def sourceEntry := materialEntry (SpinPair.support sourceVisit.current)
def sourceAuthority := SpinPair.authorityAt 13

abbrev Support := MaterialSupport × Option ReleasedContact
abbrev Responsibility := RootResidualPayload × Option (ReleasedContact × ℝ)

inductive Current
  | ingress
  | active (physical : SpinPair.Current) (contact : ReleasedContact)

def underlying : Current → SpinPair.Current
  | .ingress => sourceVisit.current
  | .active physical _ => physical

def support : Current → Support
  | .ingress => (SpinPair.support sourceVisit.current, none)
  | .active physical contact => (SpinPair.support physical, some contact)

inductive ActionAt : Current → Type
  | receive (contact : ReleasedContact) (source_exact : contact = releasedContact) : ActionAt .ingress
  | advance (physical : SpinPair.Current) (contact : ReleasedContact) : ActionAt (.active physical contact)

def actionAt : (current : Current) → ActionAt current
  | .ingress => .receive releasedContact rfl
  | .active physical contact => .advance physical contact

def actionTarget : {current : Current} → ActionAt current → Current
  | _, .receive contact _ => .active (SpinPair.next sourceVisit.current) contact
  | _, .advance physical contact => .active (SpinPair.next physical) contact

def next (current : Current) : Current := actionTarget (actionAt current)

theorem action_unique {current : Current} (action : ActionAt current) : action = actionAt current := by
  cases action with
  | receive contact exact => cases exact; rfl
  | advance => rfl

def residual (where_ : Support) : Responsibility :=
  (materialResidual where_.1, where_.2.map fun contact => (contact, contactResidual contact))

structure OpenAt (where_ : Support) (responsibility : Responsibility) : Type where
  exact : responsibility = residual where_

inductive InstrumentInputNeed
  | disjointPhaseAlignment
  | independentRealBellPreparation
  | disjointBinaryReadoutAssignment
  deriving DecidableEq

def requiredInputs : List InstrumentInputNeed :=
  [.disjointPhaseAlignment, .independentRealBellPreparation, .disjointBinaryReadoutAssignment]

abbrev AuditClaim := ReleasedContact × List InstrumentInputNeed
abbrev Claim := MaterialClaim ⊕ AuditClaim

def holds : Support → Claim → Type
  | where_, .inl claim => materialClaimHolds where_.1 claim
  | where_, .inr claim => PLift
      (where_.2 = some claim.1 ∧ 0 < contactResidual claim.1 ∧ claim.2 = requiredInputs)

abbrev ObstructionAt (where_ : Support) :=
  MaterialObstructionAt where_.1 ⊕
    { contact : ReleasedContact // where_.2 = some contact ∧ 0 < contactResidual contact }

inductive DispositionAt : Support → WorldDispositionKind → Type
  | inherited {where_ : Support} {kind : WorldDispositionKind}
      (receipt : MaterialN.DispositionAt where_.1 kind) : DispositionAt where_ kind
  | transfer {current : Current} (action : ActionAt current) : DispositionAt (support current) .transfer

def network : WorldRelationNetwork where
  Support := Support
  Anchor := MaterialN.Anchor
  Incidence := Support
  Lineage := MaterialN.Lineage
  Responsibility := Responsibility
  Claim := Claim
  anchorAt := fun _ => positiveSmoothUnifiedSource
  incidenceAt := id
  lineageAt := fun _ => positiveSmoothUnifiedSource
  OpenAt := OpenAt
  openClaimAt := fun _ => .inl (.inl .liveAccount)
  HoldsAt := holds
  ObstructionAt := ObstructionAt
  obstructionClaim := fun {_} obstruction => match obstruction with
    | .inl old => .inl (MaterialN.obstructionClaim old)
    | .inr contact => .inr (contact.val, requiredInputs)
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := DispositionAt

abbrev N := network

def entry (where_ : Support) : OpenResponsibilityAt N where_ := ⟨residual where_, ⟨rfl⟩⟩

theorem entry_unique (where_ : Support) (candidate : OpenResponsibilityAt N where_) :
    candidate = entry where_ := by
  rcases candidate with ⟨_, ⟨exact⟩⟩
  cases exact
  rfl

private def identityRetract (A : Type) : ConstructiveRetract A A := ⟨id, id, fun _ => rfl⟩

def translation : TypedSemanticWorldNetworkTranslationAt MaterialN N where
  support := ⟨fun old => (old, none), Prod.fst, fun _ => rfl⟩
  anchor := identityRetract _
  incidence := ⟨fun old => (old, none), Prod.fst, fun _ => rfl⟩
  lineage := identityRetract _
  responsibility := ⟨fun old => (old, none), Prod.fst, fun _ => rfl⟩
  claim := ⟨Sum.inl, (fun | .inl old => old | .inr _ => .inl .liveAccount), fun _ => rfl⟩
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun _ => rfl
  lineage_commutes := fun _ => rfl
  oldOpenLedger := fun old =>
    { forward := fun _ => entry (old, none)
      backward := fun _ => materialEntry old
      backward_forward := fun candidate => (materialEntry_unique old candidate).symm }
  oldOpenClaim_commutes := fun _ _ => rfl
  oldOpenProgressBudget_commutes := fun _ _ => rfl
  oldHoldsSurvives := fun _ _ evidence => evidence
  oldDispositionSurvives := fun _ _ receipt => .inherited receipt

theorem ingress_no_fresh (candidate : OpenResponsibilityAt N (support .ingress)) :
    candidate = (translation.oldOpenLedger (SpinPair.support sourceVisit.current)).forward sourceEntry :=
  entry_unique _ candidate

/-- The source contact creates an empirical obstruction without asserting a
nonzero classical Euler residual. Its scope is the fixed ideal apparatus claim. -/
def generatedObstruction : N.ObstructionAt (support (next .ingress)) :=
  .inr ⟨releasedContact, rfl, released_contact_residual_positive⟩

theorem account_claim_invariant (left right : Support) :
    @OpenResponsibilityAt.claim N left (entry left) =
      @OpenResponsibilityAt.claim N right (entry right) := rfl

theorem physical_source_preserved :
    N.anchorAt (support (next .ingress)) = positiveSmoothUnifiedSource := rfl

end
end SaturationMonoid.PhysicsCore.Stage10.Empirical.ContactEpoch
