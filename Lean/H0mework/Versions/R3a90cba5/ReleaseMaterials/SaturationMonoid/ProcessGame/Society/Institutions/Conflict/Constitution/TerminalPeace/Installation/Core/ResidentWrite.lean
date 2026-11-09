import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Sequential

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core.ResidentWrite

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (Resident First identityWhole)

noncomputable section

variable {N : WorldRelationNetwork} {Payload : Type}

/-- The finite live inventory is the actual resident's complete ledger. -/
structure Ready (prior : Resident N) : Prop where
  finite : Finite (OpenResponsibilityAt N prior.support)
  fibres : ∀ support row, Subsingleton (N.OpenAt support row)

variable (prior : Resident N) (ready : Ready prior) (emission : Payload) (writes : Bool)

def first : First N where
  before := prior.support
  after := prior.support
  whole := identityWhole _
  beforeFinite := ready.finite
  afterFinite := ready.finite
  openFibres := ready.fibres
  writes := writes

def component : SourceNativeProjectionLaw (Compiler.ledgerSource (first prior ready writes).flow) where
  Projection := PUnit
  ActiveAt := fun _ {current} _ => PLift (current = true)
  InactiveAt := fun _ {current} _ => PLift (current ≠ true)
  classify := fun _ {current} _ =>
    letI : Decidable (current = true) := decEq (α := Bool) current true
    if active : current = true then .inl ⟨active⟩ else .inr ⟨active⟩
  PayloadAt := fun _ {_} _ _ => Payload
  project := fun _ {_} _ _ => emission

local notation "FirstWrite" => first prior ready writes

set_option maxHeartbeats 700000 in
private def targetAt (event : ExactTemporalCausalRootEventAt
    prior.root.toAuthoritativeRoot.toLedgerRoot prior.visit) :
    SourceNativeSequentialActualActionTargetAt prior.root prior.visit event prior.entry prior.authority := by
  rw [event.eq_generated]
  let base := (FirstWrite).sequentialTarget prior rfl prior.event
  let root := base.targetRoot.withProjectionCoface (component prior ready emission writes)
  exact {
    base with
    targetRoot := root
    canonical_targetNextVisit_eq :=
      Ingress.next_is_the_same_generated_successor root (FirstWrite).initial (FirstWrite).successor
    Answer := Payload
    answer := emission
    Receipt := fun read => ULift.{3, 0} (PLift (read = emission))
    receipt := ⟨⟨rfl⟩⟩ }

private def program : SourceNativeSequentialActualActionProgramAt
    prior.root prior.visit prior.entry prior.authority where
  targetAt := targetAt prior ready emission writes

def action := (program prior ready emission writes).generate prior.event

def landing : Resident N :=
  let target := (action prior ready emission writes).target
  { V := target.TargetV
    root := target.targetRoot
    visit := target.targetVisit
    entry := target.targetEntry
    authority := target.targetAuthority
    unique := Compiler.occurrence_eq_emitted (FirstWrite).flow }

theorem lands_at_first_write : (landing prior ready emission writes).visit.current = true :=
  Compiler.successor_current (FirstWrite).flow false

theorem support_eq : (landing prior ready emission writes).support = prior.support :=
  congrArg (FirstWrite).support (lands_at_first_write prior ready emission writes)

def face : SourceNativeRootSemanticFaceAt (landing prior ready emission writes).root
    (landing prior ready emission writes).visit where
  projection := .component PUnit.unit
  active := ⟨lands_at_first_write prior ready emission writes⟩
  classifier_eq := by
    let now := (landing prior ready emission writes).visit.current
    let : Decidable (now = true) := decEq (α := Bool) now true
    change (if active : now = true then Sum.inl (PLift.up active) else Sum.inr (PLift.up active)) = _
    exact dif_pos (lands_at_first_write prior ready emission writes)

theorem canonical_next :
    (⟨N, (action prior ready emission writes).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (landing prior ready emission writes).erase :=
  congrArg (fun next => (⟨N, next⟩ : AnyAuthoritativeRootCurrent))
    (action prior ready emission writes).target.targetAnswerAndNext_next_eq

theorem whole_first_write :
    let written := (action prior ready emission writes).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole prior.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  ⟨(FirstWrite).first_destination, (FirstWrite).first_origin⟩

theorem earlier_reads (projection : prior.root.source.base.projectionLaw.Projection) :
    let arrived := landing prior ready emission writes
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (prior.root.source.base.projectionLaw.outcomeAt projection (prior.root.emitted prior.visit.current)) := by
  let ledger := Compiler.ledgerSource (FirstWrite).flow
  let base := (Compiler.livingRoot (FirstWrite).flow).source.base
  let frozen := (FirstWrite).inherit prior
  let material := component prior ready emission writes
  let install := (SourceNativeProjectionLaw.InstallationAt.componentCoface base frozen).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (base.withProjectionCoface frozen) material)
  let occurrence := Compiler.emitted (FirstWrite).flow (landing prior ready emission writes).visit.current
  exact (install.outcome_heq occurrence projection).trans
    (QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome
      prior.root.source.base.projectionLaw (prior.root.emitted prior.visit.current) ledger occurrence projection)

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core.ResidentWrite
