import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Run.State

set_option autoImplicit false
set_option maxRecDepth 8192

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Reparation.Actual (Resident First StateAt identityWhole)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]

/-- An installed occurrence reads its payload on the original live state.
Its stack and all previously installed dependent reads remain in place. -/
structure Landed (seed : Root.Cut Party Good Port Technology Instrument) (community : Party → Community)
    (cut : Root.Cut Party Good Port Technology Instrument) (Payload : Type) where
  private mk ::
  state : StateAt seed community cut
  material : SourceNativeRootSemanticFaceAt state.resident.root state.resident.visit
  materialType : material.Restriction = Payload

def Landed.read {seed cut : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
    {Payload : Type} (visit : Landed seed community cut Payload) : Payload :=
  cast visit.materialType visit.material.rootRead

variable {seed cut : Root.Cut Party Good Port Technology Instrument} {community : Party → Community}
  {Payload : Type}

private theorem finiteRows (prior : StateAt seed community cut) :
    Finite (OpenResponsibilityAt prior.world prior.resident.support) := by
  rw [prior.exactSupport]
  let native := cut.native
  exact prior.stack.finite _ (native.frame.entries_finite native.visit.current)

private def first (prior : StateAt seed community cut) (writes : Bool) : First prior.world where
  before := prior.resident.support
  after := prior.resident.support
  whole := identityWhole _
  beforeFinite := finiteRows prior
  afterFinite := finiteRows prior
  openFibres := prior.stack.fibres cut.native.frame.family.open_fibres
  writes := writes

private def component {N : WorldRelationNetwork} (first : First N) (emission : Payload) :
    SourceNativeProjectionLaw (Compiler.ledgerSource first.flow) where
  Projection := PUnit
  ActiveAt := fun _ {current} _ => PLift (current = true)
  InactiveAt := fun _ {current} _ => PLift (current ≠ true)
  classify := fun _ {current} _ =>
    letI : Decidable (current = true) := decEq (α := Bool) current true
    if active : current = true then .inl ⟨active⟩ else .inr ⟨active⟩
  PayloadAt := fun _ {_} _ _ => Payload
  project := fun _ {_} _ _ => emission

variable (prior : StateAt seed community cut) (emission : Payload) (writes : Bool)

set_option maxHeartbeats 700000 in
private def targetAt (event : ExactTemporalCausalRootEventAt
    prior.resident.root.toAuthoritativeRoot.toLedgerRoot prior.resident.visit) :
    SourceNativeSequentialActualActionTargetAt prior.resident.root prior.resident.visit event
      prior.resident.entry prior.resident.authority := by
  rw [event.eq_generated]
  let base := (first prior writes).sequentialTarget prior.resident rfl prior.resident.event
  let root := base.targetRoot.withProjectionCoface (component (first prior writes) emission)
  exact {
    base with
    targetRoot := root
    canonical_targetNextVisit_eq := Ingress.next_is_the_same_generated_successor
      root (first prior writes).initial (first prior writes).successor
    Answer := Payload
    answer := emission
    Receipt := fun read => ULift.{3, 0} (PLift (read = emission))
    receipt := ⟨⟨rfl⟩⟩ }

private def program : SourceNativeSequentialActualActionProgramAt
    prior.resident.root prior.resident.visit prior.resident.entry prior.resident.authority where
  targetAt := targetAt prior emission writes

def action := (program prior emission writes).generate prior.resident.event

private def landed : Resident prior.world :=
  let target := (action prior emission writes).target
  { V := target.TargetV
    root := target.targetRoot
    visit := target.targetVisit
    entry := target.targetEntry
    authority := target.targetAuthority
    unique := Compiler.occurrence_eq_emitted (first prior writes).flow }

private theorem the_material_face_is_at_the_first_write :
    (landed prior emission writes).visit.current = true :=
  Compiler.successor_current (first prior writes).flow false

private def landedFace :
    SourceNativeRootSemanticFaceAt (landed prior emission writes).root (landed prior emission writes).visit where
  projection := .component PUnit.unit
  active := ⟨the_material_face_is_at_the_first_write prior emission writes⟩
  classifier_eq := by
    let : Decidable ((landed prior emission writes).visit.current = true) :=
      decEq (α := Bool) (landed prior emission writes).visit.current true
    change (if active : (landed prior emission writes).visit.current = true then
      Sum.inl (PLift.up active) else Sum.inr (PLift.up active)) = _
    exact dif_pos (the_material_face_is_at_the_first_write prior emission writes)

def publish : Landed seed community cut Payload where
  state := {
    world := prior.world
    stack := prior.stack
    resident := landed prior emission writes
    exactSupport := by
      change (Compiler.emitted (first prior writes).flow (landed prior emission writes).visit.current).1 = _
      rw [the_material_face_is_at_the_first_write prior emission writes]
      exact prior.exactSupport }
  material := landedFace prior emission writes
  materialType := rfl

theorem the_canonical_write_is_the_published_whole_state :
    (⟨prior.world, (action prior emission writes).target.targetAnswerAndNext.nextCurrent⟩ :
      AnyAuthoritativeRootCurrent) = (publish prior emission writes).state.resident.erase :=
  congrArg (fun next => (⟨prior.world, next⟩ : AnyAuthoritativeRootCurrent))
    (action prior emission writes).target.targetAnswerAndNext_next_eq

theorem original_rows_are_the_whole_first_write :
    let written := (action prior emission writes).target.firstSuccessor.ledgerEvolution
    let original := (identityWhole prior.resident.support).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  ⟨(first prior writes).first_destination, (first prior writes).first_origin⟩

theorem earlier_reads_are_kept_at_the_landing
    (projection : prior.resident.root.source.base.projectionLaw.Projection) :
    let arrived := (publish prior emission writes).state.resident
    HEq (arrived.root.source.base.projectionLaw.outcomeAt (.inherited (.component projection))
      (arrived.root.emitted arrived.visit.current))
      (prior.resident.root.source.base.projectionLaw.outcomeAt projection
        (prior.resident.root.emitted prior.resident.visit.current)) := by
  let ledger := Compiler.ledgerSource (first prior writes).flow
  let base := (Compiler.livingRoot (first prior writes).flow).source.base
  let frozen := (first prior writes).inherit prior.resident
  let newMaterial := component (first prior writes) emission
  let install := (SourceNativeProjectionLaw.InstallationAt.componentCoface base frozen).trans
    (SourceNativeProjectionLaw.InstallationAt.inheritedCoface (base.withProjectionCoface frozen) newMaterial)
  let current := (landed prior emission writes).visit.current
  let occurrence := Compiler.emitted (first prior writes).flow current
  exact (install.outcome_heq occurrence projection).trans
    (QueryHistory.every_frozen_outcome_is_the_same_original_dependent_outcome
      prior.resident.root.source.base.projectionLaw
      (prior.resident.root.emitted prior.resident.visit.current) ledger occurrence projection)

theorem publish_reads_the_exact_payload :
    (publish prior emission writes).read = emission :=
  rfl

theorem publish_preserves_the_entire_stack :
    (publish prior emission writes).state.stack = prior.stack :=
  rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Installation.Core
