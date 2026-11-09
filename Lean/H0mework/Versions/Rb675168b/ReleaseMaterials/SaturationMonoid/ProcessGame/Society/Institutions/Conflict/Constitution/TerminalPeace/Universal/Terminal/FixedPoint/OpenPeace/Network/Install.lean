import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Runtime.LocalU7
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Source
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network.Audit
import H0mework.Versions.Rb675168b.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Dispatch

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open ObstructionGeneratedMinimalCoface
open Reparation.Actual (First identityWhole)

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port]
  [DecidableEq Instrument] [DecidableEq Community]
  {seed cut : Conflict.Root.Cut Party Good Port Technology Instrument} {community : Party → Community}

variable (prior : Installation.Live.Ledger seed community cut)
  (grammar : Language (RawEvent Party Good Port Technology Instrument) (Effect Party Good Port Technology Instrument))
  (observed : Set (Effect Party Good Port Technology Instrument))
  (lane : LocalU7 prior.world)
  (novel : ¬ observed ⊆ grammar.covered)

local notation "N₀" => LocalU7.asWorld lane
local notation "Focus" => prior.resident.support
local notation "Bearer" => prior.resident.entry
local notation "OldTheory" => LocalU7.restrictTheory lane prior.resident.root.source.base.lawSurface
local notation "N₁" => world N₀ Focus Bearer grammar observed
local notation "Translation" => translation N₀ Focus Bearer grammar observed
local notation "Theory" => theory N₀ Focus Bearer grammar observed OldTheory
local notation "Obstruction" => obstruction N₀ Focus Bearer grammar observed novel
local notation "Failure" => failure N₀ Focus Bearer grammar observed OldTheory novel
local notation "Calculus" => calculus N₀ Focus Bearer grammar observed (LocalU7.producer lane) (LocalU7.calculus lane)
local notation "AuditEvent" => U7ActualSuccessorSource.emit (U7ObstructionEvolutionCalculus.source Calculus) Obstruction
local notation "Token" => SourceNativeRootExpressibilityFailureTokenAt Failure Calculus AuditEvent
local notation "Change" =>
  WorldRelationNetwork.SemanticChangeAt N₁ Focus
    (OpenResponsibilityAt.claim (inheritedBearer N₀ Focus Bearer grammar observed))
    (WorldRelationNetwork.obstructionClaim N₁ Obstruction)

def auditFirst : First N₁ where
  before := Focus
  after := Focus
  whole := identityWhole (N := N₁) Focus
  beforeFinite := prior.ready.finite
  afterFinite := prior.ready.finite
  openFibres := prior.ready.fibres
  writes := true

local notation "FirstWrite" => auditFirst prior grammar observed lane

inductive Projection
  | effect
  | failure

def auditProjection : SourceNativeProjectionLaw (Compiler.ledgerSource (FirstWrite).flow) where
  Projection := Projection
  ActiveAt := fun _ {current} _ => PLift (current = true)
  InactiveAt := fun _ {current} _ => PLift (current ≠ true)
  classify := fun _ {current} _ =>
    letI : Decidable (current = true) := decEq (α := Bool) current true
    if h : current = true then .inl ⟨h⟩ else .inr ⟨h⟩
  PayloadAt := fun projection {_} _ _ => match projection with
    | .effect => Set (Effect Party Good Port Technology Instrument) × Change
    | .failure => Token
  project := fun projection {_} _ _ => match projection with
    | .effect => ⟨observed \ grammar.covered, residualChange N₀ Focus Bearer grammar observed novel⟩
    | .failure => .canonical

def auditBase := sourceWithTheory FirstWrite Theory

def auditRoot : SourceNativeLivingRootClosure N₁ (Compiler.V (FirstWrite).flow) :=
  let root := auditBase prior grammar observed lane
  let inherited := (FirstWrite).inherit prior.resident
  (root.withProjectionCoface inherited).withProjectionCoface
    (auditProjection prior grammar observed lane novel)

local notation "Root" => auditRoot prior grammar observed lane novel

private def occurrences : ConstructivePresentation
    (prior.resident.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt prior.resident.visit.current)
    ((Root).toAuthoritativeRoot.toRoot.actual.OccurrenceAt false) where
  forward := fun _ => (Root).emitted false
  backward := fun _ => prior.resident.root.emitted prior.resident.visit.current
  backward_forward := fun old => (prior.resident.unique old).symm
  forward_backward := fun new => (Compiler.occurrence_eq_emitted (FirstWrite).flow new).symm

set_option maxHeartbeats 600000 in
private def targetAt (event : ExactTemporalCausalRootEventAt
    prior.resident.root.toAuthoritativeRoot.toLedgerRoot prior.resident.visit) :
    SourceNativeSequentialActualActionTargetAt prior.resident.root prior.resident.visit event
      prior.resident.entry prior.resident.authority where
  TargetN := N₁
  translation := { __ := Translation }
  TargetV := Compiler.V (FirstWrite).flow
  targetRoot := Root
  targetTheory := Theory
  lawSurface_heq := HEq.rfl
  targetTheory_rootSemantic := theory_conservative N₀ Focus Bearer grammar observed OldTheory
  occurrencePresentation := occurrences prior grammar observed lane novel
  occurrence_commutes := rfl
  initialSupport_heq := HEq.rfl
  initialOpenLedger := (Translation).oldOpenLedger Focus
  initialOpenLedger_heq := HEq.rfl
  initialLedger_responsibility_commutes := fun _ => rfl
  initialLedger_claim_commutes := fun _ => rfl
  initialLedger_budget_conservative := fun _ => Nat.le_refl _
  initialLedgerNoFresh := fun row => ⟨⟨⟨row.1, row.2⟩, ⟨rfl⟩⟩⟩
  translatedSourceEntryRow := Compiler.generatedRow (FirstWrite).flow (FirstWrite).initial
    (inheritedBearer N₀ Focus Bearer grammar observed)
  firstSuccessor := (FirstWrite).successor
  canonical_targetNextVisit_eq :=
    Ingress.next_is_the_same_generated_successor Root (FirstWrite).initial (FirstWrite).successor
  Answer := Set (Effect Party Good Port Technology Instrument)
  answer := observed \ grammar.covered
  Receipt := fun read => ULift.{3, 0} (PLift (read = observed \ grammar.covered))
  receipt := ⟨⟨rfl⟩⟩

/-- The restricted theory is entered by the original resident's actual
sequential action. The initial ledger includes exactly the original rows. -/
def install :=
  let program : SourceNativeSequentialActualActionProgramAt prior.resident.root prior.resident.visit
      prior.resident.entry prior.resident.authority :=
    ⟨targetAt prior grammar observed lane novel⟩
  program.generate prior.resident.event

local notation "Installed" => SourceGeneratedSequentialActualActionAt.target (install prior grammar observed lane novel)

def auditResident : Reparation.Actual.Resident N₁ where
  V := (Installed).TargetV
  root := (Installed).targetRoot
  visit := (Installed).targetVisit
  entry := (Installed).targetEntry
  authority := (Installed).targetAuthority
  unique := Compiler.occurrence_eq_emitted (FirstWrite).flow

theorem audit_lands_at_first_write :
    (auditResident prior grammar observed lane novel).visit.current = true :=
  Compiler.successor_current (FirstWrite).flow false

theorem audit_support :
    (auditResident prior grammar observed lane novel).support = Focus :=
  congrArg (FirstWrite).support (audit_lands_at_first_write prior grammar observed lane novel)

theorem audit_bearer_kept :
    HEq (auditResident prior grammar observed lane novel).entry
      (inheritedBearer N₀ Focus Bearer grammar observed) := by
  let target := Installed
  let successor := target.firstSuccessor
  have actual := Compiler.canonical_destination_heq target.targetRoot.toAuthoritativeRoot.toLedgerRoot
    _ _ successor.next_eq successor target.translatedSourceEntry
  exact actual.trans (Reparation.Transport.destination_congr rfl (FirstWrite).first_support
    successor.ledgerEvolution (FirstWrite).whole.val (FirstWrite).first_destination
    target.translatedSourceEntry (inheritedBearer N₀ Focus Bearer grammar observed) HEq.rfl)

theorem audit_whole_first_write :
    let written := (Installed).firstSuccessor.ledgerEvolution
    let original := (identityWhole (N := N₁) Focus).val
    HEq written.destination original.destination ∧ HEq written.origin original.origin :=
  ⟨(FirstWrite).first_destination, (FirstWrite).first_origin⟩

theorem audit_is_canonical_next :
    (⟨N₁, (Installed).targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      (auditResident prior grammar observed lane novel).erase :=
  congrArg (fun next => (⟨N₁, next⟩ : AnyAuthoritativeRootCurrent)) (Installed).targetAnswerAndNext_next_eq

def installedEffect : SourceNativeRootSemanticFaceAt
    (auditResident prior grammar observed lane novel).root
    (auditResident prior grammar observed lane novel).visit where
  projection := .component .effect
  active := ⟨audit_lands_at_first_write prior grammar observed lane novel⟩
  classifier_eq := by
    let arrived := auditResident prior grammar observed lane novel
    let : Decidable (arrived.visit.current = true) := decEq (α := Bool) arrived.visit.current true
    change (if active : arrived.visit.current = true then
      Sum.inl (PLift.up active) else Sum.inr (PLift.up active)) = _
    exact dif_pos (audit_lands_at_first_write prior grammar observed lane novel)

theorem installed_effect_is_exact :
    HEq (installedEffect prior grammar observed lane novel).rootRead
      (⟨observed \ grammar.covered, residualChange N₀ Focus Bearer grammar observed novel⟩ :
        Set (Effect Party Good Port Technology Instrument) × Change) :=
  HEq.rfl

def installedToken : SourceNativeRootSemanticFaceAt
    (auditResident prior grammar observed lane novel).root
    (auditResident prior grammar observed lane novel).visit where
  projection := .component .failure
  active := ⟨audit_lands_at_first_write prior grammar observed lane novel⟩
  classifier_eq := by
    let arrived := auditResident prior grammar observed lane novel
    let : Decidable (arrived.visit.current = true) := decEq (α := Bool) arrived.visit.current true
    change (if active : arrived.visit.current = true then
      Sum.inl (PLift.up active) else Sum.inr (PLift.up active)) = _
    exact dif_pos (audit_lands_at_first_write prior grammar observed lane novel)

theorem installed_token_is_exact :
    HEq (installedToken prior grammar observed lane novel).rootRead
      (SourceNativeRootExpressibilityFailureTokenAt.canonical : Token) :=
  HEq.rfl

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Constitution.TerminalPeace.Universal.Terminal.FixedPoint.OpenPeace.Network
