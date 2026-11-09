import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.First
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.QueryHistory

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint
open Capitalism.Universal.Root.Financial.Installation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Transport

noncomputable section

variable {N M : WorldRelationNetwork}

private def OriginExact (flow : Compiler.Flow N) (current : flow.Current)
    (image : SourceNativeLedgerEvolutionAt (Compiler.source flow) (Compiler.emitted flow current)) : Prop :=
  ∀ actual : SourceNativeLedgerGeneratedSuccessorAt (Compiler.emitted flow current) image,
    HEq actual.ledgerEvolution.origin (flow.evolution current).origin

private theorem successor_origin (flow : Compiler.Flow N) (current : flow.Current) :
    HEq (Compiler.successor flow current).ledgerEvolution.origin (flow.evolution current).origin := by
  have exactImage : OriginExact flow current
      ((Compiler.ledgerCompiler flow).compile (Compiler.emitted flow current)) := by
    dsimp only [Compiler.ledgerCompiler, Compiler.sourcePacket]
    split <;> intro actual <;> exact heq_of_eq (Compiler.patch_origin flow current)
  exact exactImage _

private theorem keys_from_write {s t u : N.Support} (same : t = u)
    (actual : LedgerWriteEvolutionAt N ⟨s⟩ ⟨t⟩) (chosen : Whole N s u)
    (destination : HEq actual.destination chosen.val.destination) (origin : HEq actual.origin chosen.val.origin) :
    KeepsKeys actual := by
  cases same
  constructor
  · intro entry
    rw [eq_of_heq destination]
    exact chosen.property.1 entry
  · intro entry
    rw [eq_of_heq origin]
    exact chosen.property.2 entry

namespace First

variable (first : First N)

def inherit (old : Resident M) : SourceNativeProjectionLaw (Compiler.ledgerSource first.flow) :=
  QueryHistory.freeze old.root.toAuthoritativeRoot.source.projectionLaw
    (old.root.emitted old.visit.current) (Compiler.ledgerSource first.flow)

variable (component : SourceNativeProjectionLaw (Compiler.ledgerSource first.flow))

abbrev rooted := (Compiler.livingRoot first.flow).withProjectionCoface component
abbrev initial := Compiler.initialVisit first.flow
abbrev successor := Compiler.successor first.flow false
abbrev landing := first.initial.next first.successor.next_eq

theorem first_support : first.successor.targetOccurrence.1 = first.after :=
  Compiler.successor_support first.flow false

theorem first_destination : HEq first.successor.ledgerEvolution.destination first.whole.val.destination :=
  Compiler.successor_destination first.flow false

theorem first_origin : HEq first.successor.ledgerEvolution.origin first.whole.val.origin :=
  successor_origin first.flow false

def draft (entry : OpenResponsibilityAt N first.before) : Draft N where
  resident := {
    V := Compiler.V first.flow
    root := first.rooted component
    visit := first.initial
    entry := entry
    authority := SourceNativeLivingTemporalCausalEntryAuthorityAt.generatedFromInitialRow
      (first.rooted component) entry (Compiler.generatedRow first.flow first.initial entry)
    unique := Compiler.occurrence_eq_emitted first.flow }
  write := first.successor
  nextUnique := Compiler.occurrence_eq_emitted first.flow
  keeps := keys_from_write first.first_support _ first.whole first.first_destination first.first_origin
  beforeFinite := first.beforeFinite
  afterFinite := cast (congrArg (fun s => Finite (OpenResponsibilityAt N s)) first.first_support.symm)
    first.afterFinite
  openFibres := first.openFibres

def landed (entry : OpenResponsibilityAt N first.before) : Resident N where
  V := Compiler.V first.flow
  root := first.rooted component
  visit := first.landing
  entry := (first.rooted component).toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
    first.successor.next_eq entry
  authority := (first.draft component entry).resident.authority.next first.successor.next_eq
  unique := Compiler.occurrence_eq_emitted first.flow

theorem landed_support (entry : OpenResponsibilityAt N first.before) :
    (first.landed component entry).support = first.after :=
  congrArg first.support (Compiler.successor_current first.flow false)

end First

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
