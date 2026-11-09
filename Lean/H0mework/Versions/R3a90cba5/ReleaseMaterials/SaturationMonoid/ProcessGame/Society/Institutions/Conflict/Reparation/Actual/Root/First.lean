import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Write

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Root.Financial.Installation
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Transport

noncomputable section

variable {N : WorldRelationNetwork}

/-- The original live occurrence and its own focus entry. All other open
rows travel with the same visit. -/
structure Resident (N : WorldRelationNetwork) where
  V : ConstructiveRoot.Vocabulary
  root : SourceNativeLivingRootClosure N V
  visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot
  entry : OpenResponsibilityAt N (root.emitted visit.current).1
  authority : SourceNativeLivingTemporalCausalEntryAuthorityAt root visit entry
  unique : ∀ actual : root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt visit.current,
    actual = root.emitted visit.current

namespace Resident

variable (resident : Resident N)

abbrev support : N.Support := (resident.root.emitted resident.visit.current).1
abbrev event := resident.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt resident.visit

def erase : AnyAuthoritativeRootCurrent :=
  ⟨N, ⟨resident.V, resident.root.toAuthoritativeRoot, resident.visit⟩⟩

end Resident

/-- The selected first write at this occurrence, available before any new
responsibility coordinate is attached to that very write. -/
structure Draft (N : WorldRelationNetwork) where
  resident : Resident N
  write : SourceNativeLedgerGeneratedSuccessorAt (resident.root.emitted resident.visit.current)
    (resident.root.toAuthoritativeRoot.toLedgerRoot.generatedLedgerAt resident.visit.current)
  nextUnique : ∀ actual : resident.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt write.targetCurrent,
    actual = resident.root.emitted write.targetCurrent
  keeps : KeepsKeys write.ledgerEvolution
  beforeFinite : Finite (OpenResponsibilityAt N resident.support)
  afterFinite : Finite (OpenResponsibilityAt N write.targetOccurrence.1)
  openFibres : ∀ support row, Subsingleton (N.OpenAt support row)

namespace Draft

variable (draft : Draft N)

abbrev afterSupport : N.Support := draft.write.targetOccurrence.1
abbrev whole : Whole N draft.resident.support draft.afterSupport := ⟨draft.write.ledgerEvolution, draft.keeps⟩

def enter : Resident N where
  V := draft.resident.V
  root := draft.resident.root
  visit := draft.resident.visit.next draft.write.next_eq
  entry := draft.resident.root.toAuthoritativeRoot.toLedgerRoot.canonicalTargetEntryAtNext
    draft.write.next_eq draft.resident.entry
  authority := draft.resident.authority.next draft.write.next_eq
  unique := by
    intro actual
    exact draft.nextUnique actual

theorem enter_support : draft.enter.support = draft.afterSupport :=
  (congrArg (fun occurrence => occurrence.1) (draft.nextUnique draft.write.targetOccurrence)).symm

theorem enter_is_the_canonical_next :
    (⟨N, (draft.resident.root.generatedCausalEntryAnswerAndNextAt draft.resident.visit
      draft.resident.entry draft.resident.authority).nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      draft.enter.erase :=
  congrArg (fun next => (⟨N, next⟩ : AnyAuthoritativeRootCurrent))
    (Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      draft.resident.root draft.resident.visit draft.write)

end Draft

def identityWhole (support : N.Support) : Whole N support support :=
  ⟨{ destination := fun row => ⟨row, .carried rfl HEq.rfl⟩
     origin := fun row => ⟨row, .carried rfl HEq.rfl⟩ },
   ⟨fun _ => rfl, fun _ => rfl⟩⟩

structure First (N : WorldRelationNetwork) where
  before : N.Support
  after : N.Support
  whole : Whole N before after
  beforeFinite : Finite (OpenResponsibilityAt N before)
  afterFinite : Finite (OpenResponsibilityAt N after)
  openFibres : ∀ support row, Subsingleton (N.OpenAt support row)
  writes : Bool

namespace First

variable (first : First N)

def support : Bool → N.Support
  | false => first.before
  | true => first.after

def wholeAt : (cursor : Bool) → Whole N (first.support cursor) first.after
  | false => first.whole
  | true => identityWhole first.after

def flow : Compiler.Flow N where
  Current := Bool
  initial := false
  support := first.support
  next := fun _ => true
  writes := fun cursor => !cursor && first.writes
  evolution := fun cursor => (first.wholeAt cursor).val
  finite := fun cursor => match cursor with
    | false => first.beforeFinite
    | true => first.afterFinite
  injective := fun cursor =>
    let keys := (first.wholeAt cursor).property
    ⟨keys_imply_origin_injective _ keys first.openFibres, keys_imply_destination_injective _ keys first.openFibres⟩
  open_fibres := first.openFibres

end First

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual
