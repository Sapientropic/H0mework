import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Source
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Migration.Compiler
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Execution
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Physical.Public.Compiler

/-! One family of existing physical sources. The tag chooses a literal source;
it supplies neither a target state nor a replacement execution. -/

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Source.ProgrammeFace

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  (input : ProgrammeSource.Input Party Good Port Technology Instrument) (depth count : Nat)

inductive Tag where
  | review (datum : Admission.Datum input (Admission.frame input depth count)) (limit : Nat)
  | migration (prefixLimit renewalLimit : Nat)
  | actual (prefixLimit renewalLimit : Nat)
      (start : Registered.Physical.Cursor Party Good Port Technology Instrument)
  | publicActual (prefixLimit renewalLimit : Nat)
      (oldPast : List (Registered.Compile.RawInput Party Good Port Technology Instrument))
      (start : Registered.Physical.Cursor Party Good Port Technology Instrument)

def interpreter : Tag input depth count → RawLaw Party Good Port Technology Instrument
  | .publicActual .. => PublicFunction.physicalLaw input.law
  | .review .. | .migration .. | .actual .. => input.law

abbrev N := Migration.N input depth count

def V : Tag input depth count → ConstructiveRoot.Vocabulary
  | .review datum limit => Decision.Controller.V input depth count datum limit
  | .migration prefixLimit renewalLimit => Migration.V input depth count prefixLimit renewalLimit
  | .actual prefixLimit renewalLimit _ => Registered.Physical.V input depth count prefixLimit renewalLimit
  | .publicActual prefixLimit renewalLimit oldPast _ => Registered.Physical.Public.V input depth count prefixLimit renewalLimit oldPast

def ledgerRoot (tag : Tag input depth count) : SourceNativeLedgerRootClosure (N input depth count) (V input depth count tag) :=
  match tag with
  | .review datum limit => Epoch.ledgerRoot input depth count datum limit
  | .migration prefixLimit renewalLimit => {
      source := Migration.ledgerSource input depth count prefixLimit renewalLimit
      emitted := Migration.emitted input depth count prefixLimit renewalLimit
      compiler_commutes := fun _ => rfl }
  | .actual prefixLimit renewalLimit start => Registered.Physical.ledgerRoot input depth count prefixLimit renewalLimit start
  | .publicActual prefixLimit renewalLimit oldPast start =>
      Registered.Physical.Public.ledgerRoot input depth count prefixLimit renewalLimit oldPast start

abbrev root (tag : Tag input depth count) := (ledgerRoot input depth count tag).toRoot
abbrev Visit (tag : Tag input depth count) := RootVisit (root input depth count tag)

def rawAt : (tag : Tag input depth count) → (V input depth count tag).Current → RawCurrent Party Good Technology Instrument
  | .review _ _, current => current.raw
  | .migration prefixLimit renewalLimit, current => Migration.rawAt input depth count prefixLimit renewalLimit current
  | .actual prefixLimit renewalLimit _, current =>
      (Registered.Physical.stateAt input depth count prefixLimit renewalLimit current.past).raw
  | .publicActual prefixLimit renewalLimit oldPast _, current =>
      (Registered.Physical.Public.stateAt input depth count prefixLimit renewalLimit oldPast current.past).raw

def execution : (tag : Tag input depth count) → (V input depth count tag).Current →
    ExecutionResult Party Good Port Technology Instrument
  | .review datum limit, current => Decision.Controller.actualExecution input depth count datum limit current
  | .migration prefixLimit renewalLimit, current =>
      match Migration.wordAt input depth count prefixLimit renewalLimit current with
      | some word => input.law.execute (Migration.rawAt input depth count prefixLimit renewalLimit current) 0 word
      | none => ⟨Migration.rawAt input depth count prefixLimit renewalLimit current, []⟩
  | .actual prefixLimit renewalLimit _, current => Registered.Physical.execution input depth count prefixLimit renewalLimit current
  | .publicActual prefixLimit renewalLimit oldPast _, current => Registered.Physical.Public.execution input depth count prefixLimit renewalLimit oldPast current

def entry (tag : Tag input depth count) (visit : Visit input depth count tag) :
    OpenResponsibilityAt (N input depth count) ((root input depth count tag).supportAt visit.current) := by
  cases tag with
  | review datum limit =>
      exact Decision.Controller.entryAt input depth count datum limit
        (Decision.Controller.emitted input depth count datum limit visit.current)
  | migration prefixLimit renewalLimit =>
      exact (Admission.frame input depth count).native.entrySupport
        (Continuation.oldSupport input (Admission.frame input depth count))
  | actual prefixLimit renewalLimit start =>
      exact (Admission.frame input depth count).native.entrySupport
        (Continuation.oldSupport input (Admission.frame input depth count))
  | publicActual prefixLimit renewalLimit oldPast start =>
      exact (Admission.frame input depth count).native.entrySupport
        (Continuation.oldSupport input (Admission.frame input depth count))

def body (tag : Tag input depth count) (visit : Visit input depth count tag) : Origin Party Good Port Technology Instrument :=
  ⟨rawAt input depth count tag visit.current,
    (execution input depth count tag visit.current).items.map ExecutionItem.request⟩

theorem body_is_the_same_actual_inventory (tag : Tag input depth count) (visit : Visit input depth count tag) :
    (interpreter input depth count tag).rawItems (body input depth count tag visit).1 (body input depth count tag visit).2 =
      (execution input depth count tag visit.current).items := by
  cases tag with
  | review datum limit =>
      exact congrArg ExecutionResult.items (Epoch.execution_is_original_replay input depth count datum limit visit.current)
  | migration prefixLimit renewalLimit =>
      dsimp only [body, execution, rawAt, interpreter]
      cases observed : Migration.wordAt input depth count prefixLimit renewalLimit visit.current with
      | some word => simp only [RawLaw.inventory_requests_exact, RawLaw.rawItems]
      | none => rfl
  | actual prefixLimit renewalLimit start =>
      exact Registered.Physical.body_is_the_same_actual_inventory input depth count prefixLimit renewalLimit visit.current
  | publicActual prefixLimit renewalLimit oldPast start =>
      exact Registered.Physical.Public.body_is_the_same_actual_inventory input depth count prefixLimit renewalLimit oldPast visit.current

theorem actual_source_is_the_literal_ledger_root (prefixLimit renewalLimit : Nat)
    (start : Registered.Physical.Cursor Party Good Port Technology Instrument) :
    ledgerRoot input depth count (.actual prefixLimit renewalLimit start) =
      Registered.Physical.ledgerRoot input depth count prefixLimit renewalLimit start := rfl

theorem public_interpreter_is_the_literal_generated_law (prefixLimit renewalLimit : Nat)
    (oldPast : List (Registered.Compile.RawInput Party Good Port Technology Instrument))
    (start : Registered.Physical.Cursor Party Good Port Technology Instrument) :
    interpreter input depth count (.publicActual prefixLimit renewalLimit oldPast start) = PublicFunction.physicalLaw input.law := rfl

structure ActualItem where
  tag : Tag input depth count
  visit : Visit input depth count tag
  position : Fin (execution input depth count tag visit.current).items.length

def ActualItem.instruction (item : ActualItem input depth count) : ExecutionItem Party Good Port Technology Instrument :=
  (execution input depth count item.tag item.visit.current).items.get item.position

def ActualItem.row (item : ActualItem input depth count) := entry input depth count item.tag item.visit

def ActualItem.causalDepth (item : ActualItem input depth count) : Nat :=
  ProductiveFiniteRootHistoryAt.causalDepth item.visit.history

theorem ActualItem.original_inventory (item : ActualItem input depth count) :
    item.instruction input depth count ∈ (execution input depth count item.tag item.visit.current).items := List.get_mem _ _

theorem different_source_tags_have_different_origins (first second : ActualItem input depth count)
    (different : first.tag ≠ second.tag) : first ≠ second := fun same => different (congrArg ActualItem.tag same)

theorem different_actual_epochs_have_different_origins (first second : ActualItem input depth count)
    (different : first.causalDepth input depth count ≠ second.causalDepth input depth count) : first ≠ second :=
  fun same => different (congrArg (ActualItem.causalDepth input depth count) same)

theorem review_and_migration_cannot_share_an_origin
    (datum : Admission.Datum input (Admission.frame input depth count)) (limit prefixLimit renewalLimit : Nat)
    (first second : ActualItem input depth count)
    (review : first.tag = .review datum limit) (migration : second.tag = .migration prefixLimit renewalLimit) : first ≠ second := by
  apply different_source_tags_have_different_origins input depth count first second
  rw [review, migration]
  intro impossible
  cases impossible

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface

#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.body_is_the_same_actual_inventory
#print axioms SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Epoch.Interface.review_and_migration_cannot_share_an_origin
