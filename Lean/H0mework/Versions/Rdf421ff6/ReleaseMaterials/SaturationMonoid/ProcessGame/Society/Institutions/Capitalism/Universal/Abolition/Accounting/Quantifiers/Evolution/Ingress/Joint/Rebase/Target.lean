import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase.Source
import H0mework.Versions.R2.Foundation.Source.SequentialAction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open Source.Program Innovation Quantifiers.Joint

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {mechanism : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : mechanism.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)}
  (seed : Global.Seed (mechanism := mechanism) (past := past) (nature := nature) (response := response))
  (grossClaim : Entitlement.Source.Claim (Quantifiers.Joint.window seed))

local notation "oldRoot" => Origin.root seed grossClaim
local notation "newRoot" => root seed grossClaim
local notation "initial" => Abolition.Accounting.Root.Compiler.initialVisit (flow seed grossClaim)
local notation "first" => Abolition.Accounting.Root.Compiler.successor (flow seed grossClaim) Stage.pending

def occurrencePresentation : ConstructivePresentation
    ((oldRoot).toAuthoritativeRoot.toRoot.actual.OccurrenceAt seed.current.visit.current)
    ((newRoot).toAuthoritativeRoot.toRoot.actual.OccurrenceAt Stage.pending) where
  forward := fun _ => (newRoot).emitted Stage.pending
  backward := fun _ => (oldRoot).emitted seed.current.visit.current
  backward_forward := fun occurrence => (seed.current.occurrence_eq seed.current.visit.current occurrence).symm
  forward_backward := fun occurrence => (Abolition.Accounting.Root.Compiler.occurrence_eq_emitted (flow seed grossClaim) occurrence).symm

def initialLedger := (translation seed grossClaim).oldOpenLedger (oldSupport seed)

def targetAt (event : ExactTemporalCausalRootEventAt (oldRoot).toAuthoritativeRoot.toLedgerRoot seed.current.visit) :
    SourceNativeSequentialActualActionTargetAt oldRoot seed.current.visit event seed.current.row
      (Origin.authority seed grossClaim) := by
  rw [event.eq_generated]
  exact {
    TargetN := NewN seed grossClaim
    translation := translation seed grossClaim
    TargetV := V seed grossClaim
    targetRoot := newRoot
    targetTheory := TheoryState.rootSemantic (NewN seed grossClaim)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation seed grossClaim
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := initialLedger seed grossClaim
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := each_original_row_keeps_its_actual_translated_key seed grossClaim (oldSupport seed)
    initialLedger_claim_commutes := (translation seed grossClaim).oldOpenClaim_commutes (oldSupport seed)
    initialLedger_budget_conservative := fun row =>
      ((translation seed grossClaim).oldOpenProgressBudget_commutes (oldSupport seed) row).le
    initialLedgerNoFresh := fun row => ⟨⟨(initialLedger seed grossClaim).backward row,
      ⟨no_row_is_created_or_deleted_in_the_initial_representation seed grossClaim (oldSupport seed) row⟩⟩⟩
    translatedSourceEntryRow := Abolition.Accounting.Root.Compiler.generatedRow (flow seed grossClaim) initial
      ((initialLedger seed grossClaim).forward seed.current.row)
    firstSuccessor := first
    canonical_targetNextVisit_eq := Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      (newRoot) initial first
    Answer := Current seed grossClaim
    answer := Current.initial seed grossClaim
    Receipt := fun answer => ULift.{3,0} (PLift
      (answer = Current.initial seed grossClaim ∧ answer.raw = (productiveState seed).raw ∧
        answer.productive = (productiveState seed).remaining ∧
        answer.productiveDeclared = (productiveState seed).declared ∧
        answer.gross = (Entitlement.Duty.State.initial grossClaim).remaining))
    receipt := ⟨⟨rfl,rfl,rfl,rfl,rfl⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt oldRoot seed.current.visit seed.current.row
    (Origin.authority seed grossClaim) where
  targetAt := targetAt seed grossClaim

def generated := (program seed grossClaim).generate
  ((oldRoot).toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt seed.current.visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Ingress.Joint.Rebase
