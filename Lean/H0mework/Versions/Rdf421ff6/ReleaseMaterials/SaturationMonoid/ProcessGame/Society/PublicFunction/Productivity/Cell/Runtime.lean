import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Validation
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Openness
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Feedback.Accounting
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Finance
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Audit.Contract

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Root
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Source.ProgrammeControl

abbrev previousRoot := OutstandingSource.NativeService.Runtime.root source
abbrev previousFacade := OutstandingSource.NativeService.Runtime.facade source

structure ActualTail (depth : Nat) where
  response : Feedback.Outcome (source.currentAt (depth + 1))
  selected : response = Feedback.respond (source.currentAt (depth + 1))
  submitted : (source.actualExecution depth).submitted = response.word
  written : (source.writtenReceipt depth).val = .original (source.currentAt (depth + 1)) response.word
  remaining : List (Feedback.Deficit (source.actualExecution depth).after
    (Feedback.parent (source.currentAt (depth + 1))))
  remaining_generated : remaining = Feedback.deficits (source.actualExecution depth).after
    (Feedback.parent (source.currentAt (depth + 1)))
  keeps_claims : 10 ≤ depth →
    (source.actualExecution depth).after.claims = (source.actualExecution depth).before.claims
  inventoryActors : List Party
  inventory_generated : inventoryActors = Feedback.participants (depth + 2)
  inventory_complete : ∀ actor ∉ inventoryActors, ∀ good,
    (source.actualExecution depth).after.stock actor good = 0
  inventory_accounted : ∀ actor good,
    Feedback.stockFromReceipts (depth + 2) actor good = (source.actualExecution depth).after.stock actor good
  financialAccount : (Financial.process source.input).GeneratedState
  financial_generated : financialAccount = Finance.account (depth + 2)
  financial_matrix : Financial.BalanceConservation.ledgerClaims source.input financialAccount.current =
    (source.actualExecution depth).after.claims
  financial_crossing : (Financial.process source.input).Run
    (Finance.account (depth + 1)).current financialAccount.current
  financial_origins : (Finance.account (depth + 1)).current.slots.map (Financial.slotClaim source.input) <+:
    financialAccount.current.slots.map (Financial.slotClaim source.input)
  financial_history : (Finance.account (depth + 1)).current.history <+: financialAccount.current.history
  audit : Audit.Result (depth + 2)
  audit_generated : audit = Audit.generate (depth + 2)
  no_capital : (source.currentAt (depth + 1)).technology.1 = true →
    ¬ Nonempty (Kernel.CapitalRelationKernel law (source.currentAt (depth + 1)) response.word)
  own_resources : ∀ item ∈ law.rawItems (source.currentAt (depth + 1)) response.word,
    law.Valid item.before item.request →
      ∀ entry ∈ law.debit item.before item.request, entry.1.1 = item.request.signer

def actualTail (depth : Nat) : Option (ActualTail depth) :=
  if ready : 2 ≤ depth + 1 ∧ source.pendingSlots (source.frameAt (depth + 1)).payments = [] then
    some {
      response := Feedback.respond (source.currentAt (depth + 1))
      selected := rfl
      remaining := Feedback.deficits (source.actualExecution depth).after
        (Feedback.parent (source.currentAt (depth + 1)))
      remaining_generated := rfl
      keeps_claims := Feedback.every_actual_response_keeps_old_claims depth
      inventoryActors := Feedback.participants (depth + 2)
      inventory_generated := rfl
      inventory_complete := by
        intro actor outside good
        rw [source.actual_execution_after, ← raw_current_frame]
        exact Feedback.outside_generated_support_has_zero_stock _ actor good outside
      inventory_accounted := by
        intro actor good
        rw [source.actual_execution_after, ← raw_current_frame]
        exact Feedback.receipt_consumer_matches_every_actor _ actor good
      financialAccount := Finance.account (depth + 2)
      financial_generated := rfl
      financial_matrix := by
        rw [source.actual_execution_after, ← raw_current_frame]
        exact Finance.all_native_positions_are_the_actual_claims _
      financial_crossing := Finance.continuation (depth + 1) 1
      financial_origins := (Finance.original_issues_and_native_history_survive (depth + 1) 1).1
      financial_history := (Finance.original_issues_and_native_history_survive (depth + 1) 1).2
      audit := Audit.generate (depth + 2)
      audit_generated := rfl
      no_capital := no_capital_kernel _ _
      own_resources := fun item _inside valid => valid_debits_only_the_signer _ _ valid
      submitted := by
        rw [source.actual_execution_word, ← (source.canonical_frame (depth + 1)).2]
        exact source.completed_word_is_source_continuation (depth + 1) 0 ready.1 ready.2 rfl
      written := by
        rw [source.written_report_exact]
        unfold OutstandingSource.reportAt
        rw [source.ordinal_exact, if_neg (by omega)]
        unfold OutstandingSource.decideAt
        rw [show source.incoming? (source.currentAt (depth + 1)) = none from rfl, dif_pos ready.2]
        rfl }
  else none

theorem generated_tail (depth : Nat) (started : 2 ≤ depth + 1) :
    ∃ tail, actualTail depth = some tail := by
  have complete := source.completion_persists 2 (depth - 1) original_service_paid
  have ready : source.pendingSlots (source.frameAt (depth + 1)).payments = [] := by
    simpa only [show 2 + (depth - 1) = depth + 1 by omega] using complete
  unfold actualTail
  rw [dif_pos ⟨started, ready⟩]
  exact ⟨_, rfl⟩

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource source.input).restructuringSource.toLedgerSource where
  Projection := Unit
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun _ {current} _ _ =>
    (depth : Nat) → current = (ProgrammeHistory.visitAt source.input (depth + 1)).current →
      Option (ActualTail depth)
  project := fun _ {_} _ _ depth _canonical => actualTail depth

def root := previousRoot.withProjectionCoface projectionLaw

theorem original_root_is_preserved :
    root.toAuthoritativeRoot.toRoot = (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.toRoot := rfl

def stateAt (ordinal : Nat) : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) :=
  ⟨ProgrammeSource.V source.input, root, ProgrammeHistory.temporalVisit source.input ordinal⟩

def process : SourceNativeLivingRootProcess (ProgrammeSource.N source.input) where
  State := Nat
  stateAt := stateAt
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N source.input) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt source.input first).current =
        (ProgrammeHistory.visitAt source.input second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective source.input currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : OutstandingSource.NativeService.Runtime.Face source)
  | productivity

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N source.input) where
  process := process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => previousFacade.componentAt previousFacade.seed previous
    | .productivity => projectionLaw
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
        exact (previousFacade.installationAt previousFacade.seed previous).trans
          (SourceNativeProjectionLaw.InstallationAt.inheritedCoface previousRoot.toAuthoritativeRoot.source projectionLaw)
    | productivity => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
  projectionAt := fun _ face => match face with
    | .previous previous => previousFacade.projectionAt previousFacade.seed previous
    | .productivity => ()

def activated (ordinal : Nat) : LivingRuntimeState process := facade.seed.advance ordinal

theorem activated_state (ordinal : Nat) : (activated ordinal).state = ordinal := by
  induction ordinal with
  | zero => rfl
  | succ ordinal ih => exact congrArg Nat.succ ih

theorem payload_is_actual (depth : Nat) :
    projectionLaw.project () (ProgrammeSource.emitted source.input
      (ProgrammeHistory.visitAt source.input (depth + 1)).current) () depth rfl = actualTail depth := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.Runtime
