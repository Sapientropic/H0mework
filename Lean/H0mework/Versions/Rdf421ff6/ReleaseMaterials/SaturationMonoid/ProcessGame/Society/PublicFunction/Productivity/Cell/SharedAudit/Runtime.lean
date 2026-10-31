import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Responsibility

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal.Source.Program
open Institutions.Capitalism.Universal.Root
open OutstandingSource.NativeService

structure MethodCertificate where
  method : PaidMethod
  generated : method = originalMethod
  before : method.before = source.currentAt 4
  word : method.word = (source.actualExecution 3).submitted
  original : method.item ∈ (source.actualExecution 3).interpreted.items
  paid : flowAt (law.actualDebit method.item.before method.item.request) 0 .labor = 1
  stored : (frameAt 5).method = some method
  next : (source.actualExecution 3).after = source.currentAt 5

def methodCertificate : MethodCertificate where
  method := originalMethod
  generated := rfl
  before := actual_paid_method_origin.1
  word := actual_paid_method_origin.2.1
  original := actual_paid_method_origin.2.2.1
  paid := actual_paid_method_origin.2.2.2
  stored := original_method_is_kept 0
  next := (source.actualExecution 3).root_next_exact

structure Certificate where
  amount : ℚ
  generated_amount : amount = laborDividend
  positive : 0 < amount
  method : MethodCertificate
  reuse : (source.actualExecution 6).submitted = method.method.plan 2
  inventory : ∀ actor good, (source.currentAt 11).stock actor good =
    (Cell.source.currentAt 11).stock actor good + if actor = 0 ∧ good = .labor then 1 else 0
  debits : ∀ actor good, law.totalDebit (receipts source 11) actor good +
    (if actor = 0 ∧ good = .labor then 1 else 0) = law.totalDebit (receipts Cell.source 11) actor good
  credits : ∀ actor good, law.totalCredit (receipts source 11) actor good =
    law.totalCredit (receipts Cell.source 11) actor good
  floor : ∀ item ∈ receipts source 11, ∀ actor : Party,
    ((actor < 3 ∨ 0 < item.before.stock actor .seed) →
      1 ≤ item.before.stock actor .life ∧ 1 ≤ item.before.stock actor .spare) ∧
    ((actor < 3 ∨ 0 < (law.step item.before item.request).stock actor .seed) →
      1 ≤ (law.step item.before item.request).stock actor .life ∧
        1 ≤ (law.step item.before item.request).stock actor .spare)
  carrier : source.currentAt 11 = withLabor (Cell.source.currentAt 11) 1
  continuation : ∀ word, (∀ item ∈ law.rawItems (Cell.source.currentAt 11) word, law.Valid item.before item.request) →
    (∀ item ∈ law.rawItems (source.currentAt 11) word, law.Valid item.before item.request) ∧
      (law.execute (source.currentAt 11) 0 word).final =
        withLabor (law.execute (Cell.source.currentAt 11) 0 word).final 1
  native : (index : source.Slot) → Prefix source index 10
  archives : ∀ index, (native index).state = (historyAt source index 1).state
  finance : Financial.BalanceConservation.ledgerClaims source.input (financialAccount 11).current =
    (source.currentAt 11).claims
  financeRun : (Financial.process source.input).Run (financialAccount 0).current (financialAccount 11).current
  no_capital : ∀ word, ¬ Nonempty
    (Institutions.Capitalism.Universal.Source.ProgrammeControl.Kernel.CapitalRelationKernel law (source.currentAt 11) word)
  row : ProgrammeLedger.transferReceiptOf source.input (source.taskWrite 9).2 = some (source.writtenReceipt 9)
  written : (source.writtenReceipt 9).val = source.reportAt (source.currentAt 10)
  next : (source.actualExecution 9).after = source.currentAt 11

def certificate : Certificate where
  amount := laborDividend
  generated_amount := rfl
  positive := exact_strict_labor_dividend.2
  method := methodCertificate
  reuse := actual_reuse_consumes_the_original_paid_programme.1
  inventory := complete_inventory_difference
  debits := complete_debit_difference
  credits := complete_credits_equal
  floor := every_actual_cut_keeps_all_original_and_seeded_bearers
  carrier := actual_final_current_is_the_same_carrier_plus_one_labor
  continuation := actual_dividend_preserves_every_old_executable_continuation
  native := fun index => historyAt source index 10
  archives := fun index => native_original_archives_survive index 9
  finance := native_financial_matrix 11
  financeRun := financialRun
  no_capital := every_later_word_has_no_capital_relation 8
  row := source.receipt_is_in_original_task_write 9
  written := source.written_report_exact 9
  next := (source.actualExecution 9).root_next_exact

abbrev previousRoot := OutstandingSource.NativeService.Runtime.root source
abbrev previousFacade := OutstandingSource.NativeService.Runtime.facade source

inductive Projection where
  | method
  | dividend

def projectionLaw : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource source.input).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .method => current = (ProgrammeHistory.visitAt source.input 4).current → MethodCertificate
    | .dividend => current = (ProgrammeHistory.visitAt source.input 10).current → Certificate
  project := fun projection {_} _ _ => match projection with
    | .method => fun _canonical => methodCertificate
    | .dividend => fun _canonical => certificate

def root := previousRoot.withProjectionCoface projectionLaw

theorem original_root_is_preserved : root.toAuthoritativeRoot.toRoot =
    (ProgrammeLiving.livingRoot source.input).toAuthoritativeRoot.toRoot := rfl

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
  | method | dividend

def facade : SourceNativeLivingRuntimeFacade (ProgrammeSource.N source.input) where
  process := process
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous previous => previousFacade.componentAt previousFacade.seed previous
    | .method | .dividend => projectionLaw
  installationAt := by
    intro state face
    cases face with
    | previous previous =>
      exact (previousFacade.installationAt previousFacade.seed previous).trans
        (SourceNativeProjectionLaw.InstallationAt.inheritedCoface previousRoot.toAuthoritativeRoot.source projectionLaw)
    | method | dividend => exact SourceNativeProjectionLaw.InstallationAt.componentCoface previousRoot.toAuthoritativeRoot.source projectionLaw
  projectionAt := fun _ face => match face with
    | .previous previous => previousFacade.projectionAt previousFacade.seed previous
    | .method => .method
    | .dividend => .dividend

def activated (ordinal : Nat) : LivingRuntimeState process := facade.seed.advance ordinal

theorem actual_method_payload : projectionLaw.project .method
    (ProgrammeSource.emitted source.input (ProgrammeHistory.visitAt source.input 4).current) () rfl = methodCertificate := rfl

theorem actual_dividend_payload : projectionLaw.project .dividend
    (ProgrammeSource.emitted source.input (ProgrammeHistory.visitAt source.input 10).current) () rfl = certificate := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Cell.SharedAudit.Runtime
