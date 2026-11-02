import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Openness

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Runtime

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open Institutions.Capitalism.Universal
open Source.Program Instances.OpenReplication Root

/-- The first-window saving and its actual use are kept in separate fields. -/
structure Certificate (n : Nat) (shared : Bool) where
  amount : ℚ
  generated_amount : amount = dividend n
  positive : 0 < amount
  services : ∀ branch, ServiceAdequate (law n) (currentAt n branch 1) (task n) (execution n branch 1).submitted
  authorized : ∀ branch, ∀ item ∈ (execution n branch 1).interpreted.items,
    (law n).Valid item.before item.request
  credits : ∀ branch party good,
    (law n).totalCredit (execution n branch 1).interpreted.items party good =
      if good then (n : ℚ) + 1 else 0
  costs : ∀ branch party good, taskDebit n branch party good =
    if party then (if good then (n : ℚ) + 1 else 0)
    else if good then (n : ℚ) + 1 else if branch then 3 else (n : ℚ) + 4
  own_budget : maintenanceBudget (currentAt n shared 2) = if shared then n + 1 else 0
  own_word : (execution n shared 2).submitted = List.replicate (if shared then n + 1 else 0) maintain
  own_cuts : ∀ item ∈ (execution n shared 2).interpreted.items,
    (law n).Valid item.before item.request ∧
    1 ≤ item.before.stock false false ∧
    1 ≤ ((law n).step item.before item.request).stock false false ∧ item.request = maintain
  payment : extraDebit n true false false - extraDebit n false false false = amount
  no_double_count : taskDebit n true false false + extraDebit n true false false =
    taskDebit n false false false + extraDebit n false false false
  final_inventory : (currentAt n true 3).stock = (currentAt n false 3).stock
  final_claims : ∀ branch instrument debtor holder, (currentAt n branch 3).claims instrument debtor holder = 0
  horizon : (currentAt n true 3).clock = 3 ∧ (currentAt n false 3).clock = 3
  written : (writtenReceipt n shared 1).val = .original (currentAt n shared 2) (execution n shared 2).submitted
  row : ProgrammeLedger.transferReceiptOf (input n shared) (taskWrite n shared 1).2 =
    some (writtenReceipt n shared 1)
  original_row : HEq (taskWrite n shared 1)
    ((ProgrammeLedger.evolution (input n shared)
      (ProgrammeHistory.visitAt (input n shared) 2).current).destination
        (ProgrammeSource.sourceEntry (input n shared)
          (ProgrammeHistory.visitAt (input n shared) 2).current
          (.instruction ⟨0, by change 0 < 1; decide⟩)))
  own_next : (execution n shared 2).after = currentAt n shared 3

def certificate (n : Nat) (shared : Bool) : Certificate n shared where
  amount := dividend n
  generated_amount := rfl
  positive := (exact_strict_dividend_and_actual_payment n).2.1
  services := same_task_paid_in_the_same_window n
  authorized := first_programme_is_authorized n
  credits := complete_task_credits n
  costs := complete_task_debits n
  own_budget := reinvestment_budget n shared
  own_word := reinvestment_word n shared
  own_cuts := every_reinvestment_cut_is_paid_and_keeps_the_reserve n shared
  payment := (exact_strict_dividend_and_actual_payment n).2.2.1
  no_double_count := (saved_fuel_equals_spent_dividend n).2
  final_inventory := (exact_strict_dividend_and_actual_payment n).2.2.2.1
  final_claims := (exact_strict_dividend_and_actual_payment n).2.2.2.2.1
  horizon := (exact_strict_dividend_and_actual_payment n).2.2.2.2.2
  written := written_report n shared 1
  row := actual_row_receipt n shared 1
  original_row := actual_row_is_original_destination n shared 1
  own_next := actual_next n shared 2

structure AccessCertificate (n : Nat) (shared : Bool) (later : Nat) where
  response : Access.Response n (currentAt n shared (3 + later))
  selected : response = Access.respond n (currentAt n shared (3 + later))
  word : (execution n shared (3 + later)).submitted = response.word
  authorized : ∀ item ∈ (execution n shared (3 + later)).interpreted.items,
    (law n).Valid item.before item.request
  public_service : ServiceAdequate (law n) (currentAt n true (3 + later)) (Access.taskAt n later)
    (execution n true (3 + later)).submitted
  no_capital : ¬ Nonempty (Source.ProgrammeControl.Kernel.CapitalRelationKernel (law n)
    (currentAt n true (3 + later)) (execution n true (3 + later)).submitted)
  fuel : (law n).totalDebit (execution n shared (3 + later)).interpreted.items false false = 0
  produced : (law n).totalCredit (execution n shared (3 + later)).interpreted.items true true =
    if shared then (n : ℚ) + 1 else 0
  used : (law n).totalDebit (execution n shared (3 + later)).interpreted.items true true =
    if shared then (n : ℚ) + 1 else 0
  written : (writtenReceipt n shared (2 + later)).val =
    .original (currentAt n shared (3 + later)) (execution n shared (3 + later)).submitted
  row : ProgrammeLedger.transferReceiptOf (input n shared) (taskWrite n shared (2 + later)).2 =
    some (writtenReceipt n shared (2 + later))
  own_next : (execution n shared (3 + later)).after = currentAt n shared (3 + (later + 1))

def accessCertificate (n : Nat) (shared : Bool) (later : Nat) : AccessCertificate n shared later where
  response := Access.respond n (currentAt n shared (3 + later))
  selected := rfl
  word := by rw [Access.every_later_word, Access.every_later_current, Access.selected_word]
  authorized := Access.every_later_programme_is_authorized n shared later
  public_service := Access.every_later_public_service_is_actually_paid n later
  no_capital := Access.every_later_public_execution_has_no_complete_capital_relation n later
  fuel := (Access.every_later_service_has_zero_fuel_cost n shared later).1
  produced := (Access.every_later_service_has_zero_fuel_cost n shared later).2.1
  used := (Access.every_later_service_has_zero_fuel_cost n shared later).2.2
  written := by
    exact (written_report n shared (2 + later)).trans
      (congrArg (fun visit : Nat => (ProgrammeSource.ProgrammeReport.original
        (currentAt n shared visit) (execution n shared visit).submitted :
          ProgrammeSource.ProgrammeReport Bool Bool (Option Bool) Bool Unit))
        (show 2 + later + 1 = 3 + later by omega))
  row := actual_row_receipt n shared (2 + later)
  own_next := by simpa only [show 3 + later + 1 = 3 + (later + 1) by omega] using actual_next n shared (3 + later)

inductive Projection where
  | dividend
  | access

def projectionLaw (n : Nat) (shared : Bool) : SourceNativeProjectionLaw
    (ProgrammeLiving.authoritySource (input n shared)).restructuringSource.toLedgerSource where
  Projection := Projection
  ActiveAt := fun _ {_} _ => Unit
  InactiveAt := fun _ {_} _ => Empty
  classify := fun _ {_} _ => .inl ()
  PayloadAt := fun projection {current} _ _ => match projection with
    | .dividend => current = (ProgrammeHistory.visitAt (input n shared) 2).current → Certificate n shared
    | .access => (later : Nat) →
        current = (ProgrammeHistory.visitAt (input n shared) (3 + later)).current → AccessCertificate n shared later
  project := fun projection {_} _ _ => match projection with
    | .dividend => fun _canonical => certificate n shared
    | .access => fun later _canonical => accessCertificate n shared later

def root (n : Nat) (shared : Bool) :=
  (ProgrammeLiving.livingRoot (input n shared)).withProjectionCoface (projectionLaw n shared)

theorem original_root_is_preserved (n : Nat) (shared : Bool) :
    (root n shared).toAuthoritativeRoot.toRoot =
      (ProgrammeLiving.livingRoot (input n shared)).toAuthoritativeRoot.toRoot := rfl

def stateAt (n : Nat) (shared : Bool) (ordinal : Nat) :
    SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input n shared)) :=
  ⟨ProgrammeSource.V (input n shared), root n shared, ProgrammeHistory.temporalVisit (input n shared) ordinal⟩

def process (n : Nat) (shared : Bool) : SourceNativeLivingRootProcess (ProgrammeSource.N (input n shared)) where
  State := Nat
  stateAt := stateAt n shared
  stateAt_injective := by
    intro first second same
    have labels := congrArg
      (fun state : SourceNativeLivingRootCurrentAt (ProgrammeSource.N (input n shared)) =>
        (⟨state.V.Current, state.visit.current⟩ : Sigma fun Carrier : Type => Carrier)) same
    have currents : (ProgrammeHistory.visitAt (input n shared) first).current =
        (ProgrammeHistory.visitAt (input n shared) second).current := eq_of_heq (Sigma.mk.inj labels).2
    exact ProgrammeHistory.visit_current_injective (input n shared) currents
  initial := 0
  successorAt := fun ordinal => ⟨ordinal + 1, rfl, HEq.rfl⟩

inductive Face where
  | previous (face : ProgrammeLiving.Projection)
  | dividend
  | access

def facade (n : Nat) (shared : Bool) : SourceNativeLivingRuntimeFacade (ProgrammeSource.N (input n shared)) where
  process := process n shared
  FaceAt := fun _ => Face
  componentAt := fun _ face => match face with
    | .previous _ => ProgrammeLiving.projectionLaw (input n shared)
    | .dividend | .access => projectionLaw n shared
  installationAt := by
    intro state face
    cases face with
    | previous _ =>
        exact SourceNativeProjectionLaw.InstallationAt.inheritedCoface
          (ProgrammeLiving.livingRoot (input n shared)).toAuthoritativeRoot.source (projectionLaw n shared)
    | dividend | access =>
        exact SourceNativeProjectionLaw.InstallationAt.componentCoface
          (ProgrammeLiving.livingRoot (input n shared)).toAuthoritativeRoot.source (projectionLaw n shared)
  projectionAt := fun _ face => match face with
    | .previous previous => previous
    | .dividend => .dividend
    | .access => .access

def activated (n : Nat) (shared : Bool) (ordinal : Nat) : LivingRuntimeState (process n shared) :=
  (facade n shared).seed.advance ordinal

theorem actual_payload (n : Nat) (shared : Bool) :
    (projectionLaw n shared).project .dividend (ProgrammeSource.emitted (input n shared)
      (ProgrammeHistory.visitAt (input n shared) 2).current) () rfl = certificate n shared := rfl

theorem actual_access_payload (n : Nat) (shared : Bool) (later : Nat) :
    (projectionLaw n shared).project .access (ProgrammeSource.emitted (input n shared)
      (ProgrammeHistory.visitAt (input n shared) (3 + later)).current) () later rfl =
        accessCertificate n shared later := rfl

end SaturationMonoid.ProcessGame.Society.PublicFunction.Productivity.Dividend.Runtime
