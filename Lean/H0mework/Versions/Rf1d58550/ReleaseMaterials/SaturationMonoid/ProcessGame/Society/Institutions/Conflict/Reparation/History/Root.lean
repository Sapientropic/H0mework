import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History.Opening
import H0mework.Versions.Rf1d58550.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Payment.Root

set_option autoImplicit false

open private sameSupportLedger sameSupportLedger_heq sameSupportLedger_rows from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Ledger

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History

open Capitalism.Universal.Source.Program
open Capitalism.Universal.Root
open Capitalism.Universal.Abolition
open Capitalism.Universal.Abolition.Root.Registered
open Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {Party Good Port Technology Instrument Community : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  [DecidableEq Community]
  {source : Root.Cut Party Good Port Technology Instrument}
  {attack : RawEvent Party Good Port Technology Instrument}
  {community : Party → Community} {key : Key Party Good}
  (claim : ClaimAt source attack community key)

local notation "Script" => List (Option (Capitalism.Universal.Abolition.Root.Registered.Compile.RawInput
  Party Good Port Technology Instrument))

def NoReceipt (script : Script) : Prop :=
  ∀ item ∈ Quantities.Execution.inventory (Birth.attacked claim) script,
    receiptCredit source.native.input.law item key = 0

variable (script : List (Option (Capitalism.Universal.Abolition.Root.Registered.Compile.RawInput
    Party Good Port Technology Instrument))) (safe : NoFinancialBirths (Birth.attacked claim) script)

abbrev livingRoot := Accounting.Root.Compiler.livingRoot (flow claim script safe)
abbrev initial := Accounting.Root.Compiler.initialVisit (flow claim script safe)
abbrev first := Accounting.Root.Compiler.successor (flow claim script safe) (initial claim script safe).current

private def occurrencePresentation : ConstructivePresentation
    ((filed claim).targetRoot.toAuthoritativeRoot.toRoot.actual.OccurrenceAt (filedVisit claim).current)
    ((livingRoot claim script safe).toAuthoritativeRoot.toRoot.actual.OccurrenceAt (initial claim script safe).current) where
  forward := fun _ => (livingRoot claim script safe).emitted (initial claim script safe).current
  backward := fun _ => (filed claim).targetRoot.emitted (filedVisit claim).current
  backward_forward := fun event => (Accounting.Root.Compiler.occurrence_eq_emitted (Birth.flow claim) event).symm
  forward_backward := fun event => (Accounting.Root.Compiler.occurrence_eq_emitted (flow claim script safe) event).symm

variable (nonempty : 0 < script.length)
  (paid : Quantities.Settled (Birth.attacked claim) script)

set_option maxHeartbeats 1000000 in
def action (event : ExactTemporalCausalRootEventAt
    (filed claim).targetRoot.toAuthoritativeRoot.toLedgerRoot (filedVisit claim)) :
    SourceNativeSequentialActualActionTargetAt (filed claim).targetRoot (filedVisit claim) event
      (filedOwner claim) (filedAuthority claim) := by
  rw [event.eq_generated]
  let same := initial_is_the_actual_filed_support claim script safe nonempty
  let ledger := sameSupportLedger same
  exact {
    TargetN := Birth.N claim
    translation := Financial.Installation.Ingress.identityTranslation (Birth.N claim)
    TargetV := Accounting.Root.Compiler.V (flow claim script safe)
    targetRoot := livingRoot claim script safe
    targetTheory := TheoryState.rootSemantic (Birth.N claim)
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation claim script safe
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq same
    initialOpenLedger := ledger
    initialOpenLedger_heq := sameSupportLedger_heq same
    initialLedger_responsibility_commutes := fun row => ((sameSupportLedger_rows same).1 row).symm
    initialLedger_claim_commutes := fun row => ((sameSupportLedger_rows same).2.1 row).symm
    initialLedger_budget_conservative := fun row => ((sameSupportLedger_rows same).2.2.1 row).le
    initialLedgerNoFresh := fun row => ⟨⟨ledger.backward row, ⟨(sameSupportLedger_rows same).2.2.2 row⟩⟩⟩
    translatedSourceEntryRow := Accounting.Root.Compiler.generatedRow (flow claim script safe)
      (initial claim script safe) (ledger.forward (filedOwner claim))
    firstSuccessor := first claim script safe
    canonical_targetNextVisit_eq := Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
      (livingRoot claim script safe) (initial claim script safe) (first claim script safe)
    Answer := ℚ
    answer := recordedDue source attack script community key
    Receipt := fun amount => ULift.{3,0} (PLift (amount = recordedDue source attack script community key ∧
      Quantities.Settled (Birth.attacked claim) script))
    receipt := ⟨⟨rfl, paid⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt (filed claim).targetRoot (filedVisit claim)
    (filedOwner claim) (filedAuthority claim) where
  targetAt := action claim script safe nonempty paid

def generated := (program claim script safe nonempty paid).generate
  ((filed claim).targetRoot.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (filedVisit claim))

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.History
