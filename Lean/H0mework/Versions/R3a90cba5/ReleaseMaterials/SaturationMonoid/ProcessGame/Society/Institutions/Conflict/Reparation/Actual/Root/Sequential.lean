import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.Root.Compile
import H0mework.Versions.R3a90cba5.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Transport.Sequential

set_option autoImplicit false

open private sameSupportLedger sameSupportLedger_heq sameSupportLedger_rows from
  H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Public.Continuation.Admitted.Ledger

namespace SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.First

open Capitalism.Universal.Abolition.Accounting.Root
open Capitalism.Universal.Abolition.Root.Registered.Macro
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion

noncomputable section

variable {N : WorldRelationNetwork} (first : First N) (current : Resident N)
  (same : first.before = current.support)

local notation "nextRoot" => First.rooted first (first.inherit current)

abbrev translatedEntry : OpenResponsibilityAt N first.before :=
  (sameSupportLedger same).forward current.entry

private def occurrence : ConstructivePresentation
    (current.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current.visit.current)
    ((nextRoot).toAuthoritativeRoot.toRoot.actual.OccurrenceAt first.initial.current) where
  forward := fun _ => (nextRoot).emitted first.initial.current
  backward := fun _ => current.root.emitted current.visit.current
  backward_forward := fun actual => (current.unique actual).symm
  forward_backward := fun actual => (Compiler.occurrence_eq_emitted first.flow actual).symm

set_option maxHeartbeats 700000 in
def sequentialTarget (event : ExactTemporalCausalRootEventAt
    current.root.toAuthoritativeRoot.toLedgerRoot current.visit) :
    SourceNativeSequentialActualActionTargetAt current.root current.visit event current.entry current.authority := by
  rw [event.eq_generated]
  let ledger := sameSupportLedger same
  exact {
    TargetN := N
    translation := Capitalism.Universal.Root.Financial.Installation.Ingress.identityTranslation N
    TargetV := Compiler.V first.flow
    targetRoot := nextRoot
    targetTheory := TheoryState.rootSemantic N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id, fun _ => rfl⟩
    occurrencePresentation := occurrence first current
    occurrence_commutes := rfl
    initialSupport_heq := heq_of_eq same
    initialOpenLedger := ledger
    initialOpenLedger_heq := sameSupportLedger_heq same
    initialLedger_responsibility_commutes := fun row => ((sameSupportLedger_rows same).1 row).symm
    initialLedger_claim_commutes := fun row => ((sameSupportLedger_rows same).2.1 row).symm
    initialLedger_budget_conservative := fun row => ((sameSupportLedger_rows same).2.2.1 row).le
    initialLedgerNoFresh := fun row => ⟨⟨ledger.backward row, ⟨(sameSupportLedger_rows same).2.2.2 row⟩⟩⟩
    translatedSourceEntryRow := Compiler.generatedRow first.flow first.initial
      (translatedEntry first current same)
    firstSuccessor := first.successor
    canonical_targetNextVisit_eq :=
      Ingress.next_is_the_same_generated_successor (nextRoot) first.initial first.successor
    Answer := Unit
    answer := ()
    Receipt := fun _ => PUnit
    receipt := PUnit.unit }

def sequentialProgram : SourceNativeSequentialActualActionProgramAt
    current.root current.visit current.entry current.authority where
  targetAt := sequentialTarget first current same

def sequential := (sequentialProgram first current same).generate current.event

def prepare : Draft N := first.draft (first.inherit current) (translatedEntry first current same)

theorem sequential_reaches_its_first_write :
    (⟨N, (sequential first current same).target.targetAnswerAndNext.nextCurrent⟩ : AnyAuthoritativeRootCurrent) =
      (prepare first current same).enter.erase :=
  congrArg (fun next => (⟨N, next⟩ : AnyAuthoritativeRootCurrent))
    (sequential first current same).target.targetAnswerAndNext_next_eq

end

end SaturationMonoid.ProcessGame.Society.Institutions.Conflict.Reparation.Actual.First
