import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.TargetRoot
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse.Compiler.Key
import H0mework.Versions.R2.Foundation.Source.SequentialAction

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion DebtActivationWorld
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Source.Program Innovation

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  {original : Trials.Mechanism Party Good Port Technology Instrument}
  {past : List (RawEvent Party Good Port Technology Instrument)} {nature : original.Nature}
  {response : Control.HistoryResponse (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument)} {oldN : WorldRelationNetwork}
  (claim : Responsibility.Family.Claim original past nature response)
  (current : Current (oldN := oldN) claim) (word : RawEvent Party Good Port Technology Instrument)

local notation "N" => ExtendedNetwork oldN (Responsibility.Family.activationLaw claim)
local notation "C" => code claim current word
local notation "newRoot" => targetRoot claim current word

def occurrencePresentation : ConstructivePresentation
    (current.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current.visit.current)
    ((newRoot).toAuthoritativeRoot.toRoot.actual.OccurrenceAt false) where
  forward := Compiler.represented C false
  backward := Compiler.originalOccurrence C
  backward_forward := Compiler.original_represented C false
  forward_backward := Compiler.represented_original C

def targetAt (event : ExactTemporalCausalRootEventAt current.root.toAuthoritativeRoot.toLedgerRoot current.visit) :
    SourceNativeSequentialActualActionTargetAt current.root current.visit event current.row current.authority := by
  rw [event.eq_generated]
  exact {
    TargetN := N
    translation := Financial.Installation.Ingress.identityTranslation N
    TargetV := targetV claim current word
    targetRoot := newRoot
    targetTheory := TheoryState.rootSemantic N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation claim current word
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := (Financial.Installation.Ingress.identityTranslation N).oldOpenLedger (Current.support claim current)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun entry => ⟨⟨entry,⟨rfl⟩⟩⟩
    translatedSourceEntryRow := Compiler.generatedRow C (Compiler.initialVisit C) current.row
    firstSuccessor := Compiler.successor C false
    canonical_targetNextVisit_eq :=
      Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor
        (newRoot) (Compiler.initialVisit C) (Compiler.successor C false)
    Answer := Responsibility.Family.State claim
    answer := updated claim current word
    Receipt := fun answer => ULift.{3,0} (PLift
      (answer = updated claim current word ∧
        (∀ key,answer.remaining key ≤ (Current.state claim current).remaining key) ∧
        answer.raw.claims = (Current.state claim current).raw.claims)) ×
      ULift.{3,0} (Responsibility.Family.MaterialVerdict claim (Current.state claim current) current.actualLaw word) ×
      ULift.{3,0} (Responsibility.Family.NeedDisposition current.actualLaw (Current.state claim current).raw
        (Responsibility.Family.State.attempt claim (Current.state claim current) current.actualLaw word).actualWord current.members)
    receipt := ⟨⟨⟨rfl,Responsibility.Family.State.actual_advance_never_refills_any_original_cell _ _ _ _,
        Responsibility.Family.State.actual_advance_retains_every_original_financial_claim _ _ _ _⟩⟩,
      ⟨Responsibility.Family.adjudicate claim (Current.state claim current) current.actualLaw word⟩,
      ⟨Responsibility.Family.inspectActualNeeds claim (Current.state claim current) current.actualLaw word current.members⟩⟩ }

def rawProgram : SourceNativeSequentialActualActionProgramAt current.root current.visit current.row current.authority where
  targetAt := targetAt claim current word

def rawGenerated := (rawProgram claim current word).generate
  (current.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt current.visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Sparse
