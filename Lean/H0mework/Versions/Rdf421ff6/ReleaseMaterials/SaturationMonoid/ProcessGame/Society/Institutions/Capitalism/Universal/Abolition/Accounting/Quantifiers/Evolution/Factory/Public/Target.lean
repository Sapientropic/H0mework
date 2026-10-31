import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Root
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public.Source
import H0mework.Versions.R2.Foundation.Source.SequentialAction
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.Financial.Installation.Ingress

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root

noncomputable section

variable {Party Good Port Technology Instrument : Type} {N : WorldRelationNetwork}
  (current : Context (Party := Party) (Good := Good) (Port := Port)
    (Technology := Technology) (Instrument := Instrument) N)

def occurrencePresentation : ConstructivePresentation
    (current.root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt current.visit.current)
    ((targetRoot current).toAuthoritativeRoot.toRoot.actual.OccurrenceAt false) where
  forward := Sparse.Compiler.represented (code current) false
  backward := Sparse.Compiler.originalOccurrence (code current)
  backward_forward := Sparse.Compiler.original_represented (code current) false
  forward_backward := Sparse.Compiler.represented_original (code current)

def targetAt (event : ExactTemporalCausalRootEventAt current.root.toAuthoritativeRoot.toLedgerRoot current.visit) :
    SourceNativeSequentialActualActionTargetAt current.root current.visit event current.row current.authority := by
  rw [event.eq_generated]
  exact {
    TargetN := N
    translation := Financial.Installation.Ingress.identityTranslation N
    TargetV := V current
    targetRoot := targetRoot current
    targetTheory := TheoryState.rootSemantic N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation current
    occurrence_commutes := rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := (Financial.Installation.Ingress.identityTranslation N).oldOpenLedger (Context.support current)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun entry => ⟨⟨entry,⟨rfl⟩⟩⟩
    translatedSourceEntryRow := Sparse.Compiler.generatedRow (code current) (Sparse.Compiler.initialVisit (code current)) current.row
    firstSuccessor := Sparse.Compiler.successor (code current) false
    canonical_targetNextVisit_eq :=
      Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor (targetRoot current)
        (Sparse.Compiler.initialVisit (code current)) (Sparse.Compiler.successor (code current) false)
    Answer := Source.Answer (Party := Party) (Good := Good) (Port := Port) (Technology := Technology) (Instrument := Instrument)
    answer := Source.answer current
    Receipt := fun answer => ULift.{3,0} (PLift (answer = effectiveAt current true)) ×
      ULift.{3,0} (PLift ((code current).support true = Context.support current))
    receipt := ⟨⟨⟨rfl⟩⟩,⟨⟨rfl⟩⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt current.root current.visit current.row current.authority where
  targetAt := targetAt current

def generated := (program current).generate
  (current.root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt current.visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Public
