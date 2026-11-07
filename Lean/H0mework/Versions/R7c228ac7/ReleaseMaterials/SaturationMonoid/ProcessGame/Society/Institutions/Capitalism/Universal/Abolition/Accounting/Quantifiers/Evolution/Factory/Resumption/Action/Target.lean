import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action.Entry
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Root.Registered.Macro.Ingress.Next

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
open SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root
open Abolition.Root.Registered Abolition.Root.Registered.Macro

noncomputable section

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Port] [DecidableEq Instrument]
  {input : ProgrammeSource.Input Party Good Port Technology Instrument}
  {depth count prefixLimit renewalLimit : Nat}
  {oldPast : List (Compile.RawInput Party Good Port Technology Instrument)}
  {start : Physical.Cursor Party Good Port Technology Instrument}
  (frame : Abolition.Root.Registered.Macro.Public.NativeFrame input depth count prefixLimit renewalLimit oldPast start)
  (visit : SourceNativeTemporalVisitAt frame.root.toAuthoritativeRoot.toLedgerRoot)
  (actual : Public.Inquiry.ActualAt frame visit.current)
  (authority : SourceNativeLivingTemporalCausalEntryAuthorityAt frame.root visit (frame.entry visit.current))

def preparedContext := Factory.Public.Source.native (opened frame visit actual authority)

variable (reader : Macro.Raw.Reader input depth count)

local notation "C" => preparedContext frame visit actual authority
local notation "full" => fullFrame frame visit C reader
local notation "priorCode" => Factory.Public.code (Factory.Public.Source.native (sourceContext frame visit actual authority))
local notation "newCode" => Suffix.code frame visit.current

def suffixRoot : SourceNativeLivingRootClosure frame.N (Sparse.Compiler.V newCode) := (full).root

def occurrencePresentation : ConstructivePresentation
    ((C).root.toAuthoritativeRoot.toRoot.actual.OccurrenceAt (C).visit.current)
    ((suffixRoot frame visit actual authority reader).toAuthoritativeRoot.toRoot.actual.OccurrenceAt
      (suffixRoot frame visit actual authority reader).toAuthoritativeRoot.toRoot.source.initial) where
  forward := fun occurrence => Sparse.Compiler.represented newCode none (Sparse.Compiler.originalOccurrence priorCode occurrence)
  backward := fun occurrence => Sparse.Compiler.represented priorCode (C).visit.current (Sparse.Compiler.originalOccurrence newCode occurrence)
  backward_forward := fun occurrence =>
    (congrArg (Sparse.Compiler.represented priorCode (C).visit.current)
      (Sparse.Compiler.original_represented newCode none (Sparse.Compiler.originalOccurrence priorCode occurrence))).trans
      (Sparse.Compiler.represented_original priorCode occurrence)
  forward_backward := fun occurrence =>
    (congrArg (Sparse.Compiler.represented newCode none)
      (Sparse.Compiler.original_represented priorCode (C).visit.current (Sparse.Compiler.originalOccurrence newCode occurrence))).trans
      (Sparse.Compiler.represented_original newCode occurrence)

def targetAt (event : ExactTemporalCausalRootEventAt (C).root.toAuthoritativeRoot.toLedgerRoot (C).visit) :
    SourceNativeSequentialActualActionTargetAt (C).root (C).visit event (C).row (C).authority := by
  exact {
    TargetN := frame.N
    translation := Financial.Installation.Ingress.identityTranslation frame.N
    TargetV := Sparse.Compiler.V newCode
    targetRoot := suffixRoot frame visit actual authority reader
    targetTheory := TheoryState.rootSemantic frame.N
    lawSurface_heq := HEq.rfl
    targetTheory_rootSemantic := ⟨id,fun _ => rfl⟩
    occurrencePresentation := occurrencePresentation frame visit actual authority reader
    occurrence_commutes := by rw [event.eq_generated]; rfl
    initialSupport_heq := HEq.rfl
    initialOpenLedger := (Financial.Installation.Ingress.identityTranslation frame.N).oldOpenLedger (Context.support C)
    initialOpenLedger_heq := HEq.rfl
    initialLedger_responsibility_commutes := fun _ => rfl
    initialLedger_claim_commutes := fun _ => rfl
    initialLedger_budget_conservative := fun _ => Nat.le_refl _
    initialLedgerNoFresh := fun entry => ⟨⟨entry,⟨rfl⟩⟩⟩
    translatedSourceEntryRow := Sparse.Compiler.generatedRow newCode (Sparse.Compiler.initialVisit newCode) (C).row
    firstSuccessor := Sparse.Compiler.successor newCode none
    canonical_targetNextVisit_eq :=
      Abolition.Root.Registered.Macro.Ingress.next_is_the_same_generated_successor (full).root
        (initialVisit frame visit C reader) (Sparse.Compiler.successor newCode none)
    Answer := Factory.Public.Source.Answer (Party := Party) (Good := Good) (Port := Port)
      (Technology := Technology) (Instrument := Instrument)
    answer := Factory.Public.Source.readAnswer (opened frame visit actual authority)
    Receipt := fun answer => ULift.{3,0} (PLift (answer = Factory.Public.Source.answer (opened frame visit actual authority))) ×
      ULift.{3,0} (PLift ((full).cursor (Sparse.Compiler.successor newCode none).targetCurrent = some actual.actual))
    receipt := ⟨⟨⟨rfl⟩⟩,⟨⟨reentry_is_at_the_same_live_cursor frame visit actual C reader⟩⟩⟩ }

def program : SourceNativeSequentialActualActionProgramAt (C).root (C).visit (C).row (C).authority where
  targetAt := targetAt frame visit actual authority reader

def generated := (program frame visit actual authority reader).generate
  ((C).root.toAuthoritativeRoot.toLedgerRoot.exactTemporalCausalEventAt (C).visit)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Evolution.Factory.Resumption.Action
