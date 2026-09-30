import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.Root
import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.LivingInquiryAlignment.U7Coverage

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLivingInquiryAlignment
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot RootInquiryCompletion
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeLivingRootClosure N V}
    (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot) (Query : Type)

abbrev HeaderSection (header : MotherInquiryU7Header.Header N) :=
  (query : Query) → MotherNativeClause.Clause root visit header.1 header.2 query

/-- Install the actual material-recovered U7/calculus values, transporting
the complete clauses only through the proved literal header equality. -/
def assembleWithHeader {original : MotherInquiryU7Header.Header N}
    (actual : MotherInquiryU7Header.Header N) (same : actual = original)
    (clauses : HeaderSection visit Query original) : RootInquiryStateAt N V :=
  MotherNativeClause.assemble (Equiv.cast (congrArg (HeaderSection visit Query) same.symm) clauses)

theorem assembleWithHeader_eq {original : MotherInquiryU7Header.Header N}
    (actual : MotherInquiryU7Header.Header N) (same : actual = original)
    (clauses : HeaderSection visit Query original) :
    assembleWithHeader visit Query actual same clauses = MotherNativeClause.assemble clauses := by
  cases same
  rfl

theorem assembleWithHeader_U7 {original : MotherInquiryU7Header.Header N}
    (actual : MotherInquiryU7Header.Header N) (same : actual = original)
    (clauses : HeaderSection visit Query original) :
    (assembleWithHeader visit Query actual same clauses).U7 = actual.1 := rfl

theorem assembleWithHeader_calculus {original : MotherInquiryU7Header.Header N}
    (actual : MotherInquiryU7Header.Header N) (same : actual = original)
    (clauses : HeaderSection visit Query original) :
    (assembleWithHeader visit Query actual same clauses).calculus = actual.2 := rfl

theorem original_header_state_recovers (state : RootInquiryStateAt N V)
    (actual : MotherInquiryU7Header.Header N) (same : actual = ⟨state.U7, state.calculus⟩)
    (clauses : HeaderSection state.visit state.Query ⟨state.U7, state.calculus⟩)
    (clausesSame : clauses = MotherNativeClause.ofState state) :
    assembleWithHeader state.visit state.Query actual same clauses = state :=
  (assembleWithHeader_eq state.visit state.Query actual same clauses).trans
    ((congrArg MotherNativeClause.assemble clausesSame).trans (MotherNativeClause.assemble_ofState state))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLivingInquiryAlignment
