import H0mework.Realization.Operations.Tree.Fold.Inverse
import H0mework.Versions.R2.Realization.Operations.Tree.Fold.Consumer

/-! Independent recovery consumes the original query's retained source
programme and recognizes its whole tree before any scalar fold readout. -/

set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Inverse.Mother
open SourceOperationEffects SourceOperationExecution
variable {Root Carrier : Type u}
variable (atOccurrence : Root → List Carrier → Carrier)
open RootInquiryCompletion
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (old : RootInquiryStateAt N V)
variable (source : {current : V.Current} → (o : Installation.Occurrence old current) → Installation.TreeReadAt (Root:=Root) old o)
abbrev retainedExpression := (Installation.I.resultFace old (Installation.reader atOccurrence old source)).rootRead.1.expression
theorem recovered_tree : readTree (retainedExpression atOccurrence old source) =
    some (Installation.treeAt old source (old.root.emitted old.visit.current)) := read_program _ _
theorem query_tree (incidence : old.Query) : readTree (Installation.I.query old (Installation.reader atOccurrence old source) incidence).raw.expression =
    some (Installation.treeAt old source (old.root.emitted old.visit.current)) := read_program _ _

end SourceOperationNative.Tree.Fold.Inverse.Mother
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
