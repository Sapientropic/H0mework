import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.World

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

/-- Completion changes the row representation, not the original law epoch,
expression language, theorem witnesses or obstruction realizations. -/
def retainedTheory : TheoryState (W root boundary) where
  inventory := {
    Version := root.source.base.lawSurface.inventory.Version
    version := root.source.base.lawSurface.inventory.version
    Law := root.source.base.lawSurface.inventory.Law
    RealizationAt := fun {_} obstruction => root.source.base.lawSurface.inventory.RealizationAt obstruction
    RealizationWithoutAt := fun law {_} obstruction => root.source.base.lawSurface.inventory.RealizationWithoutAt law obstruction }
  ExpressionAt := fun support => root.source.base.lawSurface.ExpressionAt support.1
  denotes := fun expression => root.source.base.lawSurface.denotes expression
  TheoremAt := fun expression => root.source.base.lawSurface.TheoremAt expression
  theoremPresentation := fun expression => root.source.base.lawSurface.theoremPresentation expression

theorem the_completion_keeps_the_original_law_version :
    (retainedTheory root boundary).inventory.version = root.source.base.lawSurface.inventory.version := rfl

theorem every_original_expression_retains_its_literal_claim (support : N.Support) (phase : Bool)
    (expression : root.source.base.lawSurface.ExpressionAt support) :
    (retainedTheory root boundary).denotes (support := (support,phase)) expression =
      root.source.base.lawSurface.denotes expression := rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing
