import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Claim
import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.BudgetDescent

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot CategoryTheory

noncomputable section

variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

/-- This is the universal consumer of the already generated carrier, not an
input to its producer. The cocone contains only a proposed readout. -/
theorem every_compatible_original_readout_factors_uniquely
    (consumer : (diagram root boundary).CoconeTypes) :
    ∃! read : Carrier root boundary → consumer.pt,
      ∀ cut original, read (includeRow root boundary cut original) = consumer.ι cut original := by
  refine ⟨(diagram root boundary).descColimitType consumer,fun _ _ => rfl,?_⟩
  intro read exact
  funext point
  obtain ⟨cut,original,rfl⟩ := every_completed_standing_has_an_original_actual_source root boundary point
  exact exact cut original

theorem every_completed_budget_is_attained_in_the_original_actual_past (point : Carrier root boundary) :
    ∃ cut original, includeRow root boundary cut original = point ∧
      original.progressBudget = budget root boundary point := by
  obtain ⟨cut,original,rfl⟩ := every_completed_standing_has_an_original_actual_source root boundary point
  obtain ⟨later,order,attained⟩ := the_minimum_budget_is_actually_attained root boundary cut original
  refine ⟨later,(diagram root boundary).map (homOfLE order) original,?_,attained⟩
  exact (diagram root boundary).ιColimitType_map (homOfLE order) original

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion
