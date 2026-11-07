import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.Added

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)

def vocabulary : RestructuringVocabulary where
  base := base root boundary
  DescendantAt := fun source parentInc parent childInc child =>
    match source,parentInc,parent,childInc,child with
    | .inl source,.inl parentInc,.old _ parent,.inl childInc,.old _ child =>
        (Original root).DescendantAt source parentInc parent.content childInc child.content
    | _,_,_,_,_ => PEmpty
  SplitCoverageAt := fun source parent children => match source,parent with
    | .inl source,.old _ parent => Sigma fun original : List (Original root).base.Content =>
        PLift (children.map (originalContent root boundary) = original.map some) ×
          (Original root).SplitCoverageAt source parent.content original
    | _,_ => PEmpty
  MergeCoverageAt := fun source parents target => match source,target with
    | .inl source,.old _ target => Sigma fun original : List (Original root).base.Content =>
        PLift (parents.map (originalContent root boundary) = original.map some) ×
          (Original root).MergeCoverageAt source original target.content
    | _,_ => PEmpty
  LocalDischargePreservedAt := fun source parent child => match source,parent,child with
    | .inl source,.old _ parent,.old _ child =>
        (Original root).LocalDischargePreservedAt source parent.content child.content
    | _,_,_ => PEmpty
  RenameAt := fun source parent child => match source,parent,child with
    | .inl source,.old _ parent,.old _ child => (Original root).RenameAt source parent.content child.content
    | _,_,_ => PEmpty

def obligationAt (current : Current) {support : (W root boundary).Support}
    (row : OpenResponsibilityAt (W root boundary) support) : (vocabulary root boundary).Obligation := by
  rcases row with ⟨key,opened⟩
  cases key with
  | inl old =>
      exact oldObligation root boundary ⟨support,⟨.inl old,opened⟩⟩
        ((oldLaw root).obligationAt (rawOccurrence root boundary current) ⟨old,opened⟩)
  | inr point => exact addedObligation root boundary ⟨support,⟨.inr point,opened⟩⟩

theorem obligationAt_keeps_the_full_world_entry (current : Current) {support : (W root boundary).Support}
    (row : OpenResponsibilityAt (W root boundary) support) :
    entry root boundary (obligationAt root boundary current row).content = ⟨support,row⟩ := by
  rcases row with ⟨key,opened⟩
  cases key <;> rfl

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
