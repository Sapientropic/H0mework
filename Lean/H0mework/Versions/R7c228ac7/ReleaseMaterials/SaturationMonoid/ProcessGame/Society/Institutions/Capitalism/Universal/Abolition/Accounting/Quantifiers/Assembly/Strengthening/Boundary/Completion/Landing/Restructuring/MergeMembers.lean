import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.MergeReceipt

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (cut : Nat) {left right : (Before root boundary cut).Entry}
  {destinationEq : ((originalEvolution root boundary cut).destination left).1 =
    ((originalEvolution root boundary cut).destination right).1}
  (covered : SourceNativeMergeCoverageAt (oldLaw root) (oldOccurrence root boundary cut)
    (originalEvolution root boundary cut) left right destinationEq)

theorem merge_actual_source_is_listed (source : (Before root boundary cut).Entry)
    (same : ((originalEvolution root boundary cut).destination source).1 =
      ((originalEvolution root boundary cut).destination left).1) :
    (law root boundary).obligationAt (emitted root boundary (.inl cut))
      (oldRow root boundary false source) ∈ (mergeReceipt root boundary cut covered).parents := by
  let parent : {old // old ∈ covered.receipt.parents} :=
    ⟨(oldLaw root).obligationAt (oldOccurrence root boundary cut) source,covered.covers_source source same⟩
  have sameSource : mergeParent root boundary cut covered parent = source :=
    (oldLaw root).obligationAt_injective (oldOccurrence root boundary cut)
      (covered.no_phantom_parent parent.val parent.property).property.1
  exact List.mem_map.mpr ⟨parent,List.mem_attach _ _,
    (mergeImage_is_the_actual_source_obligation root boundary cut covered parent).symm.trans
      (congrArg (fun row => (law root boundary).obligationAt (emitted root boundary (.inl cut))
        (oldRow root boundary false row)) sameSource)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
