import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.SplitReceipt

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section
variable {N : WorldRelationNetwork} {V : ConstructiveRoot.Vocabulary}
  (root : SourceNativeLivingRootClosure N V)
  (boundary : SourceNativeCofinalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
  (cut : Nat) {left right : (After root boundary cut).Entry}
  {originEq : ((originalEvolution root boundary cut).origin left).1 =
    ((originalEvolution root boundary cut).origin right).1}
  (covered : SourceNativeSplitCoverageAt (oldLaw root) (oldOccurrence root boundary cut)
    (originalEvolution root boundary cut) left right originEq)

theorem split_actual_target_is_listed (target : (After root boundary cut).Entry)
    (same : ((originalEvolution root boundary cut).origin target).1 =
      ((originalEvolution root boundary cut).origin left).1) :
    (law root boundary).obligationAt (emitted root boundary (.inl cut))
      (oldRow root boundary false target) ∈ (splitReceipt root boundary cut covered).children := by
  let child : {old // old ∈ covered.receipt.children} :=
    ⟨(oldLaw root).obligationAt (oldOccurrence root boundary cut) target,covered.covers_target target same⟩
  have sameTarget : splitChild root boundary cut covered child = target :=
    (oldLaw root).obligationAt_injective (oldOccurrence root boundary cut)
      (covered.no_phantom_child child.val child.property).property.1
  exact List.mem_map.mpr ⟨child,List.mem_attach _ _,
    (splitImage_is_the_actual_target_obligation root boundary cut covered child).symm.trans
      (congrArg (fun row => (law root boundary).obligationAt (emitted root boundary (.inl cut))
        (oldRow root boundary false row)) sameTarget)⟩

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
