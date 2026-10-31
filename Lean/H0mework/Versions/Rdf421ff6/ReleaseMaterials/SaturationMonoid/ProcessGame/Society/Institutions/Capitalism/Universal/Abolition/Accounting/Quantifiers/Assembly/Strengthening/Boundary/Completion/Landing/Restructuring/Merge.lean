import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.MergeMembers

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

def mergeCoverage : SourceNativeMergeCoverageAt (law root boundary) (emitted root boundary (.inl cut))
    (liftLedger root boundary (originalEvolution root boundary cut))
    (oldRow root boundary false left) (oldRow root boundary false right)
    (congrArg (oldRow root boundary false) destinationEq) :=
  SourceNativeMergeCoverageAt.ofReceipt (mergeReceipt root boundary cut covered)
    (congrArg Sum.inl covered.sourceEvent_eq)
    (congrArg (imageOld root boundary ((originalEvolution root boundary cut).destination left).1)
      covered.target_eq)
    (merge_actual_source_is_listed root boundary cut covered left rfl)
    (merge_actual_source_is_listed root boundary cut covered right destinationEq.symm)
    (by
      intro source same
      have oldSame := congrArg (readOld root boundary) same
      have listed := merge_actual_source_is_listed root boundary cut covered
        (readOld root boundary source) oldSame
      rw [oldRow_readOld] at listed
      exact listed)
    (fun parent member =>
      let prior := mergeMember root boundary cut covered parent member
      ⟨oldRow root boundary false (mergeParent root boundary cut covered prior.val),
        (mergeImage_is_the_actual_source_obligation root boundary cut covered prior.val).trans prior.property,
        congrArg (oldRow root boundary false)
          (covered.no_phantom_parent prior.val.val prior.val.property).property.2⟩)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
