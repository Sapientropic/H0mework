import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.SplitMembers

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

def splitCoverage : SourceNativeSplitCoverageAt (law root boundary) (emitted root boundary (.inl cut))
    (liftLedger root boundary (originalEvolution root boundary cut))
    (oldRow root boundary false left) (oldRow root boundary false right)
    (congrArg (oldRow root boundary false) originEq) :=
  SourceNativeSplitCoverageAt.ofReceipt (splitReceipt root boundary cut covered)
    (congrArg Sum.inl covered.sourceEvent_eq)
    (split_actual_target_is_listed root boundary cut covered left rfl)
    (split_actual_target_is_listed root boundary cut covered right originEq.symm)
    (by
      intro target same
      have oldSame := congrArg (readOld root boundary) same
      have listed := split_actual_target_is_listed root boundary cut covered
        (readOld root boundary target) oldSame
      rw [oldRow_readOld] at listed
      exact listed)
    (by
      intro target same
      have exactBudget := congrArg OpenResponsibilityAt.progressBudget (oldRow_readOld root boundary target)
      exact exactBudget ▸ covered.childProgressBudget_strictlyDebited (readOld root boundary target)
        (congrArg (readOld root boundary) same))
    (fun child member =>
      let prior := splitMember root boundary cut covered child member
      ⟨oldRow root boundary false (splitChild root boundary cut covered prior.val),
        (splitImage_is_the_actual_target_obligation root boundary cut covered prior.val).trans prior.property,
        congrArg (oldRow root boundary false)
          (covered.no_phantom_child prior.val.val prior.val.property).property.2⟩)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
