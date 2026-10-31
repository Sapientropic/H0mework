import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.FiniteData

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

def splitChild (child : {old // old ∈ covered.receipt.children}) : (After root boundary cut).Entry :=
  (covered.no_phantom_child child.val child.property).val

def splitImage (child : {old // old ∈ covered.receipt.children}) : (vocabulary root boundary).Obligation :=
  imageOld root boundary (splitChild root boundary cut covered child) child.val

def splitChildren : List (vocabulary root boundary).Obligation :=
  covered.receipt.children.attach.map (splitImage root boundary cut covered)

theorem splitImage_is_the_actual_target_obligation (child : {old // old ∈ covered.receipt.children}) :
    (law root boundary).obligationAt (emitted root boundary (.inl cut))
      (oldRow root boundary false (splitChild root boundary cut covered child)) =
      splitImage root boundary cut covered child :=
  congrArg (imageOld root boundary (splitChild root boundary cut covered child))
    (covered.no_phantom_child child.val child.property).property.1

def splitMember (child : (vocabulary root boundary).Obligation)
    (member : child ∈ splitChildren root boundary cut covered) :
    {old : {old // old ∈ covered.receipt.children} // splitImage root boundary cut covered old = child} :=
  recoverAttached covered.receipt.children (splitImage root boundary cut covered)
    (fun new => originalAdmission root boundary new.content) (fun _ => rfl) child member

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
