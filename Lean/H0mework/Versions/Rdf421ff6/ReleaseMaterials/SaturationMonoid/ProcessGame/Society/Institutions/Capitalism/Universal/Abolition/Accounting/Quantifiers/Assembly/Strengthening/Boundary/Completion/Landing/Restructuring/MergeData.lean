import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.FiniteData

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

def mergeParent (parent : {old // old ∈ covered.receipt.parents}) : (Before root boundary cut).Entry :=
  (covered.no_phantom_parent parent.val parent.property).val

def mergeImage (parent : {old // old ∈ covered.receipt.parents}) : (vocabulary root boundary).Obligation :=
  imageOld root boundary (mergeParent root boundary cut covered parent) parent.val

def mergeParents : List (vocabulary root boundary).Obligation :=
  covered.receipt.parents.attach.map (mergeImage root boundary cut covered)

def mergeTarget : (vocabulary root boundary).Obligation :=
  imageOld root boundary ((originalEvolution root boundary cut).destination left).1 covered.receipt.target

theorem mergeImage_is_the_actual_source_obligation (parent : {old // old ∈ covered.receipt.parents}) :
    (law root boundary).obligationAt (emitted root boundary (.inl cut))
      (oldRow root boundary false (mergeParent root boundary cut covered parent)) =
      mergeImage root boundary cut covered parent :=
  congrArg (imageOld root boundary (mergeParent root boundary cut covered parent))
    (covered.no_phantom_parent parent.val parent.property).property.1

def mergeMember (parent : (vocabulary root boundary).Obligation)
    (member : parent ∈ mergeParents root boundary cut covered) :
    {old : {old // old ∈ covered.receipt.parents} // mergeImage root boundary cut covered old = parent} :=
  recoverAttached covered.receipt.parents (mergeImage root boundary cut covered)
    (fun new => originalAdmission root boundary new.content) (fun _ => rfl) parent member

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
