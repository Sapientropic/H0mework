import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.MergeData

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

def mergeReceipt : MergeReceipt (vocabulary root boundary) where
  sourceEvent := .inl covered.receipt.sourceEvent
  parents := mergeParents root boundary cut covered
  parents_nonempty := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [mergeParents,List.length_map,List.length_attach,List.length_nil] at lengths
    exact covered.receipt.parents_nonempty (List.length_eq_zero_iff.mp lengths)
  target := mergeTarget root boundary cut covered
  sourceOwnership := {
    anchor_eq := congrArg (oldAnchor root boundary) covered.receipt.sourceOwnership.anchor_eq
    incidence_eq := congrArg Sum.inl covered.receipt.sourceOwnership.incidence_eq }
  coverage := ⟨covered.receipt.parents.map AdmittedObligation.content,PLift.up (by
      change ((covered.receipt.parents.attach.map (mergeImage root boundary cut covered)).map
        AdmittedObligation.content).map (originalContent root boundary) = _
      calc
        _ = (covered.receipt.parents.attach.map (fun parent =>
            (mergeImage root boundary cut covered parent).content)).map (originalContent root boundary) :=
          congrArg (List.map (originalContent root boundary)) List.map_map
        _ = covered.receipt.parents.attach.map (fun parent => some parent.val.content) := List.map_map
        _ = covered.receipt.parents.map (fun parent => some parent.content) :=
          List.attach_map_val (l := covered.receipt.parents)
            (f := fun parent : (Original root).Obligation => some parent.content)
        _ = (covered.receipt.parents.map AdmittedObligation.content).map some := List.map_map.symm),covered.receipt.coverage⟩
  ancestor := fun parent member =>
    let prior := mergeMember root boundary cut covered parent member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation =>
      (vocabulary root boundary).DescendantAt (.inl covered.receipt.sourceEvent)
        current.sourceIncidence current.content
        (mergeTarget root boundary cut covered).sourceIncidence
        (mergeTarget root boundary cut covered).content) prior.property)
      (covered.receipt.ancestor prior.val.val prior.val.property)
  anchorTransport := fun parent member =>
    let prior := mergeMember root boundary cut covered parent member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation => SourceAnchorTransport
      current.sourceAnchor (mergeTarget root boundary cut covered).sourceAnchor) prior.property)
      (oldAnchorTransport root boundary (covered.receipt.anchorTransport prior.val.val prior.val.property))
  lineage := fun parent member =>
    let prior := mergeMember root boundary cut covered parent member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation => SameDebtLineage
      current (mergeTarget root boundary cut covered)) prior.property)
      (congrArg Sum.inl (covered.receipt.lineage prior.val.val prior.val.property))
  localDischarge := fun parent member =>
    let prior := mergeMember root boundary cut covered parent member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation =>
      (vocabulary root boundary).LocalDischargePreservedAt (.inl covered.receipt.sourceEvent)
        current.content (mergeTarget root boundary cut covered).content) prior.property)
      (covered.receipt.localDischarge prior.val.val prior.val.property)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
