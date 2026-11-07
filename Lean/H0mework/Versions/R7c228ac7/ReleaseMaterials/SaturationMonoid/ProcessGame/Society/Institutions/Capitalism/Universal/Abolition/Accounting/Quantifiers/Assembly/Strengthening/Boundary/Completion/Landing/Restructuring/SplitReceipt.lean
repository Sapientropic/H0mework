import H0mework.Versions.R7c228ac7.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring.SplitData

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

def splitReceipt : SplitReceipt (vocabulary root boundary)
    (imageOld root boundary ((originalEvolution root boundary cut).origin left).1
      ((oldLaw root).obligationAt (oldOccurrence root boundary cut)
        ((originalEvolution root boundary cut).origin left).1)) where
  sourceEvent := .inl covered.receipt.sourceEvent
  sourceOwnership := {
    anchor_eq := congrArg (oldAnchor root boundary) covered.receipt.sourceOwnership.anchor_eq
    incidence_eq := congrArg Sum.inl covered.receipt.sourceOwnership.incidence_eq }
  children := splitChildren root boundary cut covered
  children_nonempty := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [splitChildren,List.length_map,List.length_attach,List.length_nil] at lengths
    exact covered.receipt.children_nonempty (List.length_eq_zero_iff.mp lengths)
  coverage := ⟨covered.receipt.children.map AdmittedObligation.content,PLift.up (by
      change ((covered.receipt.children.attach.map (splitImage root boundary cut covered)).map
        AdmittedObligation.content).map (originalContent root boundary) = _
      calc
        _ = (covered.receipt.children.attach.map (fun child =>
            (splitImage root boundary cut covered child).content)).map (originalContent root boundary) :=
          congrArg (List.map (originalContent root boundary)) List.map_map
        _ = covered.receipt.children.attach.map (fun child => some child.val.content) := List.map_map
        _ = covered.receipt.children.map (fun child => some child.content) :=
          List.attach_map_val (l := covered.receipt.children)
            (f := fun child : (Original root).Obligation => some child.content)
        _ = (covered.receipt.children.map AdmittedObligation.content).map some := List.map_map.symm),covered.receipt.coverage⟩
  descendant := fun child member =>
    let prior := splitMember root boundary cut covered child member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation =>
      (vocabulary root boundary).DescendantAt (.inl covered.receipt.sourceEvent)
        (.inl ((oldLaw root).obligationAt (oldOccurrence root boundary cut)
          ((originalEvolution root boundary cut).origin left).1).sourceIncidence)
        (.old ⟨oldSupport root boundary _,oldRow root boundary false
          ((originalEvolution root boundary cut).origin left).1⟩
          ((oldLaw root).obligationAt (oldOccurrence root boundary cut)
            ((originalEvolution root boundary cut).origin left).1))
        current.sourceIncidence current.content) prior.property)
      (covered.receipt.descendant prior.val.val prior.val.property)
  anchorTransport := fun child member =>
    let prior := splitMember root boundary cut covered child member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation => SourceAnchorTransport
      (imageOld root boundary ((originalEvolution root boundary cut).origin left).1
        ((oldLaw root).obligationAt (oldOccurrence root boundary cut)
          ((originalEvolution root boundary cut).origin left).1)).sourceAnchor current.sourceAnchor) prior.property)
      (oldAnchorTransport root boundary (covered.receipt.anchorTransport prior.val.val prior.val.property))
  lineage := fun child member =>
    let prior := splitMember root boundary cut covered child member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation => SameDebtLineage
      (imageOld root boundary ((originalEvolution root boundary cut).origin left).1
        ((oldLaw root).obligationAt (oldOccurrence root boundary cut)
          ((originalEvolution root boundary cut).origin left).1)) current) prior.property)
      (congrArg Sum.inl (covered.receipt.lineage prior.val.val prior.val.property))
  localDischarge := fun child member =>
    let prior := splitMember root boundary cut covered child member
    Eq.mp (congrArg (fun current : (vocabulary root boundary).Obligation =>
      (vocabulary root boundary).LocalDischargePreservedAt (.inl covered.receipt.sourceEvent)
        (imageOld root boundary ((originalEvolution root boundary cut).origin left).1
          ((oldLaw root).obligationAt (oldOccurrence root boundary cut)
            ((originalEvolution root boundary cut).origin left).1)).content current.content) prior.property)
      (covered.receipt.localDischarge prior.val.val prior.val.property)

end
end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Abolition.Accounting.Quantifiers.Assembly.Strengthening.Boundary.Completion.Landing.Restructuring
