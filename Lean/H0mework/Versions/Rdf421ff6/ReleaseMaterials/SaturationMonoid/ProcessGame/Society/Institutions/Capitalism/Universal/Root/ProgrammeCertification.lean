import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeRestructuring

set_option autoImplicit false

namespace SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeCertification

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open ProgrammeWorld ProgrammeSource ProgrammeLedger ProgrammeRestructuring

variable {Party Good Port Technology Instrument : Type}
  [DecidableEq Party] [DecidableEq Good] [DecidableEq Instrument]
  (input : Input Party Good Port Technology Instrument)

theorem obligation_mem_firstChildren
    (entry : OpenResponsibilityAt (N input) (supportAt input (next input .bootstrap))) :
    obligation input entry ∈ firstChildren input ↔ entry.1 ≠ .obstruction := by
  constructor
  · intro member
    exact (mem_childRows input entry.1).mp (child_content_mem input _ member)
  · intro child
    exact List.mem_map.mpr ⟨entry.1, (mem_childRows input entry.1).mpr child,
      congrArg (obligation input) (targetEntry_complete input .bootstrap entry)⟩

def firstSplit
    (left right : OpenResponsibilityAt (N input) (supportAt input (next input .bootstrap)))
    (sameOrigin : ((evolution input .bootstrap).origin left).1 =
      ((evolution input .bootstrap).origin right).1)
    (leftChild : left.1 ≠ .obstruction) :
    SourceNativeSplitCoverageAt (restructuringLaw input) (emitted input .bootstrap)
      (evolution input .bootstrap) left right sameOrigin := by
  have parentLeft := (first_origin_parent_iff input left).mpr leftChild
  have parentRight := sameOrigin.symm.trans parentLeft
  have rightChild := (first_origin_parent_iff input right).mp parentRight
  refine SourceNativeSplitCoverageAt.ofReceipt
    (firstReceipt input ((evolution input .bootstrap).origin left).1
      (congrArg Sigma.fst parentLeft)) rfl
    ((obligation_mem_firstChildren input left).mpr leftChild)
    ((obligation_mem_firstChildren input right).mpr rightChild) ?_ ?_ ?_
  · intro target same
    exact (obligation_mem_firstChildren input target).mpr
      ((first_origin_parent_iff input target).mp (same.trans parentLeft))
  · intro target same
    rw [parentLeft]
    exact first_child_debit input target
      ((first_origin_parent_iff input target).mp (same.trans parentLeft))
  · intro child member
    refine ⟨targetEntry input .bootstrap child.content, ?_, ?_⟩
    · obtain ⟨row, _member, rfl⟩ := List.mem_map.mp member
      rfl
    · have contentMember := child_content_mem input child member
      have notObstruction := (mem_childRows input child.content).mp contentMember
      exact ((first_origin_parent_iff input
        (targetEntry input .bootstrap child.content)).mpr notObstruction).trans parentLeft.symm

theorem first_obstruction_origin_unique
    (left right : OpenResponsibilityAt (N input) (supportAt input (next input .bootstrap)))
    (leftObstruction : left.1 = .obstruction)
    (sameOrigin : ((evolution input .bootstrap).origin left).1 =
      ((evolution input .bootstrap).origin right).1) : left = right := by
  have originSame := (origin_exact input .bootstrap left).symm.trans
    (sameOrigin.trans (origin_exact input .bootstrap right))
  rcases left with ⟨left, leftOpen⟩
  rcases right with ⟨right, rightOpen⟩
  cases leftObstruction
  have rows := congrArg Sigma.fst originSame
  cases right with
  | inherited => change Row.obstruction = Row.inherited at rows; cases rows
  | instruction _ => change Row.obstruction = Row.inherited at rows; cases rows
  | obstruction => cases leftOpen; cases rightOpen; rfl

def firstCertification : ExactLedgerRestructuringCertificationAt
    (restructuringLaw input) (emitted input .bootstrap) (evolution input .bootstrap) where
  split := by
    intro left right sameOrigin
    cases kind : left.1 with
    | inherited =>
        exact .split (firstSplit input left right sameOrigin (by
          rw [kind]
          intro impossible
          cases impossible))
    | instruction _ =>
        exact .split (firstSplit input left right sameOrigin (by
          rw [kind]
          intro impossible
          cases impossible))
    | obstruction =>
        exact .identity (first_obstruction_origin_unique input left right kind sameOrigin)
  merge := fun _ _ sameDestination =>
    .identity (destination_injective input .bootstrap sameDestination)

def restructuringCompiler : SourceNativeRestructuringLedgerCompiler (ProgrammeSource.source input) where
  ledgerCompiler := ledgerCompiler input
  restructuringLaw := restructuringLaw input
  certifyRestructuring := by
    intro current occurrence
    cases occurrence_eq_emitted input occurrence
    cases current with
    | bootstrap => exact firstCertification input
    | running current past =>
        exact ExactLedgerRestructuringCertificationAt.ofInjective
          (running_origin_injective input current past)
          (destination_injective input (.running current past))

def restructuringSource : SourceNativeRestructuringLedgerSource (N input) (V input) where
  source := ProgrammeSource.source input
  compiler := restructuringCompiler input

theorem source_retains_actual_programme :
    (restructuringSource input).toLedgerSource = ledgerSource input := rfl

end SaturationMonoid.ProcessGame.Society.Institutions.Capitalism.Universal.Root.ProgrammeCertification
