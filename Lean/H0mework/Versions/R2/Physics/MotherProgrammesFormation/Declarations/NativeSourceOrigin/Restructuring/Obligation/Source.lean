import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Obligation

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot MotherRestructuringOrigin
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}} {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source)
    {generated : Sorts} {families : Families generated} (ops : Operations generated families)
    (sortMap : ∀ i, sortsOf law.vocabulary.base i ≃ generated i)
    (familyMap : FamilyMap sortMap (familiesOf law.vocabulary) families)
    (p : OperationsAcross sortMap familyMap (operationsOf law.vocabulary) ops)

/-- Entire obligations, including original admission origin/authority and
current discharge jurisdiction, travel through the formed vocabulary. -/
def sourceLaw : SourceNativeLedgerRestructuringLaw source where
  vocabulary := restructuring generated families ops
  sourceEventAt := fun {current} event => sortMap 0 (law.sourceEventAt event)
  obligationAt := fun {current} event {support} entry => obligationEquiv sortMap familyMap p (law.obligationAt event entry)
  responsibilityKey := fun value => law.responsibilityKey ((obligationEquiv sortMap familyMap p).symm value)
  anchorKey := fun value => law.anchorKey ((sortMap 8).symm value)
  incidenceKey := fun value => law.incidenceKey ((sortMap 7).symm value)
  lineageKey := fun value => law.lineageKey ((sortMap 6).symm value)
  responsibility_commutes := fun {current} event {support} entry =>
    (congrArg law.responsibilityKey ((obligationEquiv sortMap familyMap p).symm_apply_apply (law.obligationAt event entry))).trans
      (law.responsibility_commutes event entry)
  anchor_commutes := by
    intro current event support entry
    have same := congrArg (fun anchor => anchor.identity) (obligation_anchor sortMap familyMap p (law.obligationAt event entry))
    exact (congrArg (fun value => law.anchorKey ((sortMap 8).symm value)) same).trans
      ((congrArg law.anchorKey ((sortMap 8).symm_apply_apply (law.obligationAt event entry).sourceAnchor.identity)).trans
        (law.anchor_commutes event entry))
  incidence_commutes := fun {current} event {support} entry =>
    (congrArg (fun value => law.incidenceKey ((sortMap 7).symm value))
      (obligation_incidence sortMap familyMap p (law.obligationAt event entry))).trans
        ((congrArg law.incidenceKey ((sortMap 7).symm_apply_apply _)).trans (law.incidence_commutes event entry))
  lineage_commutes := fun {current} event {support} entry =>
    (congrArg (fun value => law.lineageKey ((sortMap 6).symm value))
      (obligation_lineage sortMap familyMap p (law.obligationAt event entry))).trans
        ((congrArg law.lineageKey ((sortMap 6).symm_apply_apply _)).trans (law.lineage_commutes event entry))
  obligationAt_injective := fun {current} event {support} _ _ same => law.obligationAt_injective event ((obligationEquiv sortMap familyMap p).injective same)

theorem source_obligation_recovers {current : V.Current} (event : source.toRootSource.actual.OccurrenceAt current)
    {support : N.Support} (entry : OpenResponsibilityAt N support) :
    (obligationEquiv sortMap familyMap p).symm ((sourceLaw law ops sortMap familyMap p).obligationAt event entry) =
      law.obligationAt event entry :=
  (obligationEquiv sortMap familyMap p).symm_apply_apply _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
