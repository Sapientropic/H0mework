import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.RestructuringRestriction.Vocabulary

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
open MotherFullCompiler MotherSourcePrograms MotherRestructuringOrigin MotherObligationOrigin
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    (old : SourceNativeLedgerRestructuringLaw original)
    {sortsOut : Sorts} {familiesOut : Families sortsOut} (ops : Operations sortsOut familiesOut)
    (sorts : ∀ index, sortsOf old.vocabulary.base index ≃ sortsOut index)
    (families : FamilyMap sorts (familiesOf old.vocabulary) familiesOut)
    (across : OperationsAcross sorts families (operationsOf old.vocabulary) ops)
    (actual : SourceNativeLedgerRestructuringLaw generated)
    (actual_eq : actual = sourceLaw (worldLaw p old) ops sorts families across)

/-- Read all six functions from the actual law, with only its proven
vocabulary identity used to put those functions at the shared indices. -/
def actualFields : Fields generated (restructuring sortsOut familiesOut ops) :=
  Equiv.cast (congrArg (Fields generated)
    (congrArg (fun law : SourceNativeLedgerRestructuringLaw generated => law.vocabulary) actual_eq))
    (fieldsOf actual)

theorem actualFields_eq : actualFields p old ops sorts families across actual actual_eq =
    fieldsOf (sourceLaw (worldLaw p old) ops sorts families across) := by
  cases actual_eq
  rfl

def restrictFields : Fields original old.vocabulary
  | 0 => fun point => (sorts 0).symm
      (actualFields p old ops sorts families across actual actual_eq 0 (pointEquiv p point))
  | 1 => fun value => (obligationEquiv sorts families across).symm
      (actualFields p old ops sorts families across actual actual_eq 1
        (pointEquiv p value.1, entryTotalEquiv n value.2))
  | 2 => fun value => n.responsibility.symm
      (actualFields p old ops sorts families across actual actual_eq 2 (obligationEquiv sorts families across value))
  | 3 => fun value => n.anchor.symm
      (actualFields p old ops sorts families across actual actual_eq 3 (sorts 8 value))
  | 4 => fun value => n.incidence.symm
      (actualFields p old ops sorts families across actual actual_eq 4 (sorts 7 value))
  | 5 => fun value => n.lineage.symm
      (actualFields p old ops sorts families across actual actual_eq 5 (sorts 6 value))

theorem restrictFields_eq : restrictFields p old ops sorts families across actual actual_eq = fieldsOf old := by
  unfold restrictFields
  rw [actualFields_eq]
  funext index
  fin_cases index
  · funext point
    change (sorts 0).symm (sorts 0 ((worldLaw p old).sourceEventAt (pointEquiv p point).2)) = old.sourceEventAt point.2
    exact ((sorts 0).symm_apply_apply _).trans (world_sourceEvent p old point)
  · funext value
    change (obligationEquiv sorts families across).symm
      (obligationEquiv sorts families across
        ((worldLaw p old).obligationAt (pointEquiv p value.1).2 (n.ledger value.2.1 value.2.2))) =
          old.obligationAt value.1.2 value.2.2
    exact ((obligationEquiv sorts families across).symm_apply_apply _).trans
      (world_obligation p old value.1 value.2.1 value.2.2)
  · funext value
    change n.responsibility.symm (n.responsibility (old.responsibilityKey
      ((obligationEquiv sorts families across).symm (obligationEquiv sorts families across value)))) = old.responsibilityKey value
    exact (n.responsibility.symm_apply_apply _).trans
      (congrArg old.responsibilityKey ((obligationEquiv sorts families across).symm_apply_apply value))
  · funext value
    change n.anchor.symm (n.anchor (old.anchorKey ((sorts 8).symm (sorts 8 value)))) = old.anchorKey value
    exact (n.anchor.symm_apply_apply _).trans (congrArg old.anchorKey ((sorts 8).symm_apply_apply value))
  · funext value
    change n.incidence.symm (n.incidence (old.incidenceKey ((sorts 7).symm (sorts 7 value)))) = old.incidenceKey value
    exact (n.incidence.symm_apply_apply _).trans (congrArg old.incidenceKey ((sorts 7).symm_apply_apply value))
  · funext value
    change n.lineage.symm (n.lineage (old.lineageKey ((sorts 6).symm (sorts 6 value)))) = old.lineageKey value
    exact (n.lineage.symm_apply_apply _).trans (congrArg old.lineageKey ((sorts 6).symm_apply_apply value))

private theorem fieldLaws_cast {source : SourceNativeSource N V} {first last : RestructuringVocabulary.{0}}
    (same : first = last) (fields : Fields source last) (laws : FieldLaws fields) :
    FieldLaws (Equiv.cast (congrArg (Fields source) same.symm) fields) := by
  cases same
  exact laws

private theorem lawOf_cast {source : SourceNativeSource N V} {first last : RestructuringVocabulary.{0}}
    (same : first = last) (fields : Fields source last) (laws : FieldLaws fields) :
    lawOf (Equiv.cast (congrArg (Fields source) same.symm) fields) (fieldLaws_cast same fields laws) =
      lawOf fields laws := by
  cases same
  rfl

private theorem lawOf_recovers {source : SourceNativeSource N V}
    (law : SourceNativeLedgerRestructuringLaw source) (fields : Fields source law.vocabulary)
    (same : fields = fieldsOf law) (laws : FieldLaws fields) : lawOf fields laws = law := by
  cases same
  rfl

theorem restrictFields_laws : FieldLaws (restrictFields p old ops sorts families across actual actual_eq) := by
  rw [restrictFields_eq]
  exact fieldsOf_laws old

/-- Rebuild the complete original law using the actually restored vocabulary
and all six inverse-read value functions. -/
def restrictLaw : SourceNativeLedgerRestructuringLaw original :=
  lawOf (Equiv.cast (congrArg (Fields original) (restrictVocabulary_eq old.vocabulary ops sorts families across).symm)
    (restrictFields p old ops sorts families across actual actual_eq))
    (fieldLaws_cast (restrictVocabulary_eq old.vocabulary ops sorts families across)
      (restrictFields p old ops sorts families across actual actual_eq)
      (restrictFields_laws p old ops sorts families across actual actual_eq))

theorem restrictLaw_eq : restrictLaw p old ops sorts families across actual actual_eq = old :=
  (lawOf_cast (restrictVocabulary_eq old.vocabulary ops sorts families across)
    (restrictFields p old ops sorts families across actual actual_eq)
    (restrictFields_laws p old ops sorts families across actual actual_eq)).trans
      (lawOf_recovers old (restrictFields p old ops sorts families across actual actual_eq)
        (restrictFields_eq p old ops sorts families across actual actual_eq)
        (restrictFields_laws p old ops sorts families across actual actual_eq))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherRestructuringRestriction
