import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Factory

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
open MotherFullCompiler MotherSourcePrograms
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : ConstructiveRoot.Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)

def entryTotalEquiv (n : MotherNetworkOrigin.Presentation N G) : EntryTotal N ≃ EntryTotal G :=
  Equiv.sigmaCongr n.support n.ledger

theorem recovered_entry_responsibility (value : EntryTotal G) :
    n.responsibility ((entryTotalEquiv n).symm value).2.1 = value.2.1 := by
  obtain ⟨old, rfl⟩ := (entryTotalEquiv n).surjective value
  exact congrArg (fun value : EntryTotal N => n.responsibility value.2.1) ((entryTotalEquiv n).symm_apply_apply old)

def worldLaw (old : SourceNativeLedgerRestructuringLaw original) : SourceNativeLedgerRestructuringLaw generated where
  vocabulary := old.vocabulary
  sourceEventAt := fun {current} event => old.sourceEventAt ((pointEquiv p).symm ⟨current, event⟩).2
  obligationAt := fun {current} event {support} entry =>
    old.obligationAt ((pointEquiv p).symm ⟨current, event⟩).2 ((entryTotalEquiv n).symm ⟨support, entry⟩).2
  responsibilityKey := fun value => n.responsibility (old.responsibilityKey value)
  anchorKey := fun value => n.anchor (old.anchorKey value)
  incidenceKey := fun value => n.incidence (old.incidenceKey value)
  lineageKey := fun value => n.lineage (old.lineageKey value)
  responsibility_commutes := fun {current} event {support} entry =>
    (congrArg n.responsibility (old.responsibility_commutes ((pointEquiv p).symm ⟨current, event⟩).2
      ((entryTotalEquiv n).symm ⟨support, entry⟩).2)).trans (recovered_entry_responsibility ⟨support, entry⟩)
  anchor_commutes := fun {current} event {support} entry =>
    (congrArg n.anchor (old.anchor_commutes ((pointEquiv p).symm ⟨current, event⟩).2
      ((entryTotalEquiv n).symm ⟨support, entry⟩).2)).trans
        ((n.anchor_commutes _).symm.trans
          (congrArg (fun value : EntryTotal G => G.anchorAt value.1) ((entryTotalEquiv n).apply_symm_apply ⟨support, entry⟩)))
  incidence_commutes := fun {current} event {support} entry =>
    (congrArg n.incidence (old.incidence_commutes ((pointEquiv p).symm ⟨current, event⟩).2
      ((entryTotalEquiv n).symm ⟨support, entry⟩).2)).trans
        ((n.incidence_commutes _).symm.trans
          (congrArg (fun value : EntryTotal G => G.incidenceAt value.1) ((entryTotalEquiv n).apply_symm_apply ⟨support, entry⟩)))
  lineage_commutes := fun {current} event {support} entry =>
    (congrArg n.lineage (old.lineage_commutes ((pointEquiv p).symm ⟨current, event⟩).2
      ((entryTotalEquiv n).symm ⟨support, entry⟩).2)).trans
        ((n.lineage_commutes _).symm.trans
          (congrArg (fun value : EntryTotal G => G.lineageAt value.1) ((entryTotalEquiv n).apply_symm_apply ⟨support, entry⟩)))
  obligationAt_injective := by
    intro current event support left right same
    have entryEq := old.obligationAt_injective ((pointEquiv p).symm ⟨current, event⟩).2 same
    have totalEq : (entryTotalEquiv n).symm ⟨support, left⟩ = (entryTotalEquiv n).symm ⟨support, right⟩ :=
      Sigma.ext rfl (heq_of_eq entryEq)
    exact eq_of_heq (Sigma.mk.inj ((entryTotalEquiv n).symm.injective totalEq)).2

theorem world_sourceEvent (old : SourceNativeLedgerRestructuringLaw original) (point : Point original) :
    (worldLaw p old).sourceEventAt (pointEquiv p point).2 = old.sourceEventAt point.2 :=
  congrArg (fun point : Point original => old.sourceEventAt point.2) ((pointEquiv p).symm_apply_apply point)

theorem world_obligation (old : SourceNativeLedgerRestructuringLaw original) (point : Point original)
    (support : N.Support) (entry : OpenResponsibilityAt N support) :
    (worldLaw p old).obligationAt (pointEquiv p point).2 (n.ledger support entry) = old.obligationAt point.2 entry := by
  change old.obligationAt ((pointEquiv p).symm (pointEquiv p point)).2
    ((entryTotalEquiv n).symm (entryTotalEquiv n ⟨support, entry⟩)).2 = _
  exact congrArg₂ (fun (point : Point original) (value : EntryTotal N) => old.obligationAt point.2 value.2)
    ((pointEquiv p).symm_apply_apply point) ((entryTotalEquiv n).symm_apply_apply ⟨support, entry⟩)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherObligationOrigin
