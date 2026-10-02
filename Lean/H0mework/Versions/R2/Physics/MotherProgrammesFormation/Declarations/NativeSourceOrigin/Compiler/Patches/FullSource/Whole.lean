import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Patches.FullSource.Frame

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherJointWrite
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

private theorem cast_destination (G : WorldRelationNetwork.{0}) {s s' t : G.Support}
    (same : s = s') (whole : LedgerWriteEvolutionAt G ⟨s⟩ ⟨t⟩) (entry : OpenResponsibilityAt G s) :
    ((Equiv.cast (congrArg (fun support => LedgerWriteEvolutionAt G ⟨support⟩ ⟨t⟩) same)) whole).destination
        ((Equiv.cast (congrArg (OpenResponsibilityAt G) same)) entry) =
      ⟨(whole.destination entry).1, castRowSource G same entry (whole.destination entry).1 (whole.destination entry).2⟩ := by
  cases same
  rfl

private theorem cast_origin (G : WorldRelationNetwork.{0}) {s s' t : G.Support}
    (same : s = s') (whole : LedgerWriteEvolutionAt G ⟨s⟩ ⟨t⟩) (entry : OpenResponsibilityAt G t) :
    ((Equiv.cast (congrArg (fun support => LedgerWriteEvolutionAt G ⟨support⟩ ⟨t⟩) same)) whole).origin entry =
      ⟨(Equiv.cast (congrArg (OpenResponsibilityAt G) same)) (whole.origin entry).1,
        castRowSource G same (whole.origin entry).1 entry (whole.origin entry).2⟩ := by
  cases same
  rfl

theorem whole_ext {N : WorldRelationNetwork.{0}} {s t : CompleteLiveLedgerAt N}
    {left right : LedgerWriteEvolutionAt N s t}
    (destination : ∀ a, left.destination a = right.destination a)
    (origin : ∀ b, left.origin b = right.origin b) : left = right := by
  have hd := funext destination
  have ho := funext origin
  cases left; cases right; cases hd; cases ho; rfl

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : Transitions original} {formed : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p old) formed)

def wholeEquiv (point : Point original) (target : N.Support) :
    LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨target⟩ ≃
      LedgerWriteEvolutionAt G ⟨(pointEquiv p point).2.1⟩ ⟨n.support target⟩ :=
  (n.wholeLedgerEquiv point.2.1 target).trans (Equiv.cast
    (congrArg (fun support => LedgerWriteEvolutionAt G ⟨support⟩ ⟨n.support target⟩)
      (p.support_eq point.1 point.2).symm))

theorem whole_destination (point : Point original) (target : N.Support)
    (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨target⟩) (entry : OpenResponsibilityAt N point.2.1) :
    (wholeEquiv p point target whole).destination (sourceEntryEquiv p point entry) =
      ⟨n.ledger target (whole.destination entry).1,
        rowEvolutionEquiv p ⟨point.1, point.2, target, entry, (whole.destination entry).1⟩ (whole.destination entry).2⟩ := by
  exact (cast_destination G (p.support_eq point.1 point.2).symm
    (n.wholeLedgerEquiv point.2.1 target whole) (n.ledger point.2.1 entry)).trans
    (congrArg (fun value : Σ out : OpenResponsibilityAt G (n.support target), LedgerEntryEvolutionAt G (n.ledger point.2.1 entry) out => (⟨value.1, castRowSource G (p.support_eq point.1 point.2).symm
      (n.ledger point.2.1 entry) value.1 value.2⟩ :
        Σ out : OpenResponsibilityAt G (n.support target), LedgerEntryEvolutionAt G (sourceEntryEquiv p point entry) out))
      (n.whole_destination whole entry))

theorem whole_origin (point : Point original) (target : N.Support)
    (whole : LedgerWriteEvolutionAt N ⟨point.2.1⟩ ⟨target⟩) (entry : OpenResponsibilityAt N target) :
    (wholeEquiv p point target whole).origin (n.ledger target entry) =
      ⟨sourceEntryEquiv p point (whole.origin entry).1,
        rowEvolutionEquiv p ⟨point.1, point.2, target, (whole.origin entry).1, entry⟩ (whole.origin entry).2⟩ := by
  exact (cast_origin G (p.support_eq point.1 point.2).symm
    (n.wholeLedgerEquiv point.2.1 target whole) (n.ledger target entry)).trans
    (congrArg (fun value : Σ out : OpenResponsibilityAt G (n.support point.2.1), LedgerEntryEvolutionAt G out (n.ledger target entry) => (⟨(Equiv.cast (congrArg (OpenResponsibilityAt G) (p.support_eq point.1 point.2).symm)) value.1,
      castRowSource G (p.support_eq point.1 point.2).symm value.1 (n.ledger target entry) value.2⟩ :
        Σ out : OpenResponsibilityAt G (pointEquiv p point).2.1, LedgerEntryEvolutionAt G out (n.ledger target entry)))
      (n.whole_origin whole entry))

theorem remainderOutput_whole (context : RemainderContext original) (value : RemainderOutput old context) :
    (remainderOutputEquiv p q context value).1 = wholeEquiv p context.1 context.2 value.1 := by
  apply whole_ext
  · intro entry
    obtain ⟨entry, rfl⟩ := (sourceEntryEquiv p context.1).surjective entry
    refine Eq.trans ?_ (whole_destination p context.1 context.2 value.1 entry).symm
    exact congrArg
      (fun item : Destination formed (remainderContextEquiv p context) (sourceEntryEquiv p context.1 entry) =>
        (⟨item.1, item.2.1⟩ : Σ out : OpenResponsibilityAt G (n.support context.2),
          LedgerEntryEvolutionAt G (sourceEntryEquiv p context.1 entry) out))
      (Equiv.piCongr_apply_apply (sourceEntryEquiv p context.1) (destinationEquiv p q context)
        ((certifiedBodyEquiv old context value).1) entry)
  · intro entry
    obtain ⟨entry, rfl⟩ := (n.ledger context.2).surjective entry
    refine Eq.trans ?_ (whole_origin p context.1 context.2 value.1 entry).symm
    exact congrArg
      (fun item : Origin formed (remainderContextEquiv p context) (n.ledger context.2 entry) =>
        (⟨item.1, item.2.1⟩ : Σ out : OpenResponsibilityAt G (pointEquiv p context.1).2.1,
          LedgerEntryEvolutionAt G out (n.ledger context.2 entry)))
      (Equiv.piCongr_apply_apply (n.ledger context.2) (originEquiv p q context)
        ((certifiedBodyEquiv old context value).2) entry)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFullPatches
