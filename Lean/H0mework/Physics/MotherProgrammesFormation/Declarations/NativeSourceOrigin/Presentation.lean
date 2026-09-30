import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Account

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
open MotherNetworkFactory
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

structure Presentation {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    (n : MotherNetworkOrigin.Presentation N G) (v : MotherVocabularyOrigin.Presentation V W)
    (original : SourceNativeSource N V) (generated : SourceNativeSource G W) where
  initial_eq : generated.initial = v.current original.initial
  event : ∀ c, original.toRootSource.actual.OccurrenceAt c ≃
    generated.toRootSource.actual.OccurrenceAt (v.current c)
  compile_eq : ∀ c e, generated.toRootSource.actual.compile (event c e) =
    v.evolution c (original.toRootSource.actual.compile e)
  support_eq : ∀ c e, (event c e).1 = n.support e.1
  anchor_eq : ∀ x, generated.law.anchorKey (v.anchor x) = n.anchor (original.law.anchorKey x)
  incidence_eq : ∀ x, generated.law.incidenceKey (v.incidence x) = n.incidence (original.law.incidenceKey x)
  lineage_eq : ∀ x, generated.law.lineageKey (v.lineage x) = n.lineage (original.law.lineageKey x)

private def presentationEquiv {A B : Type} (p : ConstructivePresentation A B) : A ≃ B where
  toFun := p.forward
  invFun := p.backward
  left_inv := p.backward_forward
  right_inv := p.forward_backward

/-- Both complete inventory presentations and the generated full ledger
equivalence are consumed. The only cast follows the exact support equality. -/
def Presentation.inventory {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    (p : Presentation n v original generated) {c : V.Current}
    (event : original.toRootSource.actual.OccurrenceAt c) :
    original.law.AffectedInventoryAt event.2 ≃ generated.law.AffectedInventoryAt (p.event c event).2 :=
  (presentationEquiv (original.law.affectedInventoryPresentation event.2)).trans
    ((n.ledger event.1).trans
      ((Equiv.cast (congrArg (OpenResponsibilityAt G) (p.support_eq c event).symm)).trans
        (presentationEquiv (generated.law.affectedInventoryPresentation (p.event c event).2)).symm))

def accountPresentation {net base events fields : M}
    {hn : MotherNetworkFactory.Check net} {hv : MotherVocabularyOrigin.Check base}
    {ha : MotherActualOrigin.Check base events hv}
    {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}}
    (n : MotherNetworkOrigin.Presentation N (network net hn))
    (v : MotherVocabularyOrigin.Presentation V (MotherActualOrigin.V base hv))
    (original : SourceNativeSource N V)
    (a : MotherActualOrigin.Presentation v original.toRootSource.actual (MotherActualOrigin.actual base events hv ha))
    (hm : MotherHigherLawFormation.read fields = AccountEncoding.reader n v original.toRootSource a) :
    Presentation n v original
      (native (rootSource net base events fields hn hv ha
        (AccountEncoding.graphs n v original.toRootSource a hm)
        (AccountEncoding.compatible n v original.toRootSource a hm))) := by
  let root := rootSource net base events fields hn hv ha
    (AccountEncoding.graphs n v original.toRootSource a hm)
    (AccountEncoding.compatible n v original.toRootSource a hm)
  change Presentation n v original (native root)
  refine {
    initial_eq := AccountEncoding.initial_value n v original.toRootSource a hm
    event := fun c => (a.event c).trans (eventEquiv root (v.current c))
    compile_eq := ?_
    support_eq := ?_
    anchor_eq := AccountEncoding.anchor_value n v original.toRootSource a hm
    incidence_eq := AccountEncoding.incidence_value n v original.toRootSource a hm
    lineage_eq := AccountEncoding.lineage_value n v original.toRootSource a hm }
  · intro c event
    exact (compile_original root (a.event c event)).trans (a.compile_commutes c event)
  · intro c event
    exact (support_original root (a.event c event)).trans
      (AccountEncoding.support_value n v original.toRootSource a hm c event)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeSourceOrigin
