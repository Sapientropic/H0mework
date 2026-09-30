import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Joint.Body

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N G : WorldRelationNetwork.{0}} {V W : Vocabulary.{0}}
    {original : SourceNativeSource N V} {generated : SourceNativeSource G W}
    {n : MotherNetworkOrigin.Presentation N G} {v : MotherVocabularyOrigin.Presentation V W}
    (p : MotherNativeSourceOrigin.Presentation n v original generated)
    {old : Transitions original} {formed : Transitions generated}
    (q : TransitionPresentation (transportedTransitions p old) formed)

def sourceEntryEquiv (point : Point original) :
    OpenResponsibilityAt N point.2.1 ≃ OpenResponsibilityAt G (pointEquiv p point).2.1 :=
  (n.ledger point.2.1).trans (Equiv.cast (congrArg (OpenResponsibilityAt G) (p.support_eq point.1 point.2).symm))

def remainderContextEquiv : RemainderContext original ≃ RemainderContext generated :=
  Equiv.prodCongr (pointEquiv p) n.support

def rowEvolutionEquiv (context : WriteContext original) :
    LedgerEntryEvolutionAt N context.2.2.2.1 context.2.2.2.2 ≃
      LedgerEntryEvolutionAt G (writeContextEquiv p context).2.2.2.1 (writeContextEquiv p context).2.2.2.2 :=
  (n.rowEquiv context.2.2.2.1 context.2.2.2.2).trans
    (castRowSource G (p.support_eq context.1 context.2.1).symm
      (n.ledger context.2.1.1 context.2.2.2.1) (n.ledger context.2.2.1 context.2.2.2.2))

def rowOutputEquiv (context : WriteContext original) :
    RowOutput old context ≃ RowOutput formed (writeContextEquiv p context) :=
  Equiv.prodCongr (rowEvolutionEquiv p context) (formedExactMember p q context)

def destinationEquiv (context : RemainderContext original) (entry : OpenResponsibilityAt N context.1.2.1) :
    Destination old context entry ≃
      Destination formed (remainderContextEquiv p context) (sourceEntryEquiv p context.1 entry) :=
  Equiv.sigmaCongr (n.ledger context.2)
    (fun target => rowOutputEquiv p q ⟨context.1.1, context.1.2, context.2, entry, target⟩)

def originEquiv (context : RemainderContext original) (entry : OpenResponsibilityAt N context.2) :
    Origin old context entry ≃ Origin formed (remainderContextEquiv p context) (n.ledger context.2 entry) :=
  Equiv.sigmaCongr (sourceEntryEquiv p context.1)
    (fun origin => rowOutputEquiv p q ⟨context.1.1, context.1.2, context.2, origin, entry⟩)

/-- Both complete certified sections move through their real entry indices;
the target entry, row evolution and exact member travel in the same Sigma. -/
def certifiedBodyTransport (context : RemainderContext original) :
    CertifiedBody old context ≃ CertifiedBody formed (remainderContextEquiv p context) :=
  Equiv.prodCongr (Equiv.piCongr (sourceEntryEquiv p context.1) (destinationEquiv p q context))
    (Equiv.piCongr (n.ledger context.2) (originEquiv p q context))

def remainderOutputEquiv (context : RemainderContext original) :
    RemainderOutput old context ≃ RemainderOutput formed (remainderContextEquiv p context) :=
  (certifiedBodyEquiv old context).trans
    ((certifiedBodyTransport p q context).trans (certifiedBodyEquiv formed (remainderContextEquiv p context)).symm)

theorem complete_remainder_restores (context : RemainderContext original) (value : RemainderOutput old context) :
    (remainderOutputEquiv p q context).symm (remainderOutputEquiv p q context value) = value :=
  (remainderOutputEquiv p q context).symm_apply_apply value

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
