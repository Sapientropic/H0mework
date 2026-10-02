import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Compiler.Programs.Exact.WriteGenerated

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
open MotherFullCompiler MotherSourcePrograms MotherExactPrograms
open ResponsibilityLifecycle.LivingLawEvolution
open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
noncomputable section

variable {N : WorldRelationNetwork.{0}} {V : Vocabulary.{0}} {source : SourceNativeSource N V}

abbrev Destination (operations : Transitions source) (context : RemainderContext source)
    (entry : OpenResponsibilityAt N context.1.2.1) :=
  Σ target : OpenResponsibilityAt N context.2,
    RowOutput operations ⟨context.1.1, context.1.2, context.2, entry, target⟩

abbrev Origin (operations : Transitions source) (context : RemainderContext source)
    (entry : OpenResponsibilityAt N context.2) :=
  Σ origin : OpenResponsibilityAt N context.1.2.1,
    RowOutput operations ⟨context.1.1, context.1.2, context.2, origin, entry⟩

abbrev CertifiedBody (operations : Transitions source) (context : RemainderContext source) :=
  ((entry : OpenResponsibilityAt N context.1.2.1) → Destination operations context entry) ×
    ((entry : OpenResponsibilityAt N context.2) → Origin operations context entry)

abbrev RemainderOutput (operations : Transitions source) (context : RemainderContext source) :=
  Sigma (MotherExactPrograms.WriteEncoding.Certification operations context)

/-- Each destination/origin keeps its exact row and Type-valued certificate
together. Both complete sections remain independent. -/
def certifiedBodyEquiv (operations : Transitions source) (context : RemainderContext source) :
    RemainderOutput operations context ≃ CertifiedBody operations context where
  toFun := fun ⟨whole, certified⟩ =>
    (fun entry => ⟨(whole.destination entry).1, (whole.destination entry).2, certified.destination entry⟩,
      fun entry => ⟨(whole.origin entry).1, (whole.origin entry).2, certified.origin entry⟩)
  invFun := fun ⟨destination, origin⟩ =>
    ⟨{ destination := fun entry => ⟨(destination entry).1, (destination entry).2.1⟩
       origin := fun entry => ⟨(origin entry).1, (origin entry).2.1⟩ },
      { destination := fun entry => (destination entry).2.2
        origin := fun entry => (origin entry).2.2 }⟩
  left_inv := by
    rintro ⟨⟨destination, origin⟩, ⟨destinationCertificate, originCertificate⟩⟩
    rfl
  right_inv := by
    rintro ⟨destination, origin⟩
    rfl

def castRowSource (G : WorldRelationNetwork.{0}) {left right target : G.Support} (same : left = right)
    (a : OpenResponsibilityAt G left) (b : OpenResponsibilityAt G target) :
    LedgerEntryEvolutionAt G a b ≃
      LedgerEntryEvolutionAt G (Equiv.cast (congrArg (OpenResponsibilityAt G) same) a) b := by
  cases same
  exact Equiv.refl _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointWrite
