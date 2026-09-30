import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.AuthorityRestriction.Consumer

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot
open MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
noncomputable section

abbrev LedgerRoot (value : SourcePair) := value.1.1.1.1.2.2

/-- The all-current emitter belongs to the actual root already present in
the generated declaration. Its inverse is retained along with the source. -/
structure Presentation {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (root : SourceNativeAuthoritativeRootClosure N V) (value : SourcePair)
    (data : PresentationData value) (surface : TheoryState value.1.1.1.1.1)
    extends MotherAuthorityRestriction.Presentation root.source value data surface where
  emitted_eq : ∀ current, (represented.event current).symm
    ((LedgerRoot value).emitted (vocabulary.current current)) = root.emitted current

abbrev RootSection {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeAuthoritySource N V) :=
  { emitted : (current : V.Current) → source.restructuringSource.source.toRootSource.actual.OccurrenceAt current //
    ∀ current, (source.restructuringSource.compiler.ledgerCompiler.compile (emitted current)).CommutesWith emitted }

def assemble {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeAuthoritativeRootClosure N V)
    (source : SourceNativeAuthoritySource N V) (same : source = old.source)
    (fields : RootSection old.source) : SourceNativeAuthoritativeRootClosure N V :=
  let restored := Equiv.cast (congrArg RootSection same.symm) fields
  ⟨source, restored.val, restored.property⟩

theorem assemble_eq {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (old : SourceNativeAuthoritativeRootClosure N V)
    (source : SourceNativeAuthoritySource N V) (same : source = old.source)
    (fields : RootSection old.source) (emitted_eq : fields.val = old.emitted) :
    assemble old source same fields = old := by
  cases old with
  | mk oldSource emitted commutes =>
    cases same
    cases fields with
    | mk restored valid =>
      cases emitted_eq
      rfl

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    {root : SourceNativeAuthoritativeRootClosure N V} {value : SourcePair}
    {data : PresentationData value} {surface : TheoryState value.1.1.1.1.1}
    (p : Presentation root value data surface)

def Presentation.readEmitted : (current : V.Current) →
    root.source.restructuringSource.source.toRootSource.actual.OccurrenceAt current :=
  fun current => (p.represented.event current).symm ((LedgerRoot value).emitted (p.vocabulary.current current))

theorem Presentation.readEmitted_eq : p.readEmitted = root.emitted :=
  funext p.emitted_eq

def Presentation.restrict : SourceNativeAuthoritativeRootClosure N V :=
  assemble root p.toPresentation.restrict p.toPresentation.restrict_eq
    ⟨p.readEmitted, by rw [p.readEmitted_eq]; exact root.compiler_commutes⟩

theorem Presentation.restrict_eq : p.restrict = root :=
  assemble_eq root p.toPresentation.restrict p.toPresentation.restrict_eq _ p.readEmitted_eq

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherAuthorityRoot
