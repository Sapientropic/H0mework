import H0mework.Versions.PR.Realization.Operations.Tree.Fold.Dependent.Branch.Relation.Incoming.Request.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request
open RootLawDependentJointStateController CofinalHistorySettlement SourceOperationEffects SourceOperationExecution
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (recognition : RecognitionAt H root)
variable (count : Nat)
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
abbrev querySource := (paidRuntime root visit recognition count).current.root
abbrev queryVisit := (paidRuntime root visit recognition count).current.visit
abbrev queryU7 := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.U7
  (actualRoot root visit recognition) visit U7 (installedReader root visit recognition)
abbrev queryCalculus := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.calculus
  (actualRoot root visit recognition) visit U7 calculus (installedReader root visit recognition)

abbrev Material := ResidualDispositionOutcome (face root visit recognition count) ×
  Word root visit recognition × RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=Value root visit recognition) (Var:=ChangedVar (Variable root visit recognition))
    (sort:=SourceOperationNative.Tree.Fold.Slot.result) ×
  (SourceTemporalMaterial.Code (querySource root visit recognition count).toAuthoritativeRoot.toLedgerRoot) ×
  type_of% (RootGeneratedDebtActivationJointSource.OwnerFree.runtimeCurrent
    (actualRoot root visit recognition).toAuthoritativeRoot visit.current (installedReader root visit recognition)
      (paidRuntime root visit recognition count))

def material (word : Word root visit recognition) : Material root visit recognition count :=
  ⟨disposition root visit recognition count,word,rawOfWord root visit recognition word,
    SourceTemporalMaterial.encode (querySource root visit recognition count).toAuthoritativeRoot.toLedgerRoot
      (queryVisit root visit recognition count),
    RootGeneratedDebtActivationJointSource.OwnerFree.runtimeCurrent (actualRoot root visit recognition).toAuthoritativeRoot
      visit.current (installedReader root visit recognition) (paidRuntime root visit recognition count)⟩

def component (word : Word root visit recognition) : SourceNativeProjectionLaw
    (querySource root visit recognition count).source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Material root visit recognition count
  project := fun _ {_current} _ _ => material root visit recognition count word

abbrev requestRoot (word : Word root visit recognition) :=
  (querySource root visit recognition count).withProjectionCoface (component root visit recognition count word)

def requestReader (word : Word root visit recognition)
    (occurrence : (querySource root visit recognition count).toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
      (queryVisit root visit recognition count).current) :=
  ((component root visit recognition count word).project PUnit.unit occurrence PUnit.unit).2.2.1

abbrev requestRuntime (word : Word root visit recognition) :=
  RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.runtime
    (requestRoot root visit recognition count word) (queryVisit root visit recognition count)
    (queryU7 root visit recognition U7) (queryCalculus root visit recognition U7 calculus)
    (requestReader root visit recognition count word)

end SourceOperationNative.Tree.Fold.Dependent.Branch.Relation.Incoming.Request
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
