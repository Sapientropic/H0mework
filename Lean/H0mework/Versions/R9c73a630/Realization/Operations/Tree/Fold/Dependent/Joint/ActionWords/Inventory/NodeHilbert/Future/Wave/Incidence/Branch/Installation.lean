import H0mework.Versions.R9c73a630.Realization.Operations.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.Incidence.Branch.Source
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceBranch
open RootInquiryCompletion RootLawDependentJointStateController RootLawDependentJointTransition RootLawDependentJointPassiveEffect
open SourceOperationEffects SourceOperationExecution
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (root : SourceNativeLivingRootClosure N V) (recognition : RecognitionAt H root)
variable (visit : SourceNativeTemporalVisitAt root.toAuthoritativeRoot.toLedgerRoot)
variable (successor : StepLedgerSuccessorAt (recognition.generateStepAt visit))
variable (transition : GeneratedStepJointTransitionAt (recognition.generateStepAt visit) successor)
variable (alignment : RootedAccountedUnfoldingZip.GeneratedZipAt
  (stepSourcePairingOccurrence (recognition.generateStepAt visit))
  (stepTargetPairingOccurrence (recognition.generateStepAt visit) successor))
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7) (count : Nat)


variable (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
variable (bound : Nat) (queryWord : List (Letter root recognition visit successor)) (letter : Letter root recognition visit successor)
abbrev orbitEnvironment := PaidSourceOrbit.NativeOrbitProgramme.orbitEnvironment
  (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).integralFace.toAddMonoidHom
abbrev orbitProgramme := PaidSourceOrbit.NativeOrbitProgramme.nextProgramme
  (I:=Model root recognition visit successor transition alignment U7 calculus count) (PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter).toAddMonoidHom
theorem orbit_eval (value : PaidSourceFullOrbit.FullCarrier root recognition visit successor transition alignment U7 calculus count) :
    (orbitProgramme root recognition visit successor transition alignment U7 calculus count letter).eval (orbitEnvironment root recognition visit successor transition alignment U7 calculus count value)=PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter value := rfl
abbrev nextValue := PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter (current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
def actionRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=PaidSourceIncidence.Value root recognition visit successor transition alignment U7 calculus count) (Var:=PaidSourceIncidence.Var) (sort:=PaidSourceIncidence.Slot.orbit) :=
  ⟨orbitEnvironment root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord),orbitProgramme root recognition visit successor transition alignment U7 calculus count letter⟩
def pairRaw : RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue (PaidSourceIncidence.Value root recognition visit successor transition alignment U7 calculus count)) (Var:=PaidSourceIncidence.Var) (sort:=PaidSourceIncidence.Slot.orbit) :=
  ⟨SourceOperationScalarInventoryLift.pairEnvironment
      (actionRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).environment
      (orbitEnvironment root recognition visit successor transition alignment U7 calculus count (nextValue root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)-
        (actionRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).environment),
    SourceOperationScalarInventoryLift.liftExpr (orbitProgramme root recognition visit successor transition alignment U7 calculus count letter)⟩
def pairReader {current : V.Current}
    (_ : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt current) :=
  pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter
abbrev pairResult := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.resultAt root.toAuthoritativeRoot
  (pairReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) (root.emitted visit.current)
def material := (sourceTree root recognition visit,targetTree root recognition visit successor,
  Wave.material root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord,
  (raw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord,result root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord),
  (selected root recognition visit successor transition alignment U7 calculus count bound queryWord,selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord,
    PaidSourceFullRecovery.together root recognition visit successor transition alignment U7 calculus count,PaidSourceFullRecovery.recover root recognition visit successor transition alignment U7 calculus count,
    PaidSourceFullRecovery.emit root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)),letter,
  PaidSourceFullOrbit.advance root recognition visit successor transition alignment U7 calculus count letter,current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord,
  (PaidSourceFullOrbit.input root recognition visit successor transition alignment U7 calculus count).incidence queryWord (selectedPoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord),
  queryWord,actionRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
def component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1} ⊕ PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun projection {_current} _ _ => match projection with
    | .inl _ => type_of% (material root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
    | .inr _ => type_of% (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter,
        pairResult root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
  project := fun projection {_current} _ _ => match projection with
    | .inl _ => material root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter
    | .inr _ => (pairRaw root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter,
        pairResult root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
abbrev sourceRoot := root.withProjectionCoface (component root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
def actionReader (point : Carrier root recognition visit successor) (seedWord : List (Letter root recognition visit successor))
    (bound : Nat) (queryWord : List (Letter root recognition visit successor)) (letter : Letter root recognition visit successor)
    (occurrence : root.toAuthoritativeRoot.toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt visit.current) :=
  ((component root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).project (.inl PUnit.unit) occurrence PUnit.unit).2.2.2.2.2.2.2.2.2.2
abbrev runtime := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.runtime
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) visit U7 calculus
  (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
abbrev endpoint := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.endpointCount
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) visit
  (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
abbrev paid := RootGeneratedDebtActivationJointSource.OwnerFree.Completion.runtime
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).toAuthoritativeRoot visit.current
  (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
  (endpoint root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
abbrev ledgerSeed := RootGeneratedDebtActivationJointSource.OwnerFree.Relations.exposure
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).toAuthoritativeRoot visit.current
  (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
  (paid root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
abbrev fixedFrame := RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.frame
  (sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter) visit U7 calculus
  (actionReader root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
abbrev frame := {fixedFrame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter with
  environment := fun {_current} _occurrence => orbitEnvironment root recognition visit successor transition alignment U7 calculus count
    (((component root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).project (.inl PUnit.unit)
      ((sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).emitted visit.current) PUnit.unit).2.2.2.2.2.2.1
      (((component root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).project (.inl PUnit.unit)
        ((sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).emitted visit.current) PUnit.unit).2.2.2.2.2.2.2.1))
  inventory := some (SourceOperationPaidRelations.exposure
    (((component root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).project (.inl PUnit.unit)
      ((sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).emitted visit.current) PUnit.unit).2.2.2.1.2.2.1.2))
  pairInventory := some (SourceOperationPaidRelations.exposure
    (((component root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).project (.inr PUnit.unit)
      ((sourceRoot root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter).emitted visit.current) PUnit.unit).2.2.1.2)) }
abbrev continuation := SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.UpdatedFaces.InverseRead.generated
  (ledgerSeed root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
  (frame root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter)
abbrev generated := (runtime root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter,
  continuation root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord letter,
  PaidSourceFullRecovery.emit root recognition visit successor transition alignment U7 calculus count (current root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord),
  Wave.generated root recognition visit successor transition alignment U7 calculus count point seedWord bound queryWord)
end SourceOperationNative.Tree.Fold.Dependent.Joint.ActionWords.Inventory.NodeHilbert.Future.Wave.PaidSourceIncidenceBranch
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
