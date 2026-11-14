import H0mework.Versions.Rc19e94a5.ReleaseMaterials.SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.Formation.Declarations.NativeQuery.ValueScalarCoimageConsumer
import H0mework.Realization.Operations.ObservationNative
import H0mework.Realization.Operations.DerivationReduction

/-! The original installed duration material supplies a whole function-ring
source observation. Its complete native state/generator words retain the
exact visit, and only the original successor moves that context. This is the
sealed unit-emitter chain; the original full duration exposure is retained. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery.ActionFeed

open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open SourceGeneratedActionObservationHistory RawGeneratedRoot.CofinalAction CofinalFaithfulSettlementFace

noncomputable section

abbrev G := MotherPhysicalSource.Generator
abbrev B := MotherPhysicalSource.Carrier

def installedRaw (law : MotherPhysicalLaws.Law) (depth : (process law).State) :
    SourceNativeCofinalFaithfulMaterialLaw.RawAt (Carrier := B) G
      (anchorAt law depth).2 :=
  (declarationSource law).projectionLaw.project
    ((historyInstallation law).embed (.component PUnit.unit))
    (anchorAt law depth).2 PUnit.unit

theorem installed_raw_fields (law : MotherPhysicalLaws.Law) (depth : (process law).State) :
    (installedRaw law depth).history.rootExposure =
      MotherPhysicalSource.rootExposureAt law (anchorAt law depth).2 ∧
    (installedRaw law depth).history.seed =
      MotherPhysicalSource.seedAt law (anchorAt law depth).2 ∧
    (installedRaw law depth).history.continuation =
      MotherPhysicalSource.continuationAt law (anchorAt law depth).2 ∧
    (installedRaw law depth).evaluator =
      MotherPhysicalSource.evaluatorAt law (anchorAt law depth).2 := ⟨rfl, rfl, rfl, rfl⟩

def read (law : MotherPhysicalLaws.Law) (depth : (process law).State) (generator : G) : B :=
  (installedRaw law depth).evaluator.root generator

abbrev ValueC (law : MotherPhysicalLaws.Law) := ((process law).State × G) →₀ B

def valueAction (law : MotherPhysicalLaws.Law) : ValueC law →ₗ[B] ValueC law :=
  Finsupp.lmapDomain B B (fun atom => ((process law).successor atom.1, atom.2))

def valueObserve (law : MotherPhysicalLaws.Law) : ValueC law →ₗ[B] B :=
  Finsupp.linearCombination B (fun atom => read law atom.1 atom.2)

def valueInclude (law : MotherPhysicalLaws.Law) (runtime : LivingRuntimeState (process law)) :
    (G →₀ B) →ₗ[B] ValueC law :=
  Finsupp.lmapDomain B B (fun generator => (runtime.state, generator))

theorem whole_value_slice (law : MotherPhysicalLaws.Law) (runtime : LivingRuntimeState (process law)) :
    (valueObserve law).comp (valueInclude law runtime) =
      valueWordEvaluation (MotherPhysicalSource.receiptAction law) (anchorAt law runtime.state).2 := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  simp only [LinearMap.comp_apply, valueInclude, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    valueObserve, Finsupp.linearCombination_single, valueWordEvaluation]
  exact (Finsupp.linearCombination_single (R := B)
    (v := fun g => read law runtime.state g) coefficient generator).symm

theorem whole_action_slice (law : MotherPhysicalLaws.Law) (runtime : LivingRuntimeState (process law)) :
    (valueAction law).comp (valueInclude law runtime) = valueInclude law runtime.tick.next := by
  apply Finsupp.lhom_ext
  intro generator coefficient
  simp only [LinearMap.comp_apply, valueAction, valueInclude, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_single]
  rfl

abbrev OperationValue (law : MotherPhysicalLaws.Law) : Bool → Type
  | false => ValueC law
  | true => B

instance (law : MotherPhysicalLaws.Law) : (slot : Bool) → AddCommGroup (OperationValue law slot)
  | false => inferInstance
  | true => inferInstance

def operationEnvironment (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (word : G →₀ B) :
    SourceOperationEffects.Env (OperationValue law)
      (fun _ => PUnit.{1}) :=
  fun slot _ => match slot with
    | false => valueInclude law runtime word
    | true => 0

def operationExpression (law : MotherPhysicalLaws.Law) :
    SourceOperationEffects.Expr (OperationValue law)
      (fun _ => PUnit.{1}) true :=
  .linear (s := false) (valueObserve law).toAddMonoidHom
    (.linear (s := false) (valueAction law).toAddMonoidHom (.var PUnit.unit))

def operationProof (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (word : G →₀ B) :=
  SourceOperationDerivations.Derivation.normalize (operationEnvironment law runtime word)
    (operationExpression law)

theorem operation_proof_reads_next (law : MotherPhysicalLaws.Law)
    (runtime : LivingRuntimeState (process law)) (word : G →₀ B) :
    (operationExpression law).eval (operationEnvironment law runtime word) =
      valueObserve law (valueInclude law runtime.tick.next word) := by
  have generated := (operationProof law runtime word).sound
  change valueObserve law (valueAction law (valueInclude law runtime word)) =
    valueObserve law (valueAction law (valueInclude law runtime word)) at generated
  exact generated.trans (congrArg (valueObserve law)
    (LinearMap.congr_fun (whole_action_slice law runtime) word))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativeQuery.ActionFeed
