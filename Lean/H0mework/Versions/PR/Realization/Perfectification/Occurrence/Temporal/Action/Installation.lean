import H0mework.Versions.AD.Realization.Perfectification.Occurrence.Temporal.Action.Inverse
import H0mework.Versions.PR.Realization.Perfectification.Occurrence.Temporal.Consumer
/-! The original calculation consumes its source-generated inverse word.
Complete temporal material precedes the emitter and survives every stage. -/
set_option autoImplicit false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceTemporalMaterial.Action
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
variable {N : WorldRelationNetwork.{u}} {V : Vocabulary.{u}}
variable (root : SourceNativeLivingRootClosure N V)
variable (origin : SourceNativeTemporalVisitAt (lower root))
abbrev code := encode (lower root) origin
variable (U7 : U7ProducerCalculus N) (calculus : U7ObstructionEvolutionCalculus N U7)
def Material : Type u := Result root ×
  RootGeneratedDebtActivationJointSource.OwnerFree.Raw
    (Value:=SourceOperationScalarInventoryLift.PairValue (Value root)) (Var:=Var) (sort:=Slot.result) ×
  (Σ old : Env (Value root) Var,
    SourceOperationExecution.Trace old (programme root) (.const ((programme root).eval old))) ×
  (Σ following : Env (Value root) Var,
    SourceOperationExecution.Trace following (programme root) (.const ((programme root).eval following))) ×
  SourceOperationLogic.Fibre (SourceOperationScalarRelations.evaluation (R:=ℤ)
    (environment root (code root origin) + delta root (code root origin)))
    (SourceOperationLogic.q (SourceOperationScalarRelations.evaluation (R:=ℤ)
      (environment root (code root origin) + delta root (code root origin))) (oldWord root (code root origin))) ×
  SourceOperationLogic.FibreLift.LiftingResidual (morphism root (code root origin))
def material : Material root origin :=
  ⟨actual root (code root origin), residualRaw root (code root origin),
    ⟨environment root (code root origin), sourceTrace root (code root origin)⟩,
    ⟨updatedEnvironment root (code root origin), nextTrace root (code root origin)⟩,
    target root (code root origin), reverse root (code root origin)⟩
def component : SourceNativeProjectionLaw root.source.base.restructuringSource.toLedgerSource where
  Projection := PUnit.{u+1}
  ActiveAt := fun _ {_current} _ => PUnit.{u+1}
  InactiveAt := fun _ {_current} _ => PEmpty.{u+1}
  classify := fun _ {_current} _ => .inl PUnit.unit
  PayloadAt := fun _ {_current} _ _ => Material root origin
  project := fun _ {_current} _ _ => material root origin
def reader (occurrence : (lower root).source.source.toRootSource.actual.OccurrenceAt origin.current) :=
  ((component root origin).project PUnit.unit occurrence PUnit.unit).2.1
abbrev materialRoot := root.withProjectionCoface (component root origin)
abbrev materialVisit : SourceNativeTemporalVisitAt (materialRoot root origin).toAuthoritativeRoot.toLedgerRoot := origin
namespace C
export SourceTemporalMaterial.Calculation (sourceRoot sourceVisit runtime face readback)
end C
namespace M
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source (frame)
end M
abbrev runtime := C.runtime (materialRoot root origin) (materialVisit root origin) U7 calculus (reader root origin)
abbrev frame := M.frame (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (C.sourceVisit (materialRoot root origin) (materialVisit root origin)) U7 calculus (reader root origin)
def materialFace (count : Nat) : SourceNativeRootSemanticFaceAt
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.root
      (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin)
      U7 calculus (reader root origin) count)
    (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.Math.Inquiry.Source.visit
      (C.sourceRoot (materialRoot root origin) (materialVisit root origin)) (materialVisit root origin)
      (reader root origin) count) where
  projection := .inherited (.inherited (.inherited
    ((RootGeneratedDebtActivationJointSource.OwnerFree.baseInstallation
      (C.sourceRoot (materialRoot root origin) (materialVisit root origin)).toAuthoritativeRoot
      origin.current (reader root origin)).embed (.inl (.inherited (.component PUnit.unit))))))
  active := PUnit.unit
  classifier_eq := rfl
end SourceTemporalMaterial.Action
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
