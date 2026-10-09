import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualRegisteredBornEffect"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualRegisteredBornEffect
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarRelations SourceOperationScalarPresentation SourceGeneratedScalarDifferentialResidual
namespace T
export ActualNativeRelationTransport (paid)
end T
namespace B
export ActualNativeBornSourceEffect (born actual_born_registered_expression)
end B
namespace M
export SourceOperationInquiry.Context.Faces.Execution.Activation.M (Frame)
end M
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (expression input updated_value)
end N
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace (boundary sourceOccurrence complex wholeFaces effectFaces paidCoordinate actual_inverse whole_recovery native_zero_iff)
end F
variable {Sorts : Type u} {Value Var : Sorts → Type u} [∀ s, AddCommGroup (Value s)] {sort : Sorts}
variable (frame : M.Frame (Value := Value) (Var := Var) (sort := sort))
variable (cfg : A.Programme (PhysicalValue := Value) (PhysicalVar := Var) (sort := sort))
def delta := (B.born frame cfg).activeEnvironment - (T.paid frame).environment
/-- Retain the completed source Trace and occurrence while reading its actual decoded successor update. -/
def transported := { T.paid frame with increment := delta frame cfg }
theorem actual_input : (N.input (transported frame cfg)).environment = (B.born frame cfg).activeEnvironment := by
 change (T.paid frame).environment + ((B.born frame cfg).activeEnvironment - (T.paid frame).environment) = _
 abel

theorem original_boundary : F.boundary (transported frame cfg) = F.boundary (T.paid frame) := rfl

theorem original_trace : (transported frame cfg).state.2 = (T.paid frame).state.2 := rfl

theorem same_source_occurrence : F.sourceOccurrence (transported frame cfg) = F.sourceOccurrence (T.paid frame) := rfl

theorem same_complex : F.complex (transported frame cfg) = F.complex (T.paid frame) := rfl

theorem complete_word (word : Formal ℤ Value Var sort) :
 SourceGeneratedCompleteWordDual.coimageRecovery ((F.wholeFaces (transported frame cfg)).canonical word) = word :=
 F.whole_recovery (transported frame cfg) word

theorem registered_effect : (B.born frame cfg).registered.input.expression.eval (B.born frame cfg).activeEnvironment =
 effectEvaluator (R := ℤ) (T.paid frame).environment (delta frame cfg) (F.boundary (T.paid frame)) := by
 rw [B.actual_born_registered_expression]
 have generated := N.updated_value (R := ℤ) (transported frame cfg)
 exact (congrArg (fun environment => (N.expression (transported frame cfg)).eval environment)
  (actual_input frame cfg)).symm.trans generated

theorem registered_inverse :
 ((F.effectFaces (transported frame cfg)).rangeEquiv (F.paidCoordinate (transported frame cfg))).val =
 (B.born frame cfg).registered.input.expression.eval (B.born frame cfg).activeEnvironment := by
 rw [B.actual_born_registered_expression]
 exact (F.actual_inverse (transported frame cfg)).trans
  (congrArg (fun environment => (N.expression (transported frame cfg)).eval environment) (actual_input frame cfg))

theorem registered_pair : updateInventory (R := ℤ) (T.paid frame).environment (delta frame cfg)
 (F.boundary (T.paid frame)) = (0, (B.born frame cfg).registered.input.expression.eval (B.born frame cfg).activeEnvironment) :=
 ((T.paid frame).state.2.relation_inventory (R := ℤ) (delta frame cfg)).trans
  (congrArg (fun value => (0,value)) (registered_effect frame cfg).symm)

theorem registered_zero_iff : F.paidCoordinate (transported frame cfg) = 0 ↔
 (B.born frame cfg).registered.input.expression.eval (B.born frame cfg).activeEnvironment = 0 := by
 have same := (F.actual_inverse (transported frame cfg)).symm.trans (registered_inverse frame cfg)
 exact (F.native_zero_iff (transported frame cfg)).trans (by rw [same])

def affineCertificate := normalizationCertificate (R := ℤ) (B.born frame cfg).activeEnvironment (F.boundary (T.paid frame))
theorem registered_affine_write : relationMap (R := ℤ) (B.born frame cfg).activeEnvironment (affineCertificate frame cfg) =
 F.boundary (T.paid frame) - constantMap (R := ℤ)
  (valueMap (R := ℤ) (B.born frame cfg).activeEnvironment (F.boundary (T.paid frame))) := source_reduction _ _

end ActualRegisteredBornEffect
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
