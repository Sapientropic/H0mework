import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Next.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Registered.Source
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualCanonicalBornSource"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualCanonicalBornSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open SourceOperationScalarRelations SourceOperationScalarPresentation
namespace E
export ActualRegisteredBornEffect
 (transported delta affineCertificate registered_effect registered_inverse registered_affine_write registered_zero_iff)
end E
namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace
 (boundary source_boundary effectFaces paidCoordinate)
end F

private theorem boundary_valueMap
 {Sorts : Type u} {Value Var : Sorts → Type u} [∀ target, AddCommGroup (Value target)] {s : Sorts}
 {Network : WorldRelationNetwork.{u}} {Vocabulary : ConstructiveRoot.Vocabulary.{u}}
 {lower : SourceNativeLedgerRootClosure Network Vocabulary} {current : Vocabulary.Current}
 {occurrence : lower.source.source.toRootSource.actual.OccurrenceAt current}
 (material : N.MaterialAt (Value := Value) (Var := Var) (sort := s) occurrence)
 (environment : Env Value Var) :
 ScalarRelationPresentation.freeEvaluation (R := ℤ) (Value s)
  (valueMap (R := ℤ) environment (F.boundary material)) =
 (N.expression material).eval environment := by
 have evaluated : evaluation (R := ℤ) environment (F.boundary material) =
  (N.expression material).eval environment := by
  have raw := congrArg (fun word => evaluation (R := ℤ) environment word) (F.source_boundary material)
  simp only [map_sub, evaluation, Finsupp.linearCombination_single, one_smul] at raw
  exact raw.trans (RootGeneratedDebtActivationJointSource.Native.ResidualRequest.expression_eval material environment).symm
 exact (LinearMap.congr_fun (valueMap_evaluation (R := ℤ) (s := s) environment)
  (F.boundary material)).trans evaluated

variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance consumerGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) :=
 L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

private theorem cofinal_registered_expression (ordinal : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 (cofinalRegisteredAtNext factory initial cfg language ordinal branch).expression =
 (B.born (C.selected branch.1) branch.1.2.2.1).registered.input.expression :=
 (cofinalRegisteredAtNext_source factory initial cfg language ordinal branch).1.trans
  (B.actual_born_registered_expression (C.selected branch.1) branch.1.2.2.1).symm

theorem cofinal_registered_effect (ordinal : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 (cofinalRegisteredAtNext factory initial cfg language ordinal branch).expression.eval
  (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment =
 effectEvaluator (R := ℤ) (T.paid (C.selected branch.1)).environment
  (E.delta (C.selected branch.1) branch.1.2.2.1) (F.boundary (T.paid (C.selected branch.1))) :=
 (congrArg (fun expression => expression.eval
  (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment)
  (cofinal_registered_expression factory initial cfg language ordinal branch)).trans
  (E.registered_effect (C.selected branch.1) branch.1.2.2.1)

theorem cofinal_registered_inverse (ordinal : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 ((F.effectFaces (E.transported (C.selected branch.1) branch.1.2.2.1)).rangeEquiv
  (F.paidCoordinate (E.transported (C.selected branch.1) branch.1.2.2.1))).val =
 (cofinalRegisteredAtNext factory initial cfg language ordinal branch).expression.eval
  (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment :=
 (E.registered_inverse (C.selected branch.1) branch.1.2.2.1).trans
  (congrArg (fun expression => expression.eval
   (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment)
   (cofinal_registered_expression factory initial cfg language ordinal branch)).symm

/-- Keep the literal coefficient word and connect its scalar readout to the actual next request. -/
theorem cofinal_registered_affine (ordinal : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 relationMap (R := ℤ) (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment
  (E.affineCertificate (C.selected branch.1) branch.1.2.2.1) =
 F.boundary (T.paid (C.selected branch.1)) - constantMap (R := ℤ)
  (valueMap (R := ℤ) (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment
   (F.boundary (T.paid (C.selected branch.1)))) ∧
 ScalarRelationPresentation.freeEvaluation (R := ℤ) (L.Value W branch.1.1 s)
  (valueMap (R := ℤ) (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment
   (F.boundary (T.paid (C.selected branch.1)))) =
 (cofinalRegisteredAtNext factory initial cfg language ordinal branch).expression.eval
  (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment :=
 ⟨E.registered_affine_write (C.selected branch.1) branch.1.2.2.1,
  (boundary_valueMap (T.paid (C.selected branch.1))
   (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment).trans
   (congrArg (fun expression => expression.eval
    (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment)
    (cofinalRegisteredAtNext_source factory initial cfg language ordinal branch).1).symm⟩

theorem cofinal_registered_zero_iff (ordinal : Nat)
 (branch : C.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 F.paidCoordinate (E.transported (C.selected branch.1) branch.1.2.2.1) = 0 ↔
 (cofinalRegisteredAtNext factory initial cfg language ordinal branch).expression.eval
  (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment = 0 :=
 (E.registered_zero_iff (C.selected branch.1) branch.1.2.2.1).trans
  (congrArg (fun expression => expression.eval
   (B.born (C.selected branch.1) branch.1.2.2.1).activeEnvironment = 0)
   (cofinal_registered_expression factory initial cfg language ordinal branch)).symm.to_iff

end ActualCanonicalBornSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
