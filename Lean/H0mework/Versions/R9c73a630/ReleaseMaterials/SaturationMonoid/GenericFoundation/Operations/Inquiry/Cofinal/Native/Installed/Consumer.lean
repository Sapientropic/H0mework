import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Source
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Next.Consumer
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "ActualInstalledNativeRaw"
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace ActualInstalledNativeRaw
open RootInquiryCompletion SourceOperationEffects SourceOperationScalarRelations SourceOperationScalarPresentation
namespace C
export ActualCanonicalBornSource (registeredAtNext cofinal_registered_effect cofinal_registered_inverse cofinal_registered_affine cofinal_registered_zero_iff)
end C
variable {Sorts : Type u} {W X : Sorts → Type u} [∀ target, AddCommGroup (W target)] {s : Sorts}
local instance consumerGroups (grade : Nat) (target : Sorts) : AddCommGroup (L.Value W grade target) := L.groups W grade target
variable (factory : SF.Factory W X s)
variable (initial : M.Frame (Value := W) (Var := X) (sort := s))
variable (cfg : A.Programme (PhysicalValue := W) (PhysicalVar := X) (sort := s))
variable (language : cfg.LowVar = X)

theorem installed_request (start : Nat) (branch : N.NativeSegmentAt factory initial cfg language start) :
 (O.readRaw _ (rawAtNext factory initial cfg language start branch)).environment =
  (C.registeredAtNext factory initial cfg language start branch).environment ∧
 (O.readRaw _ (rawAtNext factory initial cfg language start branch)).expression =
  (C.registeredAtNext factory initial cfg language start branch).expression := by
 have raw := (rawAtNext_read factory initial cfg language start branch).trans
  (raw_registered (B.born (N.selected branch.1) branch.1.2.2.1))
 have generated := C.registeredAtNext_source factory initial cfg language start branch
 exact ⟨(congrArg (fun input => input.environment) raw).trans generated.2.symm,
  (congrArg (fun input => input.expression) raw).trans
   ((B.actual_born_registered_expression (N.selected branch.1) branch.1.2.2.1).trans generated.1.symm)⟩

def cofinalRaw (ordinal : Nat)
 (branch : N.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :=
 rawAtNext factory initial cfg language (D.index factory initial cfg language ordinal+1) branch

theorem installed_effect (ordinal : Nat)
 (branch : N.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 (O.readRaw _ (cofinalRaw factory initial cfg language ordinal branch)).expression.eval
  (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment =
 effectEvaluator (R := ℤ) (ActualNativeRelationTransport.paid (N.selected branch.1)).environment
  (ActualRegisteredBornEffect.delta (N.selected branch.1) branch.1.2.2.1)
  (SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace.boundary
   (ActualNativeRelationTransport.paid (N.selected branch.1))) :=
 (congrArg (fun expression => expression.eval
  (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment)
  (installed_request factory initial cfg language (D.index factory initial cfg language ordinal+1) branch).2).trans
  (C.cofinal_registered_effect factory initial cfg language ordinal branch)

namespace F
export SourceGeneratedInquiryReceiptAction.Configured.Writeback.Successor.FourFace (boundary effectFaces paidCoordinate)
end F
namespace E
export ActualRegisteredBornEffect (transported affineCertificate)
end E
namespace T
export ActualNativeRelationTransport (paid)
end T

theorem installed_inverse (ordinal : Nat)
 (branch : N.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 ((F.effectFaces (E.transported (N.selected branch.1) branch.1.2.2.1)).rangeEquiv
  (F.paidCoordinate (E.transported (N.selected branch.1) branch.1.2.2.1))).val =
 (O.readRaw _ (cofinalRaw factory initial cfg language ordinal branch)).expression.eval
  (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment :=
 (C.cofinal_registered_inverse factory initial cfg language ordinal branch).trans
  (congrArg (fun expression => expression.eval
   (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment)
   (installed_request factory initial cfg language (D.index factory initial cfg language ordinal+1) branch).2).symm

theorem installed_zero_iff (ordinal : Nat)
 (branch : N.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 F.paidCoordinate (E.transported (N.selected branch.1) branch.1.2.2.1) = 0 ↔
 (O.readRaw _ (cofinalRaw factory initial cfg language ordinal branch)).expression.eval
  (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment = 0 :=
 (C.cofinal_registered_zero_iff factory initial cfg language ordinal branch).trans
  (congrArg (fun expression => expression.eval
   (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment = 0)
   (installed_request factory initial cfg language (D.index factory initial cfg language ordinal+1) branch).2).symm.to_iff

theorem installed_affine (ordinal : Nat)
 (branch : N.NativeSegmentAt factory initial cfg language (D.index factory initial cfg language ordinal+1)) :
 relationMap (R := ℤ) (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment
  (E.affineCertificate (N.selected branch.1) branch.1.2.2.1) =
 F.boundary (T.paid (N.selected branch.1)) - constantMap (R := ℤ)
  (valueMap (R := ℤ) (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment
   (F.boundary (T.paid (N.selected branch.1)))) ∧
 ScalarRelationPresentation.freeEvaluation (R := ℤ) (L.Value W branch.1.1 s)
  (valueMap (R := ℤ) (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment
   (F.boundary (T.paid (N.selected branch.1)))) =
 (O.readRaw _ (cofinalRaw factory initial cfg language ordinal branch)).expression.eval
  (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment :=
 let actual := C.cofinal_registered_affine factory initial cfg language ordinal branch
 ⟨actual.1,actual.2.trans
  (congrArg (fun expression => expression.eval
   (B.born (N.selected branch.1) branch.1.2.2.1).activeEnvironment)
   (installed_request factory initial cfg language (D.index factory initial cfg language ordinal+1) branch).2).symm⟩

end ActualInstalledNativeRaw
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
