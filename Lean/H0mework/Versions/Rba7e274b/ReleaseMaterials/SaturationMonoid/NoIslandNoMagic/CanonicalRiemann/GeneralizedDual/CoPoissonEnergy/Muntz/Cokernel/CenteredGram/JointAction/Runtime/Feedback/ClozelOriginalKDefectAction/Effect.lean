import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDefectAction.Source
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
namespace A
export SourceOperationInquiry.Context.Faces.Execution.Activation (Programme)
end A
namespace AI
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActualInputCalculation
  (actual_environment)
end AI
namespace AS
export SourceOperationNative.Tree.Fold.Dependent.Branch.JointQuery.Actor.Operation.Query.Inventory.Observer.CurrentChild.Dynamic.Live.Native.Action.Coupled.Registry.Calculation.Common.Feedback.Continuation.Lower.SourceFamily.ActivationSource
  (stock_action_reader)
end AS
local instance effectGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target

namespace Projection
export OriginalKFiniteWardGram (collapseEnvironment code_effect_base)
end Projection

def oldEnvironment (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
    Env (PairValue (PairValue C.Value)) C.Var :=
  fun target name => CF.collapseValue packet.1 ((R.actualMaterial packet.2.1.1 packet.2.2.1).environment target
    (packet.2.2.2.down.symm ▸ name))

def incrementEnvironment (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ())) :
    Env (PairValue (PairValue C.Value)) C.Var :=
  fun target name => CF.collapseValue packet.1 ((R.actualMaterial packet.2.1.1 packet.2.2.1).increment target
    (packet.2.2.2.down.symm ▸ name))

private theorem material_environment_at (code : Expr (PairValue (PairValue C.Value)) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
    oldEnvironment packet = fun target name => CF.collapseValue packet.1 (packet.2.1.1.activeEnvironment target name, 0) := by
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
      ⟨C.Var, datum, inventory, pairInventory⟩
    let packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) := ⟨grade, packetData, cfg, ⟨rfl⟩⟩
    have raw := (AS.stock_action_reader packetData.1 cfg (Root.actualOccurrence packetData.1)).symm.trans
      (generated packetData.1 (Root.actualOccurrence packetData.1))
    have environment := congrArg (fun sourceRaw => sourceRaw.environment) raw
    have actual := environment.trans (congrArg (fun sourceEnv => pairEnvironment sourceEnv
      (0 : Env (L.Value (PairValue C.Value) grade) C.Var)) (AI.actual_environment grade packetData.1))
    exact congrArg (Projection.collapseEnvironment grade) actual

private theorem material_effect_at (code : Expr (PairValue (PairValue C.Value)) C.Var ())
    (packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()))
    (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
    CF.collapseValue packet.1 ((R.actualMaterial packet.2.1.1 packet.2.2.1).raw.effect
      (R.actualMaterial packet.2.1.1 packet.2.2.1).environment
      (R.actualMaterial packet.2.1.1 packet.2.2.1).increment) =
    code.effect (oldEnvironment packet) (incrementEnvironment packet) := by
  rcases packet with ⟨grade, packetData, programme, ⟨sameVar⟩⟩
  cases programme with
  | mk lowVar datum inventory pairInventory =>
    change lowVar = C.Var at sameVar
    cases sameVar
    let cfg : A.Programme (PhysicalValue := L.Value (PairValue C.Value) grade) (PhysicalVar := C.Var) (sort := ()) :=
      ⟨C.Var, datum, inventory, pairInventory⟩
    let packet : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) := ⟨grade, packetData, cfg, ⟨rfl⟩⟩
    have raw := eq_of_heq (Paid.material_raw_at code packet generated)
    exact (congrArg (fun expression : Expr (PairValue (L.Value (PairValue C.Value) grade)) C.Var () =>
      CF.collapseValue grade (expression.effect (R.actualMaterial packetData.1 cfg).environment
        (R.actualMaterial packetData.1 cfg).increment)) raw).trans (Projection.code_effect_base code grade _ _)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

theorem actual_material_environment (ordinal : Nat) :
    oldEnvironment (defectPacket observation nontrivial half depth ordinal) = actualEnvironment observation nontrivial half depth ordinal :=
  material_environment_at _ _ (actual_admitted_input observation nontrivial half depth ordinal)

theorem actual_material_source_effect (ordinal : Nat) : type_of%
    (material_effect_at (sourceCode (RSource.coordinate observation nontrivial half)) (defectPacket observation nontrivial half depth ordinal)
      (actual_admitted_input observation nontrivial half depth ordinal)) :=
  material_effect_at _ _ (actual_admitted_input observation nontrivial half depth ordinal)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
