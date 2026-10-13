import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Force
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace N
export RootGeneratedDebtActivationJointSource.Native.ResidualRequest (input)
end N
local instance gramSourceGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

-- The actual force birth is the parent; Gram reads its variables before the next emitter.
def gramFactory := AI.withActualInput (gramCode observation nontrivial half) (D.factory observation nontrivial half)
abbrev gramParent (ordinal : Nat) := forceBorn observation nontrivial half depth ordinal
abbrev gramIncoming (ordinal : Nat) := AS.nativeAfterAdmission (gramFactory observation nontrivial half)
  (gramParent observation nontrivial half depth ordinal)
def gramPacket (ordinal : Nat) : AS.AdmissionPacket (W := PairValue C.Value) (X := C.Var) (s := ()) :=
  AS.bornAfterNative (gramIncoming observation nontrivial half depth ordinal)
abbrev configuration (ordinal : Nat) := (gramPacket observation nontrivial half depth ordinal).2.2.1
abbrev material (ordinal : Nat) := R.actualMaterial (gramPacket observation nontrivial half depth ordinal).2.1.1
  (configuration observation nontrivial half depth ordinal)
abbrev receipt (ordinal : Nat) := R.actionResultAt (gramPacket observation nontrivial half depth ordinal).2.1.1
  (configuration observation nontrivial half depth ordinal)
  (S.actualOccurrence (gramPacket observation nontrivial half depth ordinal).2.1.1)

def actualEnvironment (ordinal : Nat) : Env (PairValue (PairValue C.Value)) C.Var :=
  fun target name => CF.collapseValue (gramPacket observation nontrivial half depth ordinal).1
    ((gramPacket observation nontrivial half depth ordinal).2.1.1.activeEnvironment target name, 0)

theorem actual_admitted_input (ordinal : Nat) :
    AI.HasActualInput (gramCode observation nontrivial half)
      (gramPacket observation nontrivial half depth ordinal).1
      (gramPacket observation nontrivial half depth ordinal).2.2.1
      (gramPacket observation nontrivial half depth ordinal).2.2.2.down :=
  AI.born_after_native_input _ _ (AI.native_after_admission_input _ (D.factory observation nontrivial half) _)

theorem actual_admitted_value (ordinal : Nat) :
    CF.collapseValue (gramPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1 =
      (gramCode observation nontrivial half).eval (actualEnvironment observation nontrivial half depth ordinal) :=
  Paid.value_of_actual_input (gramCode observation nontrivial half) (gramPacket observation nontrivial half depth ordinal)
    (actual_admitted_input observation nontrivial half depth ordinal)

theorem actual_material_source_ast (ordinal : Nat) : type_of%
    (Paid.material_raw_at (gramCode observation nontrivial half)
      (gramPacket observation nontrivial half depth ordinal) (actual_admitted_input observation nontrivial half depth ordinal)) :=
  Paid.material_raw_at _ _ (actual_admitted_input observation nontrivial half depth ordinal)

attribute [irreducible] gramFactory gramPacket
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
