import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Readback
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Effect
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
local instance actionGroups (grade : Nat) (target : Unit) : AddCommGroup (L.Value (PairValue C.Value) grade target) :=
  L.groups (PairValue C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def actualDelta (ordinal : Nat) : BurnolL2 :=
  Prior.totalBranches (incrementEnvironment (returnPacket observation nontrivial half depth ordinal) () ())
def actualReturnValue : Branches := pairedPacking (Prior.originalK observation nontrivial half)
def actualReturnEffect (ordinal : Nat) : Branches :=
  pairedPacking (OriginalKCombPhysicalAction.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal))

theorem return_code_effect_source
    (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (returnCode observation nontrivial half).effect environment increment =
      pairedPacking (OriginalKCombPhysicalAction.R observation nontrivial half (Prior.totalBranches (increment () ()))) := by
  have actual : (returnCode observation nontrivial half).effect environment increment =
      (returnCode observation nontrivial half).eval (environment + increment) -
        (returnCode observation nontrivial half).eval environment := by
    rw [Expr.eval_update]
    abel
  rw [actual, return_code_source, return_code_source, ← map_sub]
  have total : Prior.totalBranches ((environment + increment) () ()) =
      Prior.totalBranches (environment () ()) + Prior.totalBranches (increment () ()) :=
    OriginalKCombCofinalTwoDirection.totalBranches_add _ _
  rw [total, map_add]
  congr 1
  abel

theorem actual_complete_source_value (ordinal : Nat) :
    CF.collapseValue (returnPacket observation nontrivial half depth ordinal).1
      (receipt observation nontrivial half depth ordinal).2.2.1 = actualReturnValue observation nontrivial half := by
  rw [actual_admitted_value]
  exact return_code_initial observation nontrivial half _
    (actual_input_return_input observation nontrivial half depth ordinal)

theorem actual_complete_source_effect (ordinal : Nat) :
    CF.collapseValue (returnPacket observation nontrivial half depth ordinal).1
      ((material observation nontrivial half depth ordinal).raw.effect
        (material observation nontrivial half depth ordinal).environment
        (material observation nontrivial half depth ordinal).increment) = actualReturnEffect observation nontrivial half depth ordinal := by
  rw [actual_material_source_effect, return_code_effect_source]
  rfl

def actualUpdatedEnvironment (ordinal : Nat) : Env (PairValue (PairValue C.Value)) C.Var :=
  oldEnvironment (returnPacket observation nontrivial half depth ordinal) +
    incrementEnvironment (returnPacket observation nontrivial half depth ordinal)

theorem actual_updated_input (ordinal : Nat) :
    Prior.totalBranches (actualUpdatedEnvironment observation nontrivial half depth ordinal () ()) =
      Return.sourceInput observation nontrivial half + actualDelta observation nontrivial half depth ordinal := by
  have source := actual_input_return_input observation nontrivial half depth ordinal
  rw [actualUpdatedEnvironment, actual_material_environment]
  change Prior.totalBranches (actualEnvironment observation nontrivial half depth ordinal () () +
    incrementEnvironment (returnPacket observation nontrivial half depth ordinal) () ()) = _
  rw [OriginalKCombCofinalTwoDirection.totalBranches_add, source]
  have packed : Prior.totalBranches (inputValue observation nontrivial half) = Return.sourceInput observation nontrivial half := by
    simp [inputValue, physicalPacking, Prior.totalBranches]
  rw [packed]
  rfl

theorem actual_updated_source_return (ordinal : Nat) :
    (returnCode observation nontrivial half).eval (actualUpdatedEnvironment observation nontrivial half depth ordinal) =
      pairedPacking (Prior.originalK observation nontrivial half +
        OriginalKCombPhysicalAction.R observation nontrivial half (actualDelta observation nontrivial half depth ordinal)) := by
  rw [return_code_source, actual_updated_input]
  exact congrArg pairedPacking (Return.source_return_actual_increment observation nontrivial half _)

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
