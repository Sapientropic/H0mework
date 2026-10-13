import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Bindings
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceReturn.Consumer
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
namespace C
export OriginalKFiniteWard.C (Value Var)
end C
namespace Prior
export OriginalKCombCofinalTwoDirection (coordinate coordinate_value originalK originalFourierK sourceShift actionCode directions totalBranches action_code_directions)
end Prior
namespace Return
export OriginalKSourceReturn (sourceInput returnedOriginalK updatedOriginalK source_return_corrected_field
  source_return_original_K source_return_actual_increment source_return_original_K_price source_return_original_FourierK_price)
end Return
namespace Source
export OriginalKSourceBalance (correctedField regularSource contactCorrection)
end Source
abbrev Branches := (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)

def physicalPacking : BurnolL2 →L[ℂ] Branches :=
  ((ContinuousLinearMap.id ℂ BurnolL2).prod 0).prod 0
def pairedPacking : BurnolL2 →L[ℂ] Branches :=
  ((ContinuousLinearMap.id ℂ BurnolL2).prod fourierL2.toLinearIsometry.toContinuousLinearMap).prod 0
def positiveDirection : Branches →L[ℂ] BurnolL2 :=
  (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _) +
    (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)
def negativeDirection : Branches →L[ℂ] BurnolL2 :=
  (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _) +
    (ContinuousLinearMap.snd ℂ _ _).comp (ContinuousLinearMap.snd ℂ _ _)

-- Each original signed source direction is read through its own inverse unitary action.
def returnDirectionRead : Branches →L[ℂ] Branches :=
  (((burnolMultiplicativeDilation (-Prior.sourceShift)).toLinearIsometry.toContinuousLinearMap.comp positiveDirection).prod
    (fourierL2.toLinearIsometry.toContinuousLinearMap.comp
      ((burnolMultiplicativeDilation Prior.sourceShift).toLinearIsometry.toContinuousLinearMap.comp negativeDirection))).prod 0

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

def correctedCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .const (physicalPacking (Source.correctedField (Prior.coordinate observation nontrivial half)))
def regularCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .const (physicalPacking (Source.regularSource (Prior.coordinate observation nontrivial half)))
def inputCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .add (.linear (s := ()) (t := ())
      (((star observation.coordinate - observation.coordinate) / 2) • ContinuousLinearMap.id ℂ Branches).toLinearMap.toAddMonoidHom
      (correctedCode observation nontrivial half))
    (.linear (s := ()) (t := ()) ((-(1 / 2 : ℂ)) • ContinuousLinearMap.id ℂ Branches).toLinearMap.toAddMonoidHom
      (regularCode observation nontrivial half))
def inputValue : Branches := physicalPacking (Return.sourceInput observation nontrivial half)

theorem input_code_source (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (inputCode observation nontrivial half).eval environment = inputValue observation nontrivial half := by
  change (((star observation.coordinate - observation.coordinate) / 2) •
      physicalPacking (Source.correctedField (Prior.coordinate observation nontrivial half)) +
    (-(1 / 2 : ℂ)) • physicalPacking (Source.regularSource (Prior.coordinate observation nontrivial half))) = _
  rw [← map_smul, ← map_smul, ← map_add]
  change physicalPacking (_ + _) = physicalPacking (_ - _)
  rw [neg_smul]
  exact congrArg physicalPacking (sub_eq_add_neg _ _).symm

def contactCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .const (pairedPacking (Source.contactCorrection (Prior.coordinate observation nontrivial half)))
def returnCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .add (.linear (s := ()) (t := ()) returnDirectionRead.toLinearMap.toAddMonoidHom
      (Prior.actionCode observation nontrivial half))
    (.linear (s := ()) (t := ()) (-ContinuousLinearMap.id ℂ Branches).toLinearMap.toAddMonoidHom
      (contactCode observation nontrivial half))

theorem return_code_source (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (returnCode observation nontrivial half).eval environment =
      pairedPacking (OriginalKCombPhysicalAction.R observation nontrivial half
        (Prior.totalBranches (environment () ())) - Source.contactCorrection (Prior.coordinate observation nontrivial half)) := by
  have calculation : (returnCode observation nontrivial half).eval environment =
      returnDirectionRead ((Prior.actionCode observation nontrivial half).eval environment) -
        pairedPacking (Source.contactCorrection (Prior.coordinate observation nontrivial half)) := by
    change _ + -_ = _ - _
    exact (sub_eq_add_neg _ _).symm
  rw [calculation]
  have action : returnDirectionRead ((Prior.actionCode observation nontrivial half).eval environment) =
      pairedPacking (OriginalKCombPhysicalAction.R observation nontrivial half (Prior.totalBranches (environment () ()))) := by
    change ((burnolMultiplicativeDilation (-Prior.sourceShift)
        (Prior.directions ((Prior.actionCode observation nontrivial half).eval environment)).1,
      fourierL2 (burnolMultiplicativeDilation Prior.sourceShift
        (Prior.directions ((Prior.actionCode observation nontrivial half).eval environment)).2)), 0) = _
    rw [Prior.action_code_directions]
    simp only [burnolMultiplicativeDilation_add, neg_add_cancel, add_neg_cancel, burnolMultiplicativeDilation_zero]
    rfl
  rw [action, ← map_sub]

theorem return_code_initial (environment : Env (PairValue (PairValue C.Value)) C.Var)
    (source : environment () () = inputValue observation nontrivial half) :
    (returnCode observation nontrivial half).eval environment = pairedPacking (Prior.originalK observation nontrivial half) := by
  rw [return_code_source, source]
  have total : Prior.totalBranches (inputValue observation nontrivial half) = Return.sourceInput observation nontrivial half := by
    simp [inputValue, physicalPacking, Prior.totalBranches]
  rw [total]
  change pairedPacking (Return.returnedOriginalK observation nontrivial half) = _
  rw [Return.source_return_original_K]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKNativeSourceReturn
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
