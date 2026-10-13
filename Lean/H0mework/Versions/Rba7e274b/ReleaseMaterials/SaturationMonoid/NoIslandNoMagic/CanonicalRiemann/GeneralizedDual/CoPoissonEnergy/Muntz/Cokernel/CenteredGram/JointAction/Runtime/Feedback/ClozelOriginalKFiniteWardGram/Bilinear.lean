import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWardGram.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace C
export OriginalKCombReceiptFeedback (Value Var)
end C
namespace Prior
export OriginalKCombCofinalTwoDirection (coordinate coordinate_value originalK originalFourierK sourceShift directions)
end Prior
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

abbrev Branches := (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)

def physicalDirections : Branches →L[ℂ] Branches :=
  (((ContinuousLinearMap.fst ℂ BurnolL2 BurnolL2).comp
       (ContinuousLinearMap.fst ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2) +
        ContinuousLinearMap.snd ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2))).prod
    (fourierL2.toLinearIsometry.toContinuousLinearMap.comp
      ((ContinuousLinearMap.snd ℂ BurnolL2 BurnolL2).comp
       (ContinuousLinearMap.fst ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2) +
        ContinuousLinearMap.snd ℂ (BurnolL2 × BurnolL2) (BurnolL2 × BurnolL2))))).prod 0

def background : Branches :=
  (((fullMellinTranslationCharacter (star observation.coordinate) Prior.sourceShift - 1) •
      Prior.originalK observation nontrivial half,
    (fullMellinTranslationCharacter (star observation.coordinate) (-Prior.sourceShift) - 1) •
      Prior.originalFourierK observation nontrivial half), 0)

def gramAction : Branches →+ Branches →+ Branches where
  toFun := fun left =>
    { toFun := fun right =>
        ((inner ℂ left.1.1 right.1.1 • Prior.originalK observation nontrivial half,
          inner ℂ left.1.2 right.1.2 • Prior.originalFourierK observation nontrivial half), 0)
      map_zero' := by simp
      map_add' := by intro right other; simp [inner_add_right, add_smul, Prod.mk_add_mk] }
  map_zero' := by
    apply AddMonoidHom.ext
    intro right
    simp
  map_add' := by
    intro left other
    apply AddMonoidHom.ext
    intro right
    simp [inner_add_left, add_smul, Prod.mk_add_mk]

def displacementCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .add (.linear (s := ()) (t := ()) physicalDirections.toLinearMap.toAddMonoidHom (.var (s := ()) ()))
    (.const (background observation nontrivial half))

def energyCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .bilinear (s := ()) (t := ()) (r := ()) (gramAction observation nontrivial half)
    (displacementCode observation nontrivial half) (displacementCode observation nontrivial half)

def unitKernel : Branches := ((Prior.originalK observation nontrivial half,
  Prior.originalFourierK observation nontrivial half), 0)

def swapBranches : Branches →L[ℂ] Branches :=
  (ContinuousLinearMap.snd ℂ _ _).prod (ContinuousLinearMap.fst ℂ _ _)

def unitCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .linear (s := ()) (t := ()) swapBranches.toLinearMap.toAddMonoidHom
    (.bilinear (s := ()) (t := ()) (r := ()) (gramAction observation nontrivial half)
      (.const (s := ()) (unitKernel observation nontrivial half)) (.const (s := ()) (unitKernel observation nontrivial half)))

def gramCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .add (energyCode observation nontrivial half) (unitCode observation nontrivial half)

theorem displacement_code_value (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (displacementCode observation nontrivial half).eval environment =
      physicalDirections (environment () ()) + background observation nontrivial half := rfl

theorem displacement_code_effect (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (displacementCode observation nontrivial half).effect environment increment =
      physicalDirections (increment () ()) := by
  change physicalDirections (increment () ()) + 0 = _
  exact add_zero _

theorem gram_code_value (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (gramCode observation nontrivial half).eval environment =
      gramAction observation nontrivial half
        ((displacementCode observation nontrivial half).eval environment)
        ((displacementCode observation nontrivial half).eval environment) +
      swapBranches (gramAction observation nontrivial half
        (unitKernel observation nontrivial half) (unitKernel observation nontrivial half)) := rfl

theorem unit_code_effect (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (unitCode observation nontrivial half).effect environment increment = 0 := by
  change swapBranches
    (gramAction observation nontrivial half (unitKernel observation nontrivial half) 0 +
      gramAction observation nontrivial half 0 (unitKernel observation nontrivial half) +
      gramAction observation nontrivial half 0 0) = 0
  simp

-- The two cross terms and joint action are generated by the actual variable programme.
theorem gram_code_effect (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (gramCode observation nontrivial half).effect environment increment =
      gramAction observation nontrivial half
        ((displacementCode observation nontrivial half).eval environment) (physicalDirections (increment () ())) +
      gramAction observation nontrivial half (physicalDirections (increment () ()))
        ((displacementCode observation nontrivial half).eval environment) +
      gramAction observation nontrivial half (physicalDirections (increment () ())) (physicalDirections (increment () ())) := by
  change (gramAction observation nontrivial half
      ((displacementCode observation nontrivial half).eval environment)
      ((displacementCode observation nontrivial half).effect environment increment) +
    gramAction observation nontrivial half
      ((displacementCode observation nontrivial half).effect environment increment)
      ((displacementCode observation nontrivial half).eval environment) +
    gramAction observation nontrivial half
      ((displacementCode observation nontrivial half).effect environment increment)
      ((displacementCode observation nontrivial half).effect environment increment)) +
      (unitCode observation nontrivial half).effect environment increment = _
  rw [unit_code_effect, add_zero, displacement_code_effect]

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWardGram
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
