import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteWard.Kernel
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
open Complex MeasureTheory
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace C
export OriginalKCombReceiptFeedback (Value Var)
end C
namespace Profile
export OriginalRieszFiniteSource (profileIntegral fourierProfileIntegral)
end Profile
namespace Trace
export OriginalRieszSource.Kernel (A beta)
end Trace
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

def scaleBranches (coefficient : ℂ) : ((BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) →L[ℂ]
    ((BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) := coefficient • ContinuousLinearMap.id ℂ _

-- Primitive profile programmes and original trace coefficients enter before K-self is read.
def finiteForceCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .add
    (.linear (s := ()) (t := ()) (scaleBranches (Trace.A (Prior.coordinate observation nontrivial half))).toLinearMap.toAddMonoidHom
      (.const ((Profile.profileIntegral (Prior.coordinate observation nontrivial half) Prior.sourceShift, 0),
        (Profile.profileIntegral (Prior.coordinate observation nontrivial half) (-Prior.sourceShift), 0))))
    (.linear (s := ()) (t := ()) (scaleBranches (Trace.beta (Prior.coordinate observation nontrivial half))).toLinearMap.toAddMonoidHom
      (.const ((Profile.fourierProfileIntegral (Prior.coordinate observation nontrivial half) Prior.sourceShift, 0),
        (Profile.fourierProfileIntegral (Prior.coordinate observation nontrivial half) (-Prior.sourceShift), 0))))

theorem finite_force_code_owned (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (finiteForceCode observation nontrivial half).eval environment =
      (((installedOriginalKReceiptAt observation nontrivial half.down).forcing Prior.sourceShift, 0),
       ((installedOriginalKReceiptAt observation nontrivial half.down).forcing (-Prior.sourceShift), 0)) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals simp [finiteForceCode, Expr.eval, scaleBranches, installedOriginalKReceiptAt_eq_source,
    OriginalRieszFiniteSource.Receipt.generate, KSource.forcingIntegral] <;> rfl

def fullTotal : ((BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) →L[ℂ] BurnolL2 :=
  Prior.pairTotal.comp (ContinuousLinearMap.fst ℂ _ _ + ContinuousLinearMap.snd ℂ _ _)

def selfRead : ((BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) →L[ℂ]
    ((BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)) :=
  (((KRead observation nontrivial half).comp fullTotal).prod
    (((FourierKRead observation nontrivial half).comp
      fourierL2.toLinearIsometry.toContinuousLinearMap).comp fullTotal)).prod 0

def selfSourceCode : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .linear (s := ()) (t := ()) (selfRead observation nontrivial half).toLinearMap.toAddMonoidHom
    (finiteForceCode observation nontrivial half)

def finiteForcePair : BurnolL2 :=
  (installedOriginalKReceiptAt observation nontrivial half.down).forcing Prior.sourceShift +
    (installedOriginalKReceiptAt observation nontrivial half.down).forcing (-Prior.sourceShift)

def selfSourceValue : BurnolL2 × BurnolL2 :=
  (KRead observation nontrivial half (finiteForcePair observation nontrivial half),
   FourierKRead observation nontrivial half (fourierL2 (finiteForcePair observation nontrivial half)))

theorem self_source_code_owned (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (selfSourceCode observation nontrivial half).eval environment =
      (selfSourceValue observation nontrivial half, 0) := by
  change selfRead observation nontrivial half ((finiteForceCode observation nontrivial half).eval environment) = _
  rw [finite_force_code_owned]
  apply Prod.ext
  · apply Prod.ext
    · change KRead observation nontrivial half ((finiteForcePair observation nontrivial half) + (0 + 0)) = _
      simp only [add_zero]
      rfl
    · change FourierKRead observation nontrivial half
        (fourierL2 ((finiteForcePair observation nontrivial half) + (0 + 0))) = _
      simp only [add_zero]
      rfl
  · rfl

theorem self_source_directions (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    Prior.directions ((selfSourceCode observation nontrivial half).eval environment) =
      selfSourceValue observation nontrivial half := by
  rw [self_source_code_owned]
  change selfSourceValue observation nontrivial half + 0 = _
  exact add_zero _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
