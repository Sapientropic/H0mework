import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalTwoDirection.Consumer

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
open Complex MeasureTheory Set Filter
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Prior
export OriginalKCombCofinalTwoDirection (coordinate coordinate_value originalK originalFourierK sourceShift pairTotal totalBranches directions)
end Prior
namespace D
export OriginalKCombFirstFullSourceDynamics (factory initial firstCfg packet input raw raw_successor next_pair original_runtime_whole original_root_future)
end D
namespace P
export OriginalKCombPhysicalAction (R)
end P
namespace KSource
export OriginalRieszFiniteSource (forcingIntegral forcingIntegral_read original_finite_action)
end KSource

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)

-- Unitarity transfers the actual finite source; the fixed K is never differentiated.
theorem finite_K_weakWard (shift : ℝ) (value : BurnolL2) :
    inner ℂ (Prior.originalK observation nontrivial half) (burnolMultiplicativeDilation shift value) -
      star (fullMellinTranslationCharacter (star observation.coordinate) (-shift)) *
        inner ℂ (Prior.originalK observation nontrivial half) value =
      inner ℂ (KSource.forcingIntegral (Prior.coordinate observation nontrivial half) (-shift)) value := by
  have unitary := (burnolMultiplicativeDilation shift).inner_map_map
    (burnolMultiplicativeDilation (-shift) (Prior.originalK observation nontrivial half)) value
  rw [burnolMultiplicativeDilation_add, add_neg_cancel, burnolMultiplicativeDilation_zero] at unitary
  have action := KSource.original_finite_action (Prior.coordinate observation nontrivial half) (-shift)
  change burnolMultiplicativeDilation (-shift) (Prior.originalK observation nontrivial half) = _ at action
  have actual := congrArg (fun left : BurnolL2 => inner ℂ left value) action
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, Prior.coordinate_value] at actual
  rw [← unitary] at actual
  exact sub_eq_iff_eq_add.mpr (by rw [add_comm]; exact actual)

theorem finite_FourierK_weakWard (shift : ℝ) (value : BurnolL2) :
    inner ℂ (Prior.originalFourierK observation nontrivial half) (burnolMultiplicativeDilation shift value) -
      star (fullMellinTranslationCharacter (star observation.coordinate) shift) *
        inner ℂ (Prior.originalFourierK observation nontrivial half) value =
      inner ℂ (fourierL2 (KSource.forcingIntegral (Prior.coordinate observation nontrivial half) shift)) value := by
  have unitary := (burnolMultiplicativeDilation shift).inner_map_map
    (burnolMultiplicativeDilation (-shift) (Prior.originalFourierK observation nontrivial half)) value
  rw [burnolMultiplicativeDilation_add, add_neg_cancel, burnolMultiplicativeDilation_zero] at unitary
  have action := congrArg fourierL2 (KSource.original_finite_action (Prior.coordinate observation nontrivial half) shift)
  rw [fourierL2_burnolMultiplicativeDilation, map_add, map_smul] at action
  change burnolMultiplicativeDilation (-shift) (Prior.originalFourierK observation nontrivial half) = _ at action
  have actual := congrArg (fun left : BurnolL2 => inner ℂ left value) action
  simp only [inner_add_left, inner_smul_left, starRingEnd_apply, Prior.coordinate_value] at actual
  rw [← unitary] at actual
  exact sub_eq_iff_eq_add.mpr (by rw [add_comm]; exact actual)

def KRead : BurnolL2 →L[ℂ] BurnolL2 :=
  (innerSL ℂ (Prior.originalK observation nontrivial half)).smulRight (Prior.originalK observation nontrivial half)

def FourierKRead : BurnolL2 →L[ℂ] BurnolL2 :=
  (innerSL ℂ (Prior.originalFourierK observation nontrivial half)).smulRight (Prior.originalFourierK observation nontrivial half)

def directedRead : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((KRead observation nontrivial half).comp (ContinuousLinearMap.fst ℂ _ _)).prod
    ((FourierKRead observation nontrivial half).comp (ContinuousLinearMap.snd ℂ _ _))

def baseRead : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  ((KRead observation nontrivial half).comp Prior.pairTotal).prod
    ((FourierKRead observation nontrivial half).comp Prior.pairTotal)

def sourceCharacter : ℂ :=
  star (fullMellinTranslationCharacter (star observation.coordinate) (-Prior.sourceShift))

def finiteSource : BurnolL2 :=
  (installedOriginalKReceiptAt observation nontrivial half.down).forcing (-Prior.sourceShift)

theorem finite_source_owned : finiteSource observation nontrivial half =
    KSource.forcingIntegral (Prior.coordinate observation nontrivial half) (-Prior.sourceShift) := rfl

def sourceRead : (BurnolL2 × BurnolL2) →L[ℂ] (BurnolL2 × BurnolL2) :=
  (((innerSL ℂ (finiteSource observation nontrivial half)).smulRight
    (Prior.originalK observation nontrivial half)).comp Prior.pairTotal).prod
    (((innerSL ℂ (fourierL2 (finiteSource observation nontrivial half))).smulRight
      (Prior.originalFourierK observation nontrivial half)).comp Prior.pairTotal)

theorem directed_source_K (value : BurnolL2) :
    (KRead observation nontrivial half) (burnolMultiplicativeDilation Prior.sourceShift value) -
      sourceCharacter observation • (KRead observation nontrivial half) value =
    inner ℂ (finiteSource observation nontrivial half) value • (Prior.originalK observation nontrivial half) := by
  change inner ℂ (Prior.originalK observation nontrivial half) (burnolMultiplicativeDilation Prior.sourceShift value) • (Prior.originalK observation nontrivial half) -
    sourceCharacter observation • (inner ℂ (Prior.originalK observation nontrivial half) value • (Prior.originalK observation nontrivial half)) = _
  rw [smul_smul, ← sub_smul, finite_source_owned]
  exact congrArg (fun scalar : ℂ => scalar • (Prior.originalK observation nontrivial half))
    (finite_K_weakWard observation nontrivial half Prior.sourceShift value)

theorem directed_source_FourierK (value : BurnolL2) :
    (FourierKRead observation nontrivial half) (burnolMultiplicativeDilation (-Prior.sourceShift) value) -
      sourceCharacter observation • (FourierKRead observation nontrivial half) value =
    inner ℂ (fourierL2 (finiteSource observation nontrivial half)) value • (Prior.originalFourierK observation nontrivial half) := by
  change inner ℂ (Prior.originalFourierK observation nontrivial half) (burnolMultiplicativeDilation (-Prior.sourceShift) value) • (Prior.originalFourierK observation nontrivial half) -
    sourceCharacter observation • (inner ℂ (Prior.originalFourierK observation nontrivial half) value • (Prior.originalFourierK observation nontrivial half)) = _
  rw [smul_smul, ← sub_smul, finite_source_owned]
  exact congrArg (fun scalar : ℂ => scalar • (Prior.originalFourierK observation nontrivial half))
    (finite_FourierK_weakWard observation nontrivial half (-Prior.sourceShift) value)

-- The embedding price is retained; no inverse, normalization or physical margin is transferred.
theorem K_read_price (value : BurnolL2) :
    inner ℂ (Prior.originalK observation nontrivial half) (KRead observation nontrivial half value) =
      inner ℂ (Prior.originalK observation nontrivial half) value *
        inner ℂ (Prior.originalK observation nontrivial half) (Prior.originalK observation nontrivial half) :=
  inner_smul_right _ _ _

theorem FourierK_read_price (value : BurnolL2) :
    inner ℂ (Prior.originalFourierK observation nontrivial half) (FourierKRead observation nontrivial half value) =
      inner ℂ (Prior.originalFourierK observation nontrivial half) value *
        inner ℂ (Prior.originalFourierK observation nontrivial half) (Prior.originalFourierK observation nontrivial half) :=
  inner_smul_right _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteWard
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
