import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKNativeSourceReturn.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.TruncatedFourier.Radius.Scaling.Variation.FiniteRank.PairPrice
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
open Complex MeasureTheory
open scoped InnerProductSpace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace Prior
export OriginalKNativeSourceReturn (Branches pairedPacking physicalPacking returnPacket returnFactory actualReturnWriteRead actual_native_source_return actualDelta)
end Prior
namespace RSource
export OriginalKCombCofinalTwoDirection (coordinate coordinate_value originalK originalFourierK sourceShift)
end RSource
namespace C
export OriginalKFiniteWard.C (Value Var)
end C
namespace F
export FixedWindowFourierReaction (H Q e quarterChart originalB originalW originalForcing gapTail originalShell actualRadius actualOverlap
  centeredOperator centeredSquare squareDifference finiteReaction mixedReactionPrice pairedShellPrice originalPairedPrice)
end F
abbrev Branches := Prior.Branches

def fieldReader : Branches →L[ℂ] BurnolL2 := (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)
def finiteFields (h : ℝ) : BurnolL2 →L[ℂ] Branches :=
  (((burnolMultiplicativeDilation h).toLinearIsometry.toContinuousLinearMap).prod
    (burnolMultiplicativeDilation (-h)).toLinearIsometry.toContinuousLinearMap).prod
  ((fourierL2.toLinearIsometry.toContinuousLinearMap.comp (burnolMultiplicativeDilation h).toLinearIsometry.toContinuousLinearMap).prod
    (fourierL2.toLinearIsometry.toContinuousLinearMap.comp (burnolMultiplicativeDilation (-h)).toLinearIsometry.toContinuousLinearMap))

def sourceEmbed : F.H →L[ℂ] BurnolL2 := burnolQuarterZeroExtension.comp F.quarterChart.symm.toContinuousLinearEquiv.toContinuousLinearMap

def reactionFields (h : ℝ) : F.H →L[ℂ] Branches :=
  ((sourceEmbed.comp (F.squareDifference (F.actualRadius h) (1/4))).prod
    (sourceEmbed.comp (F.squareDifference (F.actualRadius (-h)) (1/4)))).prod
  ((fourierL2.toLinearIsometry.toContinuousLinearMap.comp (sourceEmbed.comp (F.squareDifference (F.actualRadius h) (1/4)))).prod
    (fourierL2.toLinearIsometry.toContinuousLinearMap.comp (sourceEmbed.comp (F.squareDifference (F.actualRadius (-h)) (1/4)))))

def reaction_source (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : Branches :=
  ((sourceEmbed (F.finiteReaction (1/4) (F.actualRadius h) (F.originalB coordinate)),
    sourceEmbed (F.finiteReaction (1/4) (F.actualRadius (-h)) (F.originalB coordinate))),
   (fourierL2 (sourceEmbed (F.finiteReaction (1/4) (F.actualRadius h) (F.originalB coordinate))),
    fourierL2 (sourceEmbed (F.finiteReaction (1/4) (F.actualRadius (-h)) (F.originalB coordinate)))))

theorem reaction_fields_source (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) :
    reactionFields h (F.originalB coordinate) = reaction_source coordinate h := by
  unfold reactionFields reaction_source
  simp only [ContinuousLinearMap.prod_apply,ContinuousLinearMap.comp_apply]
  rw [FixedWindowFourierReaction.centered_square_finite (1/4) (F.actualRadius h) (by norm_num) (mul_pos (by norm_num) (Real.exp_pos _)),
    FixedWindowFourierReaction.centered_square_finite (1/4) (F.actualRadius (-h)) (by norm_num) (mul_pos (by norm_num) (Real.exp_pos _))]
  rfl

-- Original compact b and the actual returned physical field are distinct qualified sources.
def sourceCode (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ) : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .add (.linear (s := ()) (t := ()) ((finiteFields h).comp fieldReader).toLinearMap.toAddMonoidHom (.var ()))
    (.const (reactionFields h (F.originalB coordinate)))

theorem source_code_read (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (sourceCode coordinate h).eval environment = finiteFields h (fieldReader (environment () ()))+reaction_source coordinate h := by
  change finiteFields h (fieldReader (environment () ()))+reactionFields h (F.originalB coordinate)=_
  rw [reaction_fields_source]

theorem source_code_effect (coordinate : BurnolCompletedMellinCoordinate) (h : ℝ)
    (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (sourceCode coordinate h).effect environment increment = finiteFields h (fieldReader (increment () ())) := by
  have update := Expr.eval_update (sourceCode coordinate h) environment increment
  rw [source_code_read,source_code_read] at update
  change finiteFields h (fieldReader (environment () ()+increment () ()))+reaction_source coordinate h = _ at update
  rw [map_add,map_add] at update
  exact add_left_cancel (show
    finiteFields h (fieldReader (environment () ()))+reaction_source coordinate h+
      (sourceCode coordinate h).effect environment increment =
    finiteFields h (fieldReader (environment () ()))+reaction_source coordinate h+
      finiteFields h (fieldReader (increment () ())) by
    rw [← update]
    abel)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def returnedField (ordinal : Nat) : BurnolL2 := fieldReader (Prior.actualReturnWriteRead observation nontrivial half depth ordinal)
theorem returned_field_source (ordinal : Nat) : returnedField observation nontrivial half depth ordinal =
    RSource.originalK observation nontrivial half+OriginalKCombPhysicalAction.R observation nontrivial half
      (Prior.actualDelta observation nontrivial half depth ordinal) := by
  rw [returnedField,Prior.actual_native_source_return]
  rfl

theorem actual_returned_price (ordinal : Nat) :
    inner ℂ (RSource.originalK observation nontrivial half) (burnolMultiplicativeDilation RSource.sourceShift
      (returnedField observation nontrivial half depth ordinal))+
    inner ℂ (RSource.originalK observation nontrivial half) (burnolMultiplicativeDilation (-RSource.sourceShift)
      (returnedField observation nontrivial half depth ordinal)) =
    F.originalPairedPrice (RSource.coordinate observation nontrivial half) RSource.sourceShift
      (OriginalKCombPhysicalAction.R observation nontrivial half (Prior.actualDelta observation nontrivial half depth ordinal)) := by
  rw [returned_field_source]
  exact FixedWindowFourierReaction.original_paired_finite_price _ _ _

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFiniteReaction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
