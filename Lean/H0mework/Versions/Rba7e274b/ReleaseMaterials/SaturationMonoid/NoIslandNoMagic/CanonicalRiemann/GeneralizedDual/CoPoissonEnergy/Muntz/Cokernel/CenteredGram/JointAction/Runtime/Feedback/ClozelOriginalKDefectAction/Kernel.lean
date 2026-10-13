import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteReaction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ResolventFlux.RankedForcing
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
open Complex MeasureTheory
open scoped InnerProductSpace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace C
export OriginalKFiniteReaction.C (Value Var)
end C
namespace Prior
export OriginalKFiniteReaction (Branches reactionFactory reactionPacket actualWrite actualWriteRead actual_reaction_write
  actual_native_finite_reaction actualDelta returnedField returned_field_source finiteFields reaction_source)
end Prior
namespace RSource
export OriginalKFiniteReaction.RSource (coordinate coordinate_value originalK originalFourierK sourceShift)
end RSource
namespace Math
export FiniteMobiusResolventFlux (D rankedSourceDefect rankedForcing original_defect_ranked actual_defect_update)
end Math
abbrev Branches := Prior.Branches

def firstField : Branches →L[ℂ] BurnolL2 := (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)
def fieldRead : Branches →L[ℂ] BurnolL2 :=
  (burnolMultiplicativeDilation (-RSource.sourceShift)).toLinearIsometry.toContinuousLinearMap.comp firstField

-- The actual finite reaction source is removed before the same column is inverted.
def sourceField (coordinate : BurnolCompletedMellinCoordinate) (value : Branches) : BurnolL2 :=
  fieldRead (value-Prior.reaction_source coordinate RSource.sourceShift)

def actionFields : BurnolL2 →L[ℂ] Branches :=
  ((ContinuousLinearMap.id ℂ BurnolL2).prod Math.D).prod
  (fourierL2.toLinearIsometry.toContinuousLinearMap.prod
    (fourierL2.toLinearIsometry.toContinuousLinearMap.comp Math.D))

-- The programme acts on the current field; the original fixed source provides the rank forcing.
def sourceCode (coordinate : BurnolCompletedMellinCoordinate) : Expr (PairValue (PairValue C.Value)) C.Var () :=
  .linear (s := ()) (t := ()) (actionFields.comp fieldRead).toLinearMap.toAddMonoidHom
    (.add (.var ()) (.const (-Prior.reaction_source coordinate RSource.sourceShift)))

theorem source_code_read (coordinate : BurnolCompletedMellinCoordinate)
    (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (sourceCode coordinate).eval environment=actionFields (sourceField coordinate (environment () ())) := by
  change actionFields (fieldRead (environment () ()+ -Prior.reaction_source coordinate RSource.sourceShift))=_
  rw [← sub_eq_add_neg]
  rfl

theorem source_code_effect (coordinate : BurnolCompletedMellinCoordinate)
    (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (sourceCode coordinate).effect environment increment=actionFields (fieldRead (increment () ())) := by
  have source := Expr.eval_update (sourceCode coordinate) environment increment
  rw [source_code_read,source_code_read] at source
  unfold sourceField at source
  change actionFields (fieldRead (environment () ()+increment () ()-Prior.reaction_source coordinate RSource.sourceShift))=_ at source
  have sourceSplit : environment () ()+increment () ()-Prior.reaction_source coordinate RSource.sourceShift=
      (environment () ()-Prior.reaction_source coordinate RSource.sourceShift)+increment () () := by abel
  rw [sourceSplit,map_add,map_add] at source
  exact add_left_cancel source.symm

theorem finite_fields_read (value : BurnolL2) : fieldRead (Prior.finiteFields RSource.sourceShift value)=value := by
  unfold fieldRead firstField Prior.finiteFields
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
    LinearIsometry.coe_toContinuousLinearMap,LinearIsometryEquiv.coe_toLinearIsometry]
  change burnolMultiplicativeDilation (-RSource.sourceShift) (burnolMultiplicativeDilation RSource.sourceShift value)=value
  rw [burnolMultiplicativeDilation_add,neg_add_cancel,burnolMultiplicativeDilation_zero]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

def inheritedIncrement (ordinal : Nat) : BurnolL2 :=
  OriginalKCombPhysicalAction.R observation nontrivial half
    (OriginalKNativeSourceReturn.actualDelta observation nontrivial half depth ordinal)+
    Prior.actualDelta observation nontrivial half depth ordinal

theorem actual_parent_field (ordinal : Nat) :
    sourceField (RSource.coordinate observation nontrivial half) (Prior.actualWriteRead observation nontrivial half depth ordinal)=
    RSource.originalK observation nontrivial half+inheritedIncrement observation nontrivial half depth ordinal := by
  rw [Prior.actual_native_finite_reaction]
  unfold sourceField
  rw [add_sub_cancel_right,finite_fields_read,Prior.returned_field_source]
  unfold inheritedIncrement
  abel

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDefectAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
