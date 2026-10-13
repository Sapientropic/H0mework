import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDefectAction.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalTwoDirection.Consumer
import H0mework.Versions.Rba7e274b.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.CoPoisson.Source.Mobius.Window.Action.ShiftedCorrection.TwoWindow.CommonInverse.InverseEuler.SourceJoint.FullStock.NativeRead

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
open Complex MeasureTheory
open scoped InnerProductSpace
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
open BurnolPhysicalState
namespace Prior
export OriginalKDefectAction (Branches defectFactory defectPacket actualWriteRead actual_native_physical_field
 inheritedIncrement actualDelta actualEnvironment actual_admitted_input actual_admitted_value actual_material_source_ast)
end Prior
namespace OldR
export OriginalKCombCofinalTwoDirection (fourTerms four_terms_eq_action translatedCorrection translatedUnit translatedShell translatedInvisible)
end OldR
namespace Op
export OriginalKCombPhysicalAction (R)
end Op
namespace C
export OriginalKDefectAction.C (Value Var)
end C

def originalField : Prior.Branches →L[ℂ] BurnolL2:=
  (ContinuousLinearMap.fst ℂ _ _).comp (ContinuousLinearMap.fst ℂ _ _)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

/-- The original R acts on the complete variable current. Each previous
physical/defect branch remains available to its inherited receipt inventory. -/
def variableAction : Prior.Branches →L[ℂ] Prior.Branches:=
  (Op.R observation nontrivial half).prod (FiniteMobiusResolventFlux.D.comp (Op.R observation nontrivial half)) |>.comp originalField |>.prod
    ((fourierL2.toLinearIsometry.toContinuousLinearMap.comp (Op.R observation nontrivial half)).prod
      (fourierL2.toLinearIsometry.toContinuousLinearMap.comp (FiniteMobiusResolventFlux.D.comp (Op.R observation nontrivial half))) |>.comp originalField)

/-- Every Pa, unit, signed-shell and invisible term belongs to the original
R action on this variable field; it is not a new D-stream membership. -/
theorem complete_four_term_source (shift : ℝ) (value : Prior.Branches) :
    OldR.fourTerms observation nontrivial half shift (originalField value)=
      burnolMultiplicativeDilation shift (variableAction observation nontrivial half value).1.1 := by
  exact OldR.four_terms_eq_action observation nontrivial half shift (originalField value)

theorem variable_action_defect (value : Prior.Branches) :
    (variableAction observation nontrivial half value).1.2=
      FiniteMobiusResolventFlux.D ((variableAction observation nontrivial half value).1.1) := rfl

def sourceCode : Expr (PairValue (PairValue C.Value)) C.Var ():=
  .linear (s:=()) (t:=()) (variableAction observation nontrivial half).toLinearMap.toAddMonoidHom (.var ())

theorem source_code_read (environment : Env (PairValue (PairValue C.Value)) C.Var) :
    (sourceCode observation nontrivial half).eval environment=
      variableAction observation nontrivial half (environment () ()) := rfl

theorem source_code_effect (environment increment : Env (PairValue (PairValue C.Value)) C.Var) :
    (sourceCode observation nontrivial half).effect environment increment=
      variableAction observation nontrivial half (increment () ()) := by
  have actual:=Expr.eval_update (sourceCode observation nontrivial half) environment increment
  rw [source_code_read,source_code_read] at actual
  change variableAction observation nontrivial half (environment () ()+increment () ())=_ at actual
  rw [map_add] at actual
  exact add_left_cancel actual.symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKFullSourceRAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
