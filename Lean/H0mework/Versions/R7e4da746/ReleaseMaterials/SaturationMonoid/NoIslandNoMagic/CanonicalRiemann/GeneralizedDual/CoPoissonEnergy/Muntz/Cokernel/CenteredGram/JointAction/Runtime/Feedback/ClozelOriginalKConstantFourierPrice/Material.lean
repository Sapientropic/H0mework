import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Origin
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Arithmetic
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Material.Calculation.ClozelOriginalKConstantFourierPriceProgram

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option pp.deepTerms.threshold 24
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalConstantFourierPriceMaterial
open BurnolPhysicalState SourceOperationEffects SourceOperationExecution
open SourceOperationScalarInventoryLift SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
open OriginalKCofinalFullBranchFibre OriginalKCofinalFullBranchFibre.KernelWrite
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta
open OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder
namespace Root
export OriginalConstantFourierPriceOrigin (sourceRoot sourceVisit originFace currentHistory history_source seedValue seedTrace seed_actual seed_trace_source)
end Root
namespace A
export OriginalConstantFourierPriceArithmetic (actualTrace actualChild actualCursor actualOccurrence storedValue stored_child)
end A
namespace P
export OriginalConstantFourierPriceProgram (originalB originalSB)
end P
namespace Ext
export OriginalKExteriorArithmeticCalculation (columnCode sourceEnvironment fixedShift sourceAction)
end Ext
namespace C
export OriginalKCombReceiptFeedback (Value Var receipt)
end C
namespace WN
export OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.BetaDecoder.WordNative (native)
end WN
namespace Cut
export OriginalConstantFourierPriceCursor (path child_address)
end Cut
open private historyReceipt occurrence_receipt from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKConstantFourierPrice.Origin
open private mp_heq from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRSource
open private decodeMap from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKOutsideCorrectionRootSource
open private physicalValue from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaNativeCayleyNextSource
attribute [local instance] OriginalKPairedWaveRootSource.levelGroups
attribute [local irreducible] AS.nativeAfterAdmission physicalValue

private theorem column_closed (c:BurnolCompletedMellinCoordinate) (column:Fin 2) (environment:Env C.Value C.Var) :
    (Ext.columnCode c column).eval environment=(Ext.columnCode c column).eval Ext.sourceEnvironment := by
  fin_cases column <;> rfl

variable (observation:GeneratedRiemannZeroObservation)
variable (nontrivial:¬ ∃ n:Nat, observation.coordinate = -2*(n+1))
variable (half:OriginalKCombCalculation.Half observation) (depth ordinal:Nat) (t:ℝ) (column:Fin 2)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "native" => WN.native observation nontrivial half depth ordinal

/-- Select the exact original arithmetic occurrence in the history read from the current target face. -/
private noncomputable def columnReceipt := occurrence_receipt
  (historyReceipt observation nontrivial half depth ordinal t)
  (A.actualOccurrence observation nontrivial half depth column ordinal)
noncomputable def columnWord := (columnReceipt observation nontrivial half depth ordinal t column).val
theorem column_word_source : type_of% (columnReceipt observation nontrivial half depth ordinal t column).property :=
  (columnReceipt observation nontrivial half depth ordinal t column).property

noncomputable def columnValue : BurnolL2 := physicalValue (AS.bornAfterNative native).1
  (decodeMap (remaining (A.actualCursor observation nontrivial half depth column).beforeExpr) Cut.path
    (columnWord observation nontrivial half depth ordinal t column))
theorem column_value_source : columnValue observation nontrivial half depth ordinal t column=
    A.storedValue observation nontrivial half depth column ordinal :=
  congrArg (fun word=>physicalValue (AS.bornAfterNative native).1
    (decodeMap (remaining (A.actualCursor observation nontrivial half depth column).beforeExpr) Cut.path word))
      (column_word_source observation nontrivial half depth ordinal t column)
theorem column_value_child : columnValue observation nontrivial half depth ordinal t column=
    (A.actualChild observation nontrivial half depth column).value :=
  (column_value_source observation nontrivial half depth ordinal t column).trans
    (A.stored_child observation nontrivial half depth column ordinal)

noncomputable def columnTrace : Trace (C.receipt observation nontrivial depth half).1.environment
    (Ext.columnCode c column) (.const (columnValue observation nontrivial half depth ordinal t column)) :=
  Eq.mp (congrArg (fun value=>Trace (C.receipt observation nontrivial depth half).1.environment
    (Ext.columnCode c column) (.const value)) (column_value_child observation nontrivial half depth ordinal t column).symm)
      (A.actualChild observation nontrivial half depth column).trace
theorem column_trace_source : type_of% (mp_heq
    (congrArg (fun value=>Trace (C.receipt observation nontrivial depth half).1.environment
      (Ext.columnCode c column) (.const value)) (column_value_child observation nontrivial half depth ordinal t column).symm)
        (A.actualChild observation nontrivial half depth column).trace) := mp_heq _ _
theorem column_child_address : type_of% (Cut.child_address Ext.fixedShift (Ext.columnCode c column)
    (Ext.sourceAction depth 0).toLinearMap.toAddMonoidHom (A.actualTrace observation nontrivial half depth column)) :=
  Cut.child_address Ext.fixedShift (Ext.columnCode c column)
    (Ext.sourceAction depth 0).toLinearMap.toAddMonoidHom (A.actualTrace observation nontrivial half depth column)

theorem column_actual : columnValue observation nontrivial half depth ordinal t column=
    (Ext.columnCode c column).eval Ext.sourceEnvironment :=
  (columnTrace observation nontrivial half depth ordinal t column).sound.symm.trans
    (column_closed c column (C.receipt observation nontrivial depth half).1.environment)
noncomputable def bValue := columnValue observation nontrivial half depth ordinal t 0
noncomputable def sbValue := columnValue observation nontrivial half depth ordinal t 1
theorem b_actual : bValue observation nontrivial half depth ordinal t=P.originalB c :=
  column_actual observation nontrivial half depth ordinal t 0
theorem sb_actual : sbValue observation nontrivial half depth ordinal t=P.originalSB c :=
  column_actual observation nontrivial half depth ordinal t 1

end OriginalConstantFourierPriceMaterial
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "OriginalConstantFourierPriceMaterial"
