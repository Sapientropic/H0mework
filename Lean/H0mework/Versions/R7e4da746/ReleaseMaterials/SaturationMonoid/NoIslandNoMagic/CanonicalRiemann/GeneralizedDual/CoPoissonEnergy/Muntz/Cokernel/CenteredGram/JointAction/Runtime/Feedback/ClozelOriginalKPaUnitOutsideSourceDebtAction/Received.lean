import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Effect
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaUnitOutsideSourceDebtAction.Debt
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
open Complex BurnolPhysicalState
open scoped InnerProductSpace Topology
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual
local instance receivedSuccessorGroups (grade : Nat) (target : Unit) :
 AddCommGroup (L.Value (PairValue C.Value) grade target) := L.groups (PairValue C.Value) grade target
variable (source : Branches) (shift : ℝ)
variable (producer : SF.Factory (PairValue C.Value) C.Var ()) (grade : Nat)
variable (data : SF.Packet (W:=PairValue C.Value) (X:=C.Var) (s:=()) grade)
variable (sourceCfg : A.Programme (PhysicalValue:=L.Value (PairValue C.Value) grade) (PhysicalVar:=C.Var) (sort:=()))
variable (language : sourceCfg.LowVar=C.Var)

def receivedOwnIncrement : Branches := CF.collapseValue (grade+1)
 ((stockMaterial source shift producer grade data sourceCfg language).raw.effect
  (stockMaterial source shift producer grade data sourceCfg language).environment
  (stockMaterial source shift producer grade data sourceCfg language).increment)-
 inheritedSourceIncrement source shift producer grade data sourceCfg language (language.symm ▸ ())

def receivedSourceSplit : Branches := receivedOwnIncrement source shift producer grade data sourceCfg language+splitAction 0 source

def bornWrittenStock : Branches := CF.collapseValue grade
 ((stockBorn source shift producer grade data sourceCfg language).activeEnvironment () (language.symm ▸ ()))
def inheritedWrittenStock : Branches := CF.collapseValue grade
 (updatedSourceTotal source shift (splitFactory producer) grade data sourceCfg language)
def writtenSourceSplit : Branches := bornWrittenStock source shift producer grade data sourceCfg language-
 inheritedWrittenStock source shift producer grade data sourceCfg language+splitAction 0 source

theorem received_source_split
 (effect : type_of% (actual_material_stock_effect source shift producer grade data sourceCfg language)) :
 receivedSourceSplit source shift producer grade data sourceCfg language=splitAction shift source := by
 unfold receivedSourceSplit receivedOwnIncrement
 rw [effect]
 abel

theorem received_born_current_source
 (write : type_of% (actual_born_split_increment source shift (splitFactory producer) grade data sourceCfg language (language.symm ▸ ())))
 (effect : type_of% (actual_material_stock_effect source shift producer grade data sourceCfg language)) :
 bornWrittenStock source shift producer grade data sourceCfg language=
 inheritedWrittenStock source shift producer grade data sourceCfg language+receivedOwnIncrement source shift producer grade data sourceCfg language := by
 unfold receivedOwnIncrement
 rw [effect]
 change bornWrittenStock source shift producer grade data sourceCfg language-inheritedWrittenStock source shift producer grade data sourceCfg language=
 splitAction shift source-splitAction 0 source at write
 linear_combination (norm:=module) write

theorem received_write_source_split
 (write : type_of% (actual_born_split_increment source shift (splitFactory producer) grade data sourceCfg language (language.symm ▸ ())))
 (effect : type_of% (actual_material_stock_effect source shift producer grade data sourceCfg language)) :
 writtenSourceSplit source shift producer grade data sourceCfg language=receivedSourceSplit source shift producer grade data sourceCfg language := by
 unfold writtenSourceSplit receivedSourceSplit
 rw [received_born_current_source source shift producer grade data sourceCfg language write effect]
 abel

/-- The actual new write retains its inherited debt, while its recovered source split has the exact finite unitary budget. -/
theorem received_full_source_budget
 (write : type_of% (actual_born_split_increment source shift (splitFactory producer) grade data sourceCfg language (language.symm ▸ ())))
 (effect : type_of% (actual_material_stock_effect source shift producer grade data sourceCfg language)) :
 fullSplitBudget (writtenSourceSplit source shift producer grade data sourceCfg language)=fullSplitBudget (splitAction 0 source) := by
 rw [received_write_source_split source shift producer grade data sourceCfg language write effect,
  received_source_split source shift producer grade data sourceCfg language effect]
 exact source_split_finite_budget source shift

theorem received_actual_material_trace_effect :
 (stockMaterial source shift producer grade data sourceCfg language).raw.eval
  ((stockMaterial source shift producer grade data sourceCfg language).environment+
   (stockMaterial source shift producer grade data sourceCfg language).increment)=
 (stockMaterial source shift producer grade data sourceCfg language).state.1.eval
  (stockMaterial source shift producer grade data sourceCfg language).environment+
 (stockMaterial source shift producer grade data sourceCfg language).raw.effect
  (stockMaterial source shift producer grade data sourceCfg language).environment
  (stockMaterial source shift producer grade data sourceCfg language).increment := by
 have sound := (stockMaterial source shift producer grade data sourceCfg language).state.2.sound
 rw [Expr.eval_update]
 exact congrArg (fun value => value+
  (stockMaterial source shift producer grade data sourceCfg language).raw.effect
   (stockMaterial source shift producer grade data sourceCfg language).environment
   (stockMaterial source shift producer grade data sourceCfg language).increment) sound

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaUnitOutsideSourceDebtAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
