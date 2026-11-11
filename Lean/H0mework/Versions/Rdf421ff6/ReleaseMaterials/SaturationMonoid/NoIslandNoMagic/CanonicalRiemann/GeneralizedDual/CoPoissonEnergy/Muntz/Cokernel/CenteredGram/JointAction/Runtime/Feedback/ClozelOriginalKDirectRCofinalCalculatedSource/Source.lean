import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalMaterial.Whole

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalCalculatedSource
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open RootGeneratedDebtActivationJointSource.OwnerFree
open OriginalKDirectRCofinalMaterial

section LiteralSource
variable {W X : Unit→Type} [∀ target,AddCommGroup (W target)]
local instance sourceGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value W grade target) := L.groups W grade

private theorem packet_raw_source
 (code : Expr (PairValue W) X ())
 (packet : AS.AdmissionPacket (W:=W) (X:=X) (s:=()))
 (generated : AI.HasActualInput code packet.1 packet.2.2.1 packet.2.2.2.down) :
 HEq (R.actionReader packet.2.1.1 packet.2.2.1 (S.actualOccurrence packet.2.1.1)).expression
  (CF.codeAt code packet.1) ∧
 HEq (R.actionReader packet.2.1.1 packet.2.2.1 (S.actualOccurrence packet.2.1.1)).environment
  (pairEnvironment packet.2.1.1.activeEnvironment 0) := by
 rcases packet with ⟨grade,data,programme,⟨sameVar⟩⟩
 cases programme with
 | mk lowVar datum inventory pairInventory =>
  change lowVar=X at sameVar
  cases sameVar
  let cfg : A.Programme (PhysicalValue:=L.Value W grade) (PhysicalVar:=X) (sort:=()) :=
   ⟨X,datum,inventory,pairInventory⟩
  have actual := (AS.stock_action_reader data.1 cfg (S.actualOccurrence data.1)).symm.trans
   (generated data.1 (S.actualOccurrence data.1))
  have expression := congrArg (fun sourceRaw : Raw
   (Value:=PairValue (L.Value W grade)) (Var:=X) (sort:=()) => sourceRaw.expression) actual
  have environment := congrArg (fun sourceRaw : Raw
   (Value:=PairValue (L.Value W grade)) (Var:=X) (sort:=()) => sourceRaw.environment) actual
  have sourceEnvironment := environment.trans
   (congrArg (fun environment => pairEnvironment environment (0 : Env (L.Value W grade) X))
    (AI.actual_environment grade data.1))
  exact ⟨heq_of_eq expression,heq_of_eq sourceEnvironment⟩
end LiteralSource

local instance originalSourceGroups (grade : Nat) : ∀ target,AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

abbrev calculationRoot :=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.baseRoot
  (D.packet observation nontrivial half depth ordinal).2.1.1
  (D.packet observation nontrivial half depth ordinal).2.2.1).toAuthoritativeRoot
abbrev calculationCurrent :=
 (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.visit
  (D.packet observation nontrivial half depth ordinal).2.1.1
  (D.packet observation nontrivial half depth ordinal).2.2.1).current

def calculationReader :=
 fun (_ : (calculationRoot observation nontrivial half depth ordinal).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt
  (calculationCurrent observation nontrivial half depth ordinal)) =>
 R.actionReader (D.packet observation nontrivial half depth ordinal).2.1.1
  (D.packet observation nontrivial half depth ordinal).2.2.1
  (S.actualOccurrence (D.packet observation nontrivial half depth ordinal).2.1.1)

abbrev originalFrontier := Calculation.frontier
 (calculationRoot observation nontrivial half depth ordinal)
 (calculationCurrent observation nontrivial half depth ordinal)
 (calculationReader observation nontrivial half depth ordinal)
abbrev originalRealization := Calculation.realization
 (calculationRoot observation nontrivial half depth ordinal)
 (calculationCurrent observation nontrivial half depth ordinal)
 (calculationReader observation nontrivial half depth ordinal)
abbrev originalNormal := Calculation.normal
 (calculationRoot observation nontrivial half depth ordinal)
 (calculationCurrent observation nontrivial half depth ordinal)
 (calculationReader observation nontrivial half depth ordinal)
abbrev calculatedState := runtimeCurrent
 (calculationRoot observation nontrivial half depth ordinal)
 (calculationCurrent observation nontrivial half depth ordinal)
 (calculationReader observation nontrivial half depth ordinal)
 (originalNormal observation nontrivial half depth ordinal).targetRuntime
abbrev calculatedValue := (Calculation.completed
 (calculationRoot observation nontrivial half depth ordinal)
 (calculationCurrent observation nontrivial half depth ordinal)
 (calculationReader observation nontrivial half depth ordinal)).1

/-- This is the exact original occurrence reader supplied to the already paid frontier. -/
theorem source_payload_reader :
 (originalFrontier observation nontrivial half depth ordinal).sourcePayload =
 R.actionReader (D.packet observation nontrivial half depth ordinal).2.1.1
  (D.packet observation nontrivial half depth ordinal).2.2.1
  (S.actualOccurrence (D.packet observation nontrivial half depth ordinal).2.1.1) := rfl

/-- Raw AST and complete actual environment are retained before any target projection is taken. -/
theorem source_payload_literal :
 let packet:=D.packet observation nontrivial half depth ordinal
 HEq (originalFrontier observation nontrivial half depth ordinal).sourcePayload.expression
  (CF.codeAt (FR.jointCode (P.code observation nontrivial half)) packet.1) ∧
 HEq (originalFrontier observation nontrivial half depth ordinal).sourcePayload.environment
  (pairEnvironment packet.2.1.1.activeEnvironment 0) := by
 rw [source_payload_reader]
 exact packet_raw_source (FR.jointCode (P.code observation nontrivial half))
  (D.packet observation nontrivial half depth ordinal)
  (AI.cofinal_actual_input (FR.jointCode (P.code observation nontrivial half))
   (SF.defaultFactory (PairValue C.Value) C.Var ())
   (D.initial observation nontrivial half depth) (D.firstCfg observation nontrivial half depth) rfl ordinal)

/-- The material's entire typed paid state is this normal target, by the original resultAt call. -/
theorem actual_material_calculated_state :
 let packet:=D.packet observation nontrivial half depth ordinal
 (R.actualMaterial packet.2.1.1 packet.2.2.1).state =
 calculatedState observation nontrivial half depth ordinal := rfl

/-- Equality retains the complete dependent paid history, not merely its length. -/
theorem actual_material_calculated_history :
 let packet:=D.packet observation nontrivial half depth ordinal
 (R.actualMaterial packet.2.1.1 packet.2.2.1).state.2 =
 (calculatedState observation nontrivial half depth ordinal).2 := rfl

theorem actual_material_source_payload :
 let packet:=D.packet observation nontrivial half depth ordinal
 (R.actualMaterial packet.2.1.1 packet.2.2.1).raw =
  (originalFrontier observation nontrivial half depth ordinal).sourcePayload.expression ∧
 (R.actualMaterial packet.2.1.1 packet.2.2.1).environment =
  (originalFrontier observation nontrivial half depth ordinal).sourcePayload.environment := ⟨rfl,rfl⟩

/-- Each existing local operation is consumed at its exact generated full-history stage. -/
theorem original_source_operation
 (stage : Fin ((originalFrontier observation nontrivial half depth ordinal).stageCount+1)) :
 (originalFrontier observation nontrivial half depth ordinal).LocalOperationAt stage
  (originalFrontier observation nontrivial half depth ordinal).sourcePayload
  ((originalFrontier observation nontrivial half depth ordinal).history.stageAt stage) :=
 (originalRealization observation nontrivial half depth ordinal).operationAt stage

theorem actual_material_full_history_target :
 let packet:=D.packet observation nontrivial half depth ordinal
 (R.actualMaterial packet.2.1.1 packet.2.2.1).state = runtimeCurrent
  (calculationRoot observation nontrivial half depth ordinal)
  (calculationCurrent observation nontrivial half depth ordinal)
  (calculationReader observation nontrivial half depth ordinal)
  (originalFrontier observation nontrivial half depth ordinal).history.target := rfl

theorem actual_old_paid_calculated_value :
 let packet:=D.packet observation nontrivial half depth ordinal
 WB.oldPaid packet.2.1.1 packet.2.2.1=calculatedValue observation nontrivial half depth ordinal := rfl

theorem calculated_complete_target :
 (calculatedState observation nontrivial half depth ordinal).1 =
  .const (calculatedValue observation nontrivial half depth ordinal) :=
 Consumer.target_expression
  (calculationRoot observation nontrivial half depth ordinal)
  (calculationCurrent observation nontrivial half depth ordinal)
  (calculationReader observation nontrivial half depth ordinal)

theorem calculated_full_paid_history :
 (calculatedState observation nontrivial half depth ordinal).2.length =
 remaining (originalFrontier observation nontrivial half depth ordinal).sourcePayload.expression :=
 Calculation.completed_history
  (calculationRoot observation nontrivial half depth ordinal)
  (calculationCurrent observation nontrivial half depth ordinal)
  (calculationReader observation nontrivial half depth ordinal)

/-- The original local target remains the complete four-branch P.R calculation. -/
theorem calculated_full_R_branches :
 let packet:=D.packet observation nontrivial half depth ordinal
 CF.collapseValue packet.1 (calculatedValue observation nontrivial half depth ordinal)=
 Full.branches observation nontrivial half (D.input observation nontrivial half depth ordinal) := by
 rw [←actual_old_paid_calculated_value]
 exact actual_old_paid_branches observation nontrivial half depth ordinal

theorem calculated_full_R_action :
 let packet:=D.packet observation nontrivial half depth ordinal
 let result:=CF.collapseValue packet.1 (calculatedValue observation nontrivial half depth ordinal)
 result.1.1+result.1.2=P.R observation nontrivial half (D.input observation nontrivial half depth ordinal).1 ∧
 result.2.1+result.2.2=P.R observation nontrivial half (D.input observation nontrivial half depth ordinal).2 ∧
 (result.1.1+result.1.2)+(result.2.1+result.2.2)=P.R observation nontrivial half (D.raw observation nontrivial half depth ordinal) := by
 rw [←actual_old_paid_calculated_value]
 exact actual_old_paid_R observation nontrivial half depth ordinal

/-- The mathematical R target reads the original macro successor's raw value without identifying their runtimes. -/
theorem calculated_target_raw_successor :
 let packet:=D.packet observation nontrivial half depth ordinal
 let result:=CF.collapseValue packet.1 (calculatedValue observation nontrivial half depth ordinal)
 (result.1.1+result.1.2)+(result.2.1+result.2.2)=D.raw observation nontrivial half depth (ordinal+1) :=
 (calculated_full_R_action observation nontrivial half depth ordinal).2.2.trans
  (D.raw_successor observation nontrivial half depth ordinal).symm

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalCalculatedSource
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
