import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Consumer
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Query.Occurrence
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Execution.Relations.History.Feed.Occurrence.Transport
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Inquiry.Cofinal.Native.Installed.Cofinal.Action.Source.Inventory
import Lean.LibrarySuggestions.Basic
run_cmd Lean.modifyEnv fun env => Lean.LibrarySuggestions.nameDenyListExt.addEntry env "FullActionQuery"
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxErrors 1
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery
open CenteredGram.IntegralGraphJointAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation CofinalHistorySettlement
attribute [local instance] baseGroups levelGroups
local notation "slot" => CompletedSourceRCalculation.Slot.branches
namespace G
export SourceInventoryExecutionFeed.AdmissionReceipt
 (GeneratorOccurrence generatorRequest generator_request_member literal_read)
end G
namespace Coeff
export SaturationMonoid.SourceOperationExecution.Coefficients
 (expression lifted_remaining cost)
end Coeff
variable (fac : ActualCofinalSourceAction.SF.Factory A.W A.X slot)
variable (packet : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
variable (relation : RelationAt packet)

/-- The source action lifts the original ordered coefficient AST literally. -/
def sourceExpression : Expr (Lower.Value A.W (packet.1 + 1)) packet.2.2.1.LowVar slot := by
 letI : ∀ target, AddCommGroup (Lower.Value A.W packet.1 target) :=
  BornRCanonicalMethodRuntime.levelGroups packet.1
 exact packet.2.2.2.down.symm ▸
  liftExpr (Value := Lower.Value A.W packet.1)
   (Coeff.expression (Value := Lower.Value A.W packet.1) relation.val)

theorem sourceExpression_event :
 ActualCofinalSourceAction.sourceLiftEvent packet
  (.generator (Coeff.expression relation.val)) = .generator (sourceExpression packet relation) := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 rfl

theorem sourceExpression_eval
 (environment : Env (Lower.Value A.W (packet.1 + 1)) packet.2.2.1.LowVar) :
 (sourceExpression packet relation).eval environment =
 evaluation (R := ℤ) environment (Cfa.sourceWordAction packet relation.val) := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 exact G.literal_read relation.val environment

theorem sourceExpression_cost : remaining (sourceExpression packet relation) = Coeff.cost relation.val := by
 rcases packet with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 exact Coeff.lifted_remaining relation.val

variable (original : G.GeneratorOccurrence relation.inventory)
variable (code : original.expression = Coeff.expression relation.val)

/-- The existing source block transports the exact slot, preserving duplicate positions. -/
def sourceOccurrence : G.GeneratorOccurrence
 (AS.stockScalar (Cfa.selected fac packet) (Cfa.nativePacket fac packet).2.2.1) := by
 let block := ActualNativeRelationTransport.SourceInventoryBlock.source
  fac packet relation.inventory relation.installed
 refine ⟨block.before ++ original.before.map (ActualCofinalSourceAction.sourceLiftEvent packet),
  sourceExpression packet relation,
  original.after.map (ActualCofinalSourceAction.sourceLiftEvent packet) ++ block.after, ?_⟩
 have mapped : relation.inventory.trace.map (ActualCofinalSourceAction.sourceLiftEvent packet) =
   original.before.map (ActualCofinalSourceAction.sourceLiftEvent packet) ++
    PresentedRelationEventAt.generator (sourceExpression packet relation) ::
     original.after.map (ActualCofinalSourceAction.sourceLiftEvent packet) := by
  rw [original.trace_eq, List.map_append, List.map_cons, code, sourceExpression_event]
 exact block.trace_eq.trans
  ((congrArg (fun middle => block.before ++ middle ++ block.after) mapped).trans
   (by simp only [List.cons_append, List.append_assoc]))

abbrev request := G.generatorRequest (sourceOccurrence fac packet relation original code)

theorem request_member : request fac packet relation original code ∈
 SourceInventoryExecutionFeed.requests
  (AS.stockScalar (Cfa.selected fac packet) (Cfa.nativePacket fac packet).2.2.1) :=
 G.generator_request_member (sourceOccurrence fac packet relation original code)

theorem request_position : (request fac packet relation original code).position =
 (ActualNativeRelationTransport.SourceInventoryBlock.source
  fac packet relation.inventory relation.installed).before.length + original.before.length := by
 change (_ ++ original.before.map (ActualCofinalSourceAction.sourceLiftEvent packet)).length = _
 simp only [List.length_append, List.length_map]

/-- This is the actual source decoder consumed by the original Feed. -/
def environment : Env (Lower.Value A.W (packet.1 + 1)) packet.2.2.1.LowVar :=
 ActualNativeRelationTransport.AS.stockDecodedEnvironment
 (Cfa.selected fac packet) (Cfa.nativePacket fac packet).2.2.1

theorem environment_source : environment fac packet =
 (S.nextBorn (Cfa.selected fac packet) (AS.stockCfg (Cfa.nativePacket fac packet).2.2.1)).activeEnvironment :=
 (ActualNativeRelationTransport.decoded_environment _ _).symm

/-- The admitted Feed request supplies its own receipt. -/
def receipt := SourceInventoryExecutionFeed.receipt (environment fac packet)
 (request fac packet relation original code)

theorem receipt_cost : (receipt fac packet relation original code).length = Coeff.cost relation.val :=
 (SourceInventoryExecutionFeed.receipt_cost (environment fac packet)
  (request fac packet relation original code)).trans (sourceExpression_cost packet relation)

def kappa : Lower.Value A.W (packet.1 + 1) slot →₀ ℤ :=
 valueMap (R := ℤ) (Value := Lower.Value A.W (packet.1 + 1)) (Var := packet.2.2.1.LowVar)
  (environment fac packet) (Cfa.sourceWordAction packet relation.val)

/-- The independent free-word readout consumes the full affine action and actual decoder. -/
theorem value_kappa : (sourceExpression packet relation).eval (environment fac packet) =
 ScalarRelationPresentation.freeEvaluation (R := ℤ) (Lower.Value A.W (packet.1 + 1) slot)
  (kappa fac packet relation) :=
 (sourceExpression_eval packet relation (environment fac packet)).trans
  (LinearMap.congr_fun (valueMap_evaluation (R := ℤ) (s := slot) (environment fac packet))
   (Cfa.sourceWordAction packet relation.val)).symm

/-- Every event of this exact executed query is in the original next born inventory. -/
theorem receipt_written : ∀ event ∈ (P.exposure (receipt fac packet relation original code)).trace,
 event ∈ (AN.bornStock (Cfa.selected fac packet) (Cfa.nativePacket fac packet).2.2.1).trace :=
 ActualNativeRelationTransport.source_execution_written
  (Cfa.selected fac packet) (Cfa.nativePacket fac packet).2.2.1
  (request fac packet relation original code) (request_member fac packet relation original code)

open private castStock castWord bornGrade from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Feedback.Source
open private source from
 H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCountedPaSource.Initial.BornRWordPaWriteback.Readback

private def castGenerator {m n : Nat} (same : m = n)
 (stock : SourceInventoryExecutionFeed.Inventory (V := Lower.Value A.W m) (X := A.X) (s := slot))
 (point : G.GeneratorOccurrence stock) : G.GeneratorOccurrence (castStock same stock) := by
 cases same
 exact point

private theorem castGenerator_code {m n : Nat} (same : m = n)
 (stock : SourceInventoryExecutionFeed.Inventory (V := Lower.Value A.W m) (X := A.X) (s := slot))
 (point : G.GeneratorOccurrence stock) (word : Formal ℤ (Lower.Value A.W m) A.X slot)
 (literal : point.expression = Coeff.expression word) :
 (castGenerator same stock point).expression = Coeff.expression (castWord same word) := by
 cases same
 exact literal

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation)
local notation "factory" => A.fixedRFactory observation nontrivial half

/-- The original source generator is retained by its own born relation, before specialization. -/
noncomputable def bornCode
 (sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot))
 (relation : (actualBornHistory observation nontrivial half sourcePacket).relationClosure)
 (generated : HEq relation.val
  (A.nativeWordData observation nontrivial half sourcePacket.1 sourcePacket.2.1.1).gamma) :
 {point : G.GeneratorOccurrence
   (nativeRelation (AS.nativeAfterAdmission factory sourcePacket) relation).inventory //
  point.expression = Coeff.expression
   (nativeRelation (AS.nativeAfterAdmission factory sourcePacket) relation).val} := by
 rcases sourcePacket with ⟨n, ⟨frame, seed⟩, ⟨Y, datum, scalar, pair⟩, ⟨language⟩⟩
 cases language
 let sourcePacket : AS.AdmissionPacket (W := A.W) (X := A.X) (s := slot) :=
  ⟨n, ⟨frame, seed⟩, ⟨A.X, datum, scalar, pair⟩, ⟨rfl⟩⟩
 let native := AS.nativeAfterAdmission factory sourcePacket
 let point := CoefficientOccurrence.bornOccurrence observation nontrivial half sourcePacket
 have literal : point.expression = Coeff.expression relation.val := by
  have generated := CoefficientOccurrence.bornOccurrence_expression observation nontrivial half sourcePacket
  have originalWord := eq_of_heq ‹HEq relation.val
   (A.nativeWordData observation nontrivial half n frame).gamma›
  exact generated.trans (congrArg Coeff.expression originalWord.symm)
 refine ⟨castGenerator (bornGrade native).symm _ point, ?_⟩
 exact castGenerator_code (bornGrade native).symm _ point relation.val literal

variable (depth ordinal update cutoff : Nat)
local notation "actualPacket" => currentPacket observation nontrivial half depth ordinal update cutoff
local notation "gamma" => currentRelation observation nontrivial half depth ordinal update cutoff

noncomputable def actualCode :
 {point : G.GeneratorOccurrence (gamma).inventory // point.expression = Coeff.expression (gamma).val} := by
 unfold currentRelation currentPacket
 exact bornCode observation nontrivial half (source observation nontrivial half depth ordinal update cutoff)
  (actualBornRelation observation nontrivial half depth ordinal update cutoff).1
  ((actualBornRelation observation nontrivial half depth ordinal update cutoff).2.trans
   (heq_of_eq (actual_gamma_source observation nontrivial half depth ordinal update cutoff)))

noncomputable def actualRequest := request factory actualPacket gamma
 (actualCode observation nontrivial half depth ordinal update cutoff).val
 (actualCode observation nontrivial half depth ordinal update cutoff).property

noncomputable def actualReceipt := receipt factory actualPacket gamma
 (actualCode observation nontrivial half depth ordinal update cutoff).val
 (actualCode observation nontrivial half depth ordinal update cutoff).property

end CountedPaInitial.BornRWordPaWriteback.RelationFeedback.FullActionQuery
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
