import H0mework.Versions.Rdf421ff6.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.Terminal.Query

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.ResidualAction
open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift
open SourceOperationScalarRelations SourceOperationScalarPresentation
open CofinalFaithfulRealization.RootGeneratedCofinalFaithfulRealizationAt
namespace J
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint
 (disposition queryRaw queryReader queryResult)
end J
namespace Request
export SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request
 (occurrenceRaw occurrenceExecuted actualMaterial occurrence_value terminal_effect terminal_inverse)
end Request
namespace Owner
export RootGeneratedDebtActivationJointSource.OwnerFree.Installation (source_value)
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer (target_expression value_source)
end Owner
local instance actionGroups (grade : Nat) : ∀ target, AddCommGroup (L.Value (PairValue C.Value) grade target) :=
 L.groups (PairValue C.Value) grade

variable (native : NativeSigma.NativePacket)
abbrev frame := native.2.1.1
abbrev seed := native.2.1.2
def query := J.queryReader (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native))
def request := Request.occurrenceRaw (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native))
def executed := Request.occurrenceExecuted (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native))
def material := Request.actualMaterial (seed native) (frame native)
def effect := effectEvaluator (R:=ℤ) (material native).environment (material native).increment
 (relationMap (R:=ℤ) (material native).environment
  (SourceOperationInquiry.Context.Faces.Execution.Activation.InventoryProgramme.Pair.Residual.Joint.Past.NextObservation.Request.R.relations (R:=ℤ) (material native)))

theorem executed_effect : (executed native).2.2.1=effect native :=
 (Request.occurrence_value (seed native) (frame native)).trans
  (Request.terminal_effect (seed native) (frame native))

theorem executed_full_inverse : type_of% (Request.terminal_inverse (seed native) (frame native)) :=
 Request.terminal_inverse (seed native) (frame native)

private theorem request_difference : (request native).expression.eval (request native).environment =
 (query native).expression.eval (request native).environment -
 (query native).expression.eval (query native).environment := by
 let old := (SourceOperationInquiry.Context.Faces.Execution.Mother.baseState (A.epoch (frame native))).root.toAuthoritativeRoot
 have endpoint := Owner.target_expression old (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit (frame native)).current
  (fun _ => query native)
 change (Expr.add (query native).expression (Expr.linear (-AddMonoidHom.id _)
  (J.queryResult (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native))).2.1.1)).eval _ = _
 change (Expr.add (query native).expression (Expr.linear (-AddMonoidHom.id _)
  (RootGeneratedDebtActivationJointSource.OwnerFree.Consumer.targetState old
   (SourceOperationInquiry.Context.Faces.Execution.Activation.Shared.actualVisit (frame native)).current (fun _ => query native)).1)).eval _ = _
 rw [endpoint]
 simp only [Expr.eval,AddMonoidHom.neg_apply,AddMonoidHom.id_apply,sub_eq_add_neg]
 exact congrArg ((query native).expression.eval (request native).environment + ·)
  (congrArg Neg.neg (Owner.value_source old _ (fun _ => query native)))

private theorem unsound_query (obstruction : GeneratedUnsoundRelationObstructionAt (Terminal.WB.nativeFace native))
 (coordinate : GeneratedRelationResidualCoordinateAt (Terminal.WB.nativeFace native))
 (selected : J.disposition (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native)) =
  .unsound obstruction coordinate) :
 (query native).expression=Coefficients.expression coordinate.relation ∧
 (query native).expression.eval (query native).environment=coordinate.coordinate := by
 have selectedQuery : query native=Terminal.nativeQuery native (.unsound obstruction coordinate) := by
  change J.queryRaw _ _ _ (J.disposition _ _ _) = _
  rw [selected]
  rfl
 rw [selectedQuery]
 constructor
 · rfl
 · change (Coefficients.expression coordinate.relation).eval _=coordinate.coordinate
   exact (Coefficients.expression_eval coordinate.relation _).trans
    ((Terminal.Joint.query_word_read (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native))
     coordinate.relation).symm.trans coordinate.coordinate_eq.symm)

private theorem selected_execution
 (selected : ∃ (obstruction : GeneratedUnsoundRelationObstructionAt (Terminal.WB.nativeFace native))
  (coordinate : GeneratedRelationResidualCoordinateAt (Terminal.WB.nativeFace native)),
  J.disposition (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native)) = .unsound obstruction coordinate) :
 ∃ (obstruction : GeneratedUnsoundRelationObstructionAt (Terminal.WB.nativeFace native))
  (coordinate : GeneratedRelationResidualCoordinateAt (Terminal.WB.nativeFace native)),
  J.disposition (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native)) = .unsound obstruction coordinate ∧
  (query native).expression.eval (query native).environment=coordinate.coordinate ∧
  (executed native).2.2.1=(Coefficients.expression coordinate.relation).eval (request native).environment-coordinate.coordinate ∧
  (executed native).2.2.1=effect native := by
 obtain ⟨obstruction,coordinate,actual⟩:=selected
 have reads:=unsound_query native obstruction coordinate actual
 refine ⟨obstruction,coordinate,actual,reads.2,?_,executed_effect native⟩
 have generated:=Owner.source_value
  (SourceOperationInquiry.Context.Faces.Execution.Mother.baseState (A.epoch (frame native))).root.toAuthoritativeRoot
  (Request.occurrenceRaw (seed native) (A.epoch (frame native))) (S.actualOccurrence (frame native))
 exact generated.trans ((request_difference native).trans (by rw [reads.2,reads.1]))

private theorem transfer_phase (phase : ResidualDispositionOutcome (Terminal.WB.nativeFace native))
 (same : phase=J.disposition (seed native) (A.epoch (frame native)) (S.actualOccurrence (frame native)))
 (selected : ∃ (obstruction : GeneratedUnsoundRelationObstructionAt (Terminal.WB.nativeFace native))
  (coordinate : GeneratedRelationResidualCoordinateAt (Terminal.WB.nativeFace native)),phase=.unsound obstruction coordinate) :
 type_of% (selected_execution native (by
  obtain ⟨obstruction,coordinate,actual⟩:=selected
  exact ⟨obstruction,coordinate,same.symm.trans actual⟩)) :=
 selected_execution native (by
  obtain ⟨obstruction,coordinate,actual⟩:=selected
  exact ⟨obstruction,coordinate,same.symm.trans actual⟩)

end OriginalKCofinalFullBranchFibre.KernelWrite.NativeDelta.ResidualAction
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
