import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Received
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKPaCutoffCompressionSourceAction.Cofinal
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKWindowInverseResidualSourceAction.Consumer
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
open NoIslandNoMagic.CanonicalRiemann NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual BurnolPhysicalState
open scoped InnerProductSpace




open RootInquiryCompletion SourceOperationEffects SourceOperationExecution SourceOperationScalarInventoryLift CofinalHistorySettlement
open Filter
open scoped InnerProductSpace Topology

/-- A fixed physical source observer pays its own bounded action cost. -/
def windowPriceAction (radius : ℝ) : BurnolL2 →L[ℂ] BurnolPaAmbientCarrier :=
 burnolEvenAmbientProjection.comp ((burnolRadiusZeroExtension radius).comp (burnolSourceOnlyCoPoissonWindow radius))

local instance receiptConsumerGroups (grade : Nat) (target : Unit) :
 AddCommGroup (OriginalKFinitePaWindowOperatorSourceAction.L.Value (PairValue OriginalKFullSourceRAction.C.Value) grade target) :=
 OriginalKFinitePaWindowOperatorSourceAction.L.groups (PairValue OriginalKFullSourceRAction.C.Value) grade target
variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n:Nat,observation.coordinate=-2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat) (h H N : ℝ)

theorem actual_received_residual_strong_tendsto :
 Tendsto (fun n : Nat => OriginalKFullSourceRAction.originalField
  (R.actualReceivedResidual observation nontrivial half depth ordinal h H N (n+1:ℝ))) atTop (𝓝 0) := by
 have generated := actual_inverse_residual_strong_tendsto (materialAt observation nontrivial half depth ordinal h H N)
 apply generated.congr
 intro n
 have source := OriginalKWindowInverseResidualSourceAction.actual_received_residual_origin observation nontrivial half depth ordinal h H N (n+1:ℝ)
 have generatedSource := source_vector_receipt observation nontrivial half depth ordinal h H N
 exact (source.trans (congrArg (F.firstInverseResidual (n+1:ℝ)) generatedSource)).symm

theorem actual_fixed_window_residual_price_tendsto (radius : ℝ) (test : BurnolPaAmbientCarrier) :
 Tendsto (fun n : Nat => inner ℂ test (windowPriceAction radius
  (OriginalKFullSourceRAction.originalField
   (R.actualReceivedResidual observation nontrivial half depth ordinal h H N (n+1:ℝ))))) atTop (𝓝 0) := by
 have generated := (windowPriceAction radius).continuous.continuousAt.tendsto.comp
  (actual_received_residual_strong_tendsto observation nontrivial half depth ordinal h H N)
 have read := (innerSL ℂ test).continuous.continuousAt.tendsto.comp generated
 simpa only [Function.comp_def,innerSL_apply_apply,map_zero,inner_zero_right] using read

theorem actual_fixed_window_residual_price_cost (radius supportRadius : ℝ) (test : BurnolPaAmbientCarrier)
 (write : type_of% (OriginalKFinitePaWindowOperatorSourceAction.finite_stock_generated_source_delta
  (R.actualSourceFactory observation nontrivial half depth ordinal h)
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.1
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.2.down supportRadius
  (F.actualReceivedNu observation nontrivial half depth ordinal h H N)
  ((F.actualPreviousPacket observation nontrivial half depth ordinal h H N).2.2.2.down.symm ▸ ()))) :
 ‖inner ℂ test (windowPriceAction radius (OriginalKFullSourceRAction.originalField
  (R.actualReceivedResidual observation nontrivial half depth ordinal h H N supportRadius)))‖ ≤
 ‖test‖ * (‖windowPriceAction radius‖ * (‖burnolMobiusSourceL2‖ * ‖outsideTailAction supportRadius
  (actualPaField (materialAt observation nontrivial half depth ordinal h H N) : BurnolL2)‖)) := by
 exact (norm_inner_le_norm _ _).trans
  (mul_le_mul_of_nonneg_left ((windowPriceAction radius).le_opNorm _ |>.trans
   (mul_le_mul_of_nonneg_left (received_residual_source_cost _ _ _ _ _ _ _ _ _ write)
    (ContinuousLinearMap.opNorm_nonneg _))) (norm_nonneg test))


/-- The same two receipts now consume the operator law and its full residual cost. -/
theorem received_whole_inverse_source_cost (supportRadius : ℝ) (test : BurnolPaAmbientCarrier) :
 ∃ whole : type_of% (R.actualResidualWhole observation nontrivial half depth ordinal h H N supportRadius),
 (type_of% whole.actual_step) ∧ (type_of% whole.payment.strictDebit) ∧
 (type_of% whole.same_ledger) ∧ (type_of% whole.same_visit) ∧ (type_of% whole.entry) ∧
 (type_of% whole.whole_destination) ∧ (type_of% whole.source_environment) ∧ (type_of% whole.source_expression) ∧
 (type_of% (received_residual_source_cost observation nontrivial half depth ordinal h H N supportRadius
  (OriginalKFinitePaWindowOperatorSourceAction.finite_stock_generated_source_delta _ _ _ _ _ _ _ _))) ∧
 (type_of% (OriginalKWindowInverseResidualSourceAction.received_original_Pa_price
  (R.actualSourceFactory observation nontrivial half depth ordinal h)
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).1
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.1
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.2.1
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.2.2.down supportRadius
  (F.actualReceivedNu observation nontrivial half depth ordinal h H N)
  (R.actualReceivedResidual observation nontrivial half depth ordinal h H N supportRadius)
  ((R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.2.2.down.symm ▸ ()) test
  (OriginalKWindowInverseResidualSourceAction.residual_stock_generated_source_delta _ _ _ _ _ _ _ _ _))) ∧
 (type_of% (OriginalKWindowInverseResidualSourceAction.received_window_effect
  (R.actualSourceFactory observation nontrivial half depth ordinal h)
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).1
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.1
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.2.1
  (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.2.2.down supportRadius
  (F.actualReceivedNu observation nontrivial half depth ordinal h H N)
  (R.actualReceivedResidual observation nontrivial half depth ordinal h H N supportRadius)
  ((R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius).2.2.2.down.symm ▸ ())
  (OriginalKWindowInverseResidualSourceAction.receivedResidualWindowTrace _ _ _ _ _ _ _ _ _))) := by
 exact OriginalKFinitePaWindowOperatorSourceAction.consume_finite_source_receipt
  (R.actualSourceFactory observation nontrivial half depth ordinal h)
  (F.actualPreviousPacket observation nontrivial half depth ordinal h H N) supportRadius
  (F.actualReceivedNu observation nontrivial half depth ordinal h H N) fun _previous previousWrite _previousTrace =>
  OriginalKWindowInverseResidualSourceAction.consume_residual_source_receipt
   (R.actualSourceFactory observation nontrivial half depth ordinal h) supportRadius
   (F.actualReceivedNu observation nontrivial half depth ordinal h H N)
   (R.actualReceivedResidual observation nontrivial half depth ordinal h H N supportRadius)
   (R.actualSourcePacket observation nontrivial half depth ordinal h H N supportRadius) fun whole write trace =>
    ⟨whole,whole.actual_step,whole.payment.strictDebit,whole.same_ledger,whole.same_visit,whole.entry,
    whole.whole_destination,whole.source_environment,whole.source_expression,
    received_residual_source_cost _ _ _ _ _ _ _ _ _ previousWrite,
    OriginalKWindowInverseResidualSourceAction.received_original_Pa_price _ _ _ _ _ _ _ _ _ test write,
    OriginalKWindowInverseResidualSourceAction.received_window_effect _ _ _ _ _ _ _ _ _ trace⟩

end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKPaCutoffCompressionSourceAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
