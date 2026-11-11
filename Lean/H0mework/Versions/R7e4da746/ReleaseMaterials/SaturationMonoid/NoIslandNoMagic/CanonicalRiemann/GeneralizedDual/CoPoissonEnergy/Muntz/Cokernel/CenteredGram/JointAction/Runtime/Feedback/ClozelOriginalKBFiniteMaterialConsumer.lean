import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKBFiniteMaterialSemantics
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKSourceFiniteUpdate.BFiniteRGate
import H0mework.Versions.R7e4da746.Arithmetic.RiemannRuntime.PairedOmegaEffectRuntimeFacade

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKBFiniteCalculation.MaterialConsumer
open Complex BurnolPhysicalState SourceOperationExecution
open OriginalKSourceFiniteUpdate.OriginalBFiniteRAction
open OriginalKFixedBoundarySourceFibre
open scoped InnerProductSpace

private theorem fixed_nonnegative : 0 ≤ OriginalKBFiniteCalculation.fixedShift := by
  apply Real.log_nonneg
  norm_num [stageZeroSonineQ]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2 * (n + 1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)
local notation "c" => OriginalKCombCofinalTwoDirection.coordinate observation nontrivial half
local notation "h" => OriginalKBFiniteCalculation.fixedShift
local notation "material" => runtimeBFiniteCalculationResultAt observation nontrivial depth half
local notation "receipt" => installedOriginalKReceiptAt observation nontrivial half.down

/-- The installed source is the literal computation at this emitted occurrence. -/
theorem installed_source_raw :
    (material).1.environment = OriginalKBFiniteCalculation.sourceEnvironment ∧
    (material).1.expression = OriginalKBFiniteCalculation.code c h := by
  rw [runtimeBFiniteCalculationResultAt_source]
  exact ⟨rfl, rfl⟩

/-- The original B/R equation reads the paid value of the named installed face. -/
theorem installed_source_value :
    (material).2.2.1 = calculatedSourceNormal c h := by
  rw [runtimeBFiniteCalculationResultAt_source]
  exact (RootGeneratedDebtActivationJointSource.OwnerFree.Installation.source_value
    OriginalKBFiniteCalculation.Base
    (OriginalKBFiniteCalculation.reader observation nontrivial half)
    ((runtimeEffectRuntimeAt observation nontrivial depth).emittedOccurrence)).trans
      (Semantics.code_eval c h fixed_nonnegative)

theorem installed_source_complete_history :
    (material).2.1.2.length = remaining (OriginalKBFiniteCalculation.code c h) := by
  rw [runtimeBFiniteCalculationResultAt_source]
  exact OriginalKBFiniteCalculation.result_history observation nontrivial half _

/-- The source face, whole tick and actual receipt consume one generated value. -/
theorem installed_original_receipt_reads (ordinal : Nat) :
    type_of% (runtimeBFiniteCalculationReadoutAt_factorizes observation nontrivial depth half) ∧
    ((receipt).fixedResidual = -inner ℂ (receipt).kernel (material).2.2.1) ∧
    (((receipt).boundary h : BurnolL2) =
      (burnolEvenAmbientProjection (material).2.2.1 : BurnolL2)) ∧
    ((material).2.2.1 - ((receipt).boundary h : BurnolL2) = sourceProjectionLoss c h) ∧
    (‖(material).2.2.1‖^2 = ‖((receipt).boundary h : BurnolL2)‖^2 + ‖sourceProjectionLoss c h‖^2) := by
  have generated := actual_B_R_source_on_original_whole_next observation nontrivial half depth ordinal
  have price := generated.2.2.2.1
  have boundary := generated.2.2.2.2.1
  have loss := generated.2.2.2.2.2.1
  have energy := generated.2.2.2.2.2.2.1
  have value := installed_source_value observation nontrivial half depth
  change (material).2.2.1 = calculatedSourceNormal c (Real.log stageZeroSonineQ) at value
  rw [← value] at price boundary loss energy
  exact ⟨runtimeBFiniteCalculationReadoutAt_factorizes observation nontrivial depth half,
    price, boundary, loss, energy⟩

end OriginalKBFiniteCalculation.MaterialConsumer
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
end
