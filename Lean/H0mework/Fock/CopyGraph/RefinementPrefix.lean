import H0mework.Fock.CopyGraph.RefinementRecovery
import H0mework.Fock.PrimeFieldCalculation.FixedMaterial

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceGraphRefinement

open SourceWeightedRecovery SourceGeneratedRuntimeHistoryProbability
open SourceCopyProgram (Index)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory SourcePrimeHistoryRecovery
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFock
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section
local instance prefixMeasurable (width : Nat) : MeasurableSpace (SourceFixedInventoryRecovery.Observation width) := ⊤

def prefixResidual (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (width : Nat) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  SourceConditionalGraphDecoder.residual (inventoryBound runtime) (inventoryBound runtime) index
    (SourceFixedInventoryRecovery.query runtime width)

def prefixGain (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (width : Nat) :
    SourceJointClockGraph.Carrier →L[ℂ] SourceJointClockGraph.Carrier :=
  gain (inventoryBound runtime) (inventoryBound runtime) index (SourceFixedInventoryRecovery.query runtime (width + 1))
    (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width)

theorem prefix_residual_update (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (width : Nat) (value : SourceJointClockGraph.Carrier) :
    prefixResidual runtime index width value = prefixResidual runtime index (width + 1) value + prefixGain runtime index width value := by
  have generated := residual_update (inventoryBound runtime) (inventoryBound runtime) index
    (SourceFixedInventoryRecovery.query runtime (width + 1)) (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width) value
  simpa only [prefixResidual, prefixGain, SourceFixedInventoryRecovery.restriction_query] using generated

theorem prefix_energy (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (width : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖prefixResidual runtime index width value‖ ^ 2 =
      ‖prefixResidual runtime index (width + 1) value‖ ^ 2 + ‖prefixGain runtime index width value‖ ^ 2 := by
  have generated := residual_energy (inventoryBound runtime) (inventoryBound runtime) index
    (SourceFixedInventoryRecovery.query runtime (width + 1)) (prefixRestriction (R := ℤ) (B := IntegralOneParticle) width) value
  simpa only [prefixResidual, prefixGain, SourceFixedInventoryRecovery.restriction_query] using generated

theorem prefix_antitone (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (value : SourceJointClockGraph.Carrier) : Antitone (fun width => ‖prefixResidual runtime index width value‖ ^ 2) := by
  apply antitone_nat_of_succ_le
  intro width
  rw [prefix_energy runtime index width value]
  exact le_add_of_nonneg_right (sq_nonneg ‖prefixGain runtime index width value‖)

theorem prefix_total (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (width : Nat) (value : SourceJointClockGraph.Carrier) :
    ‖prefixResidual runtime index 0 value‖ ^ 2 = ‖prefixResidual runtime index width value‖ ^ 2 +
      ∑ stage ∈ Finset.range width, ‖prefixGain runtime index stage value‖ ^ 2 := by
  induction width with
  | zero => simp
  | succ width previous =>
      rw [Finset.sum_range_succ, previous, prefix_energy runtime index width value]
      ring

end
end SourceGraphRefinement
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
