import H0mework.Versions.X.Fock.HistoryConditional.FiniteObservationMinimumStable

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObservationMinimum

open SourceCopyProgram (Index)
open SourceCopyTemporalBoundary (recordedPrefix)
open SourceGeneratedAcquisitionContinuation SourceGeneratedActionObservationHistory
open NoIslandNoMagic.CanonicalArithmeticState.ParticleWaveFockRuntime
noncomputable section

theorem capacity (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat)
    (advance : PrefixCarrier SourceJointClockGraph.Carrier length → PrefixCarrier SourceJointClockGraph.Carrier length)
    (law : ∀ value : SourceJointClockGraph.Carrier,
      advance (recordedPrefix runtime index steps length value) =
        recordedPrefix runtime index steps length (SourceJointClockGraph.action value)) :
    SourceCopyRecordedRecurrence.cutoff runtime index steps + 3 ≤ (length + 1) * (inventoryBound runtime + steps + 1) := by
  have size := LinearMap.finrank_le_finrank_of_injective
    (samples_injective_of_update runtime index steps length advance law)
  simpa only [SourceCopyCurrentCoordinates.Coordinates, Module.finrank_prod, Module.finrank_fin_fun,
    Module.finrank_self, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one, Nat.add_assoc] using size

theorem no_short_update (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime)) (steps length : Nat)
    (shorter : length < index.val + 1) :
    ¬ ∃ advance : PrefixCarrier SourceJointClockGraph.Carrier length → PrefixCarrier SourceJointClockGraph.Carrier length,
      ∀ value : SourceJointClockGraph.Carrier,
        advance (recordedPrefix runtime index steps length value) =
          recordedPrefix runtime index steps length (SourceJointClockGraph.action value) := by
  rintro ⟨advance, law⟩
  have size := capacity runtime index steps length advance law
  have bound := Nat.mul_le_mul_right (inventoryBound runtime + steps + 1) (show length + 1 ≤ index.val + 1 by omega)
  have source := SourceCopyProgram.index_exact (inventoryBound runtime) index (inventoryBound runtime + steps)
  rw [SourceCopyProgram.scale_source] at source
  change SourceCopyRecordedRecurrence.cutoff runtime index steps + 1 =
    (inventoryBound runtime + steps + 1) * (index.val + 1) at source
  rw [Nat.mul_comm (inventoryBound runtime + steps + 1)] at source
  omega

theorem least_window (runtime : LivingRuntimeState process) (index : Index (inventoryBound runtime))
    (nonunit : index.val ≠ 0) (steps : Nat) :
    IsLeast {length : Nat | ∃ advance : PrefixCarrier SourceJointClockGraph.Carrier length → PrefixCarrier SourceJointClockGraph.Carrier length,
      ∀ value : SourceJointClockGraph.Carrier,
        advance (recordedPrefix runtime index steps length value) =
          recordedPrefix runtime index steps length (SourceJointClockGraph.action value)} (index.val + 1) := by
  constructor
  · exact ⟨SourceOperatorObservationAcquisition.next runtime index nonunit steps,
      SourceOperatorObservationAcquisition.next_source runtime index nonunit steps⟩
  · intro length admitted
    exact le_of_not_gt (fun shorter => no_short_update runtime index steps length shorter admitted)

end
end SourceFiniteObservationMinimum
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
