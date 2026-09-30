import H0mework.Computation.LoadedADCInformation.DistortionPhysical

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

noncomputable section

def futureRead (drive : FiniteBinaryDrive) : Nat → FiniteBinaryDrive :=
  fun future => (ConditionalAction.driveFlip^[future]) drive

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

def futureQuery (bound : Nat) (actor : Fin (bound + 1)) : Nat → FiniteBinaryDrive :=
  fun future => driveAt downstreamTechnology downstreamGraph seed (actor.val + future)

theorem future_query_factorizes (bound : Nat) (actor : Fin (bound + 1)) :
    futureQuery downstreamTechnology downstreamGraph seed bound actor =
      futureRead (query downstreamTechnology downstreamGraph seed bound actor) := by
  funext future
  change driveAt downstreamTechnology downstreamGraph seed (actor.val + future) =
    (ConditionalAction.driveFlip^[future]) (driveAt downstreamTechnology downstreamGraph seed actor.val)
  induction future with
  | zero => rfl
  | succ future previous =>
      rw [← Nat.add_assoc, driveAt_next, Function.iterate_succ_apply', ← previous]
      rfl

theorem future_query_fibre (bound : Nat) (left right : Fin (bound + 1)) :
    futureQuery downstreamTechnology downstreamGraph seed bound left =
        futureQuery downstreamTechnology downstreamGraph seed bound right ↔
      query downstreamTechnology downstreamGraph seed bound left = query downstreamTechnology downstreamGraph seed bound right := by
  rw [funext_iff]
  exact drive_future_iff downstreamTechnology downstreamGraph seed left.val right.val

theorem future_error_is_current (bound : Nat) (decoder : (Nat → FiniteBinaryDrive) → ℂ) :
    error (historyPMF bound) (futureQuery downstreamTechnology downstreamGraph seed bound)
      (timeTask downstreamTechnology downstreamGraph seed bound) decoder =
    error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (timeTask downstreamTechnology downstreamGraph seed bound) (decoder ∘ futureRead) := by
  simp only [error, future_query_factorizes, Function.comp_apply]

theorem future_decoder_grid_lower (bound : Nat) (decoder : (Nat → FiniteBinaryDrive) → ℂ) :
    gridBase (hardware := hardware) bound ≤
      error (historyPMF bound) (futureQuery downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder := by
  rw [future_error_is_current]
  exact decoder_grid_lower downstreamTechnology downstreamGraph seed bound (decoder ∘ futureRead)

theorem future_decoder_eventually_fails (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) :
    ∃ first : Nat, ∀ bound : Nat, first ≤ bound → ∀ decoder : (Nat → FiniteBinaryDrive) → ℂ,
      epsilon ^ 2 < error (historyPMF bound) (futureQuery downstreamTechnology downstreamGraph seed bound)
        (timeTask downstreamTechnology downstreamGraph seed bound) decoder := by
  obtain ⟨first, generated⟩ := gridBase_eventually_exceeds (hardware := hardware) epsilon nonnegative
  exact ⟨first, fun bound later decoder => (generated bound later).trans_le
    (future_decoder_grid_lower downstreamTechnology downstreamGraph seed bound decoder)⟩

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
