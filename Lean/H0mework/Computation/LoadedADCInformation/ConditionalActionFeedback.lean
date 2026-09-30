import H0mework.Computation.LoadedADCInformation.ConditionalActionReaction

/-! A changed command does not provide free recovery of the original next time. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.ConditionalAction

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

open SourceGeneratedRuntimeHistoryProbability SourceWeightedRecovery

def nextQuery (bound : Nat) (point : Fin (bound + 1)) : FiniteBinaryDrive :=
  driveAt downstreamTechnology downstreamGraph seed (point.val + 1)

def nextGap : ℝ :=
  charge downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed 1) +
    charge downstreamTechnology downstreamGraph (loadedAfter downstreamTechnology downstreamGraph seed 2)

theorem nextGap_pos : 0 < nextGap downstreamTechnology downstreamGraph seed :=
  add_pos (charge_pos downstreamTechnology downstreamGraph _) (charge_pos downstreamTechnology downstreamGraph _)

theorem nextGap_actual :
    loadedElapsed downstreamTechnology downstreamGraph seed 3 =
      loadedElapsed downstreamTechnology downstreamGraph seed 1 + nextGap downstreamTechnology downstreamGraph seed := by
  rw [loadedElapsed_succ downstreamTechnology downstreamGraph seed 2,
    loadedElapsed_succ downstreamTechnology downstreamGraph seed 1]
  simp only [nextGap, charge, add_assoc]

theorem next_error_source (bound : Nat) (decoder : FiniteBinaryDrive → ℂ) :
    error (historyPMF bound) (nextQuery downstreamTechnology downstreamGraph seed bound)
      (futureTime downstreamTechnology downstreamGraph seed bound) decoder =
    error (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
      (futureTime downstreamTechnology downstreamGraph seed bound) (decoder ∘ driveFlip) := by
  simp only [error, nextQuery, query, driveAt_next, Function.comp_apply]
  rfl

theorem next_time_lower_bound (bound : Nat) (enough : 2 ≤ bound) (decoder : FiniteBinaryDrive → ℂ) :
    nextGap downstreamTechnology downstreamGraph seed ^ 2 / (2 * (bound + 1 : ℝ)) ≤
      error (historyPMF bound) (nextQuery downstreamTechnology downstreamGraph seed bound)
        (futureTime downstreamTechnology downstreamGraph seed bound) decoder := by
  rw [next_error_source]
  let first : Fin (bound + 1) := ⟨0, by omega⟩
  let third : Fin (bound + 1) := ⟨2, by omega⟩
  have distinct : first ≠ third := by intro same; have := congrArg Fin.val same; simp [first, third] at this
  have same : query downstreamTechnology downstreamGraph seed bound first =
      query downstreamTechnology downstreamGraph seed bound third :=
    (driveAt_two downstreamTechnology downstreamGraph seed 0).symm
  have weight : (historyPMF bound first).toReal = (historyPMF bound third).toReal := by
    rw [history_weight, history_weight]
  have paid := equal_weight_pair_lower_bound (historyPMF bound) (query downstreamTechnology downstreamGraph seed bound)
    (futureTime downstreamTechnology downstreamGraph seed bound) (decoder ∘ driveFlip) first third distinct same weight
  have delta : ‖futureTime downstreamTechnology downstreamGraph seed bound first -
      futureTime downstreamTechnology downstreamGraph seed bound third‖ ^ 2 =
        nextGap downstreamTechnology downstreamGraph seed ^ 2 := by
    rw [futureTime_actual, futureTime_actual, timeRead_exposure, timeRead_exposure, norm_sub_rev]
    change ‖(loadedElapsed downstreamTechnology downstreamGraph seed 3 : ℂ) -
      (loadedElapsed downstreamTechnology downstreamGraph seed 1 : ℂ)‖ ^ 2 = _
    rw [nextGap_actual, Complex.ofReal_add, add_sub_cancel_left]
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [history_weight, delta] at paid
  convert paid using 1
  field_simp

theorem next_time_error_positive (bound : Nat) (enough : 2 ≤ bound) (decoder : FiniteBinaryDrive → ℂ) :
    0 < error (historyPMF bound) (nextQuery downstreamTechnology downstreamGraph seed bound)
      (futureTime downstreamTechnology downstreamGraph seed bound) decoder :=
  lt_of_lt_of_le (div_pos (sq_pos_of_pos (nextGap_pos downstreamTechnology downstreamGraph seed))
    (by positivity)) (next_time_lower_bound downstreamTechnology downstreamGraph seed bound enough decoder)

end
end FiniteADCWholeJointCurrent.Information.ConditionalAction
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
