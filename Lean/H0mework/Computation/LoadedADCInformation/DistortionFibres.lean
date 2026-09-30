import H0mework.Computation.LoadedADCInformation.DistortionSource

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Netlist.Dissipative.Dimensioned.Driven.Producer
namespace FiniteADCWholeJointCurrent.Information.Distortion

open Std.Sat Std.Tactic.BVDecide Units.Interface Cells.Conductance Cells.Storage
open Netlist.Dissipative.Dimensioned.Driven.Interface
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

def fibre (bound : Nat) (side : Fin 2) : Finset (Fin (bound + 1)) :=
  Finset.univ.filter (fun actor => phase actor.val = side)

def phaseCount (bound : Nat) (side : Fin 2) : Nat := (bound + 2 - side.val) / 2

@[simp] theorem mem_fibre (bound : Nat) (side : Fin 2) (actor : Fin (bound + 1)) :
    actor ∈ fibre bound side ↔ phase actor.val = side := by simp [fibre]

def phaseIndex (bound : Nat) (side : Fin 2) (index : Fin (phaseCount bound side)) : Fin (bound + 1) :=
  ⟨2 * index.val + side.val, by
    have inside := index.isLt
    have sideBound := side.isLt
    unfold phaseCount at inside
    omega⟩

@[simp] theorem phaseIndex_val (bound : Nat) (side : Fin 2) (index : Fin (phaseCount bound side)) :
    (phaseIndex bound side index).val = 2 * index.val + side.val := rfl

@[simp] theorem phaseIndex_phase (bound : Nat) (side : Fin 2) (index : Fin (phaseCount bound side)) :
    phase (phaseIndex bound side index).val = side := by
  apply Fin.ext
  change (2 * index.val + side.val) % 2 = side.val
  omega

def phaseEquiv (bound : Nat) (side : Fin 2) : Fin (phaseCount bound side) ≃ {actor // actor ∈ fibre bound side} where
  toFun index := ⟨phaseIndex bound side index, (mem_fibre bound side _).mpr (phaseIndex_phase bound side index)⟩
  invFun actor := ⟨actor.val.val / 2, by
    have same := congrArg Fin.val ((mem_fibre bound side actor.val).mp actor.property)
    change actor.val.val % 2 = side.val at same
    have inside := actor.val.isLt
    have sideBound := side.isLt
    unfold phaseCount
    omega⟩
  left_inv index := by
    apply Fin.ext
    change (2 * index.val + side.val) / 2 = index.val
    omega
  right_inv actor := by
    apply Subtype.ext
    apply Fin.ext
    have same := congrArg Fin.val ((mem_fibre bound side actor.val).mp actor.property)
    change actor.val.val % 2 = side.val at same
    change 2 * (actor.val.val / 2) + side.val = actor.val.val
    omega

theorem fibre_card (bound : Nat) (side : Fin 2) : (fibre bound side).card = phaseCount bound side := by
  have counted := Fintype.card_congr (phaseEquiv bound side)
  simpa only [Fintype.card_fin, Fintype.card_coe] using counted.symm

theorem sum_fibre {M : Type*} [AddCommMonoid M] (bound : Nat) (side : Fin 2) (read : Fin (bound + 1) → M) :
    ∑ actor ∈ fibre bound side, read actor = ∑ index : Fin (phaseCount bound side), read (phaseIndex bound side index) := by
  rw [← Finset.sum_coe_sort]
  exact (Equiv.sum_comp (phaseEquiv bound side) (fun actor => read actor.val)).symm

theorem sum_phase_fibres {M : Type*} [AddCommMonoid M] (bound : Nat) (read : Fin 2 → Fin (bound + 1) → M) :
    ∑ side : Fin 2, ∑ actor ∈ fibre bound side, read side actor =
      ∑ actor : Fin (bound + 1), read (phase actor.val) actor := by
  simp only [fibre, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro actor _
  simp

theorem phaseCount_total (bound : Nat) : phaseCount bound 0 + phaseCount bound 1 = bound + 1 := by
  simp only [phaseCount, Fin.val_zero, Fin.val_one]
  omega

theorem phaseCount_lower (bound : Nat) (side : Fin 2) : (bound + 1) / 2 ≤ phaseCount bound side := by
  have sideBound := side.isLt
  unfold phaseCount
  omega

theorem phaseCount_pos_of_mem (bound : Nat) (side : Fin 2) (actor : Fin (bound + 1))
    (member : actor ∈ fibre bound side) : 0 < phaseCount bound side := by
  have positive := ((phaseEquiv bound side).symm ⟨actor, member⟩).isLt
  omega

variable {β : Type} [DecidableEq β] [Hashable β]
variable {hardware : FiniteADCClockedNoisyMeteredSynchronousFixtureSource}
  {actualBoot : FiniteDimensionedSeriesRLCPortState} {technology : AIGCellTechnology}
variable (downstreamTechnology : AIGCellTechnology) (downstreamGraph : AIG β)
variable (seed : FiniteADCWholeJointCurrent hardware (loadedReceiverInstalledMaxTick hardware technology actualBoot) technology)

theorem fibre_is_original (bound : Nat) (actor : Fin (bound + 1)) :
    fibre bound (phase actor.val) = Finset.univ.filter (fun candidate =>
      query downstreamTechnology downstreamGraph seed bound candidate = query downstreamTechnology downstreamGraph seed bound actor) := by
  ext candidate
  simp only [mem_fibre, Finset.mem_filter, Finset.mem_univ, true_and,
    query_fibre downstreamTechnology downstreamGraph seed]

theorem phase_query (bound : Nat) (side : Fin 2) (index : Fin (phaseCount bound side)) :
    query downstreamTechnology downstreamGraph seed bound (phaseIndex bound side index) =
      driveAt downstreamTechnology downstreamGraph seed side.val := by
  change driveAt downstreamTechnology downstreamGraph seed (phaseIndex bound side index).val = _
  rw [drive_phase, phaseIndex_phase]

theorem fibre_is_original_side (bound : Nat) (side : Fin 2) :
    fibre bound side = Finset.univ.filter (fun actor =>
      query downstreamTechnology downstreamGraph seed bound actor = driveAt downstreamTechnology downstreamGraph seed side.val) := by
  ext actor
  simp only [mem_fibre, Finset.mem_filter, Finset.mem_univ, true_and]
  change phase actor.val = side ↔
    driveAt downstreamTechnology downstreamGraph seed actor.val = driveAt downstreamTechnology downstreamGraph seed side.val
  rw [drive_phase downstreamTechnology downstreamGraph seed actor.val]
  exact (phase_drive_injective downstreamTechnology downstreamGraph seed).eq_iff.symm

theorem query_image (bound : Nat) :
    Finset.univ.image (query downstreamTechnology downstreamGraph seed bound) =
      (Finset.univ.filter (fun side : Fin 2 => 0 < phaseCount bound side)).image
        (fun side => driveAt downstreamTechnology downstreamGraph seed side.val) := by
  ext drive
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨actor, rfl⟩
    exact ⟨phase actor.val, phaseCount_pos_of_mem bound _ actor ((mem_fibre bound _ actor).mpr rfl),
      (drive_phase downstreamTechnology downstreamGraph seed actor.val).symm⟩
  · rintro ⟨side, positive, rfl⟩
    exact ⟨phaseIndex bound side ⟨0, positive⟩, phase_query downstreamTechnology downstreamGraph seed bound side _⟩

theorem sum_query_image {M : Type*} [AddCommMonoid M] (bound : Nat) (read : FiniteBinaryDrive → M) :
    ∑ value ∈ Finset.univ.image (query downstreamTechnology downstreamGraph seed bound), read value =
      ∑ side : Fin 2, if 0 < phaseCount bound side then
        read (driveAt downstreamTechnology downstreamGraph seed side.val) else 0 := by
  rw [query_image, Finset.sum_image]
  · rw [Finset.sum_filter]
  · intro left _ right _ same
    exact phase_drive_injective downstreamTechnology downstreamGraph seed same

end
end FiniteADCWholeJointCurrent.Information.Distortion
end Netlist.Dissipative.Dimensioned.Driven.Producer
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
