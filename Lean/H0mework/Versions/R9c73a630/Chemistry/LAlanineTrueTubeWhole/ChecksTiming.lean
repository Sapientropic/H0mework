import H0mework.Versions.R9c73a630.Chemistry.LAlanineTrueTube.ChecksIncidence
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks

open TrueTubeSource Set
noncomputable section

def stepOffset (i : Step) : ℝ := (i.val : ℝ) * (stepSize : ℝ)

theorem stepOffset_zero : stepOffset 0 = 0 := by simp [stepOffset]

theorem stepOffset_nonneg (i : Step) : 0 ≤ stepOffset i :=
  mul_nonneg (Nat.cast_nonneg _) (Rat.cast_nonneg.mpr TrueTubeChecks.step_positive.le)

theorem stepOffset_end_le (i : Step) : stepOffset i + (stepSize : ℝ) ≤ 1 / 2 := by
  have bound : (i.val : ℝ) ≤ 15 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  norm_num [stepOffset, TrueTubeChecks.step_value]
  linarith

theorem stepOffset_succ (i : Fin 15) :
    stepOffset i.succ = stepOffset i.castSucc + (stepSize : ℝ) := by
  simp only [stepOffset, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  ring

theorem stepOffset_last_end : stepOffset 15 + (stepSize : ℝ) = 1 / 2 := by
  norm_num [stepOffset, TrueTubeChecks.step_value]

theorem sixteen_intervals_cover (t : ℝ) (time : t ∈ Icc (0 : ℝ) (1 / 2)) :
    ∃ i : Step, t ∈ Icc (stepOffset i) (stepOffset i + (stepSize : ℝ)) := by
  by_cases last : t = 1 / 2
  · exact ⟨15, by norm_num [last, stepOffset, TrueTubeChecks.step_value]⟩
  have nonneg : 0 ≤ 32 * t := by linarith [time.1]
  have strict : t < 1 / 2 := (lt_or_eq_of_le time.2).resolve_right last
  have small : 32 * t < 16 := by linarith
  let i : Step := ⟨⌊32 * t⌋₊, (Nat.floor_lt nonneg).mpr (by simpa using small)⟩
  refine ⟨i, ?_⟩
  have lower := Nat.floor_le nonneg
  have upper := Nat.lt_floor_add_one (32 * t)
  change (⌊32 * t⌋₊ : ℝ) * (stepSize : ℝ) ≤ t ∧
    t ≤ (⌊32 * t⌋₊ : ℝ) * (stepSize : ℝ) + (stepSize : ℝ)
  norm_num [TrueTubeChecks.step_value]
  constructor <;> linarith

theorem elapsedStart_eq_offset : ∀ d : Direction, ∀ i : Step,
    elapsedStart d i = sign d * (i.val : ℚ) * stepSize := by decide +kernel

theorem elapsedStop_eq_offset : ∀ d : Direction, ∀ i : Step,
    elapsedStop d i = sign d * ((i.val : ℚ) * stepSize + stepSize) := by decide +kernel

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeChecks
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
