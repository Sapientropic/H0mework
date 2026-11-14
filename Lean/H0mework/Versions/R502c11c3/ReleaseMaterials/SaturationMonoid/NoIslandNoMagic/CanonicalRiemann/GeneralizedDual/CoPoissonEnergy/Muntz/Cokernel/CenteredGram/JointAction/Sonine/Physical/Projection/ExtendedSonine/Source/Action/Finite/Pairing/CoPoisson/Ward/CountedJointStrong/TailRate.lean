import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
namespace OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong

open Complex Filter MeasureTheory Set
open scoped Topology

open private cell cell_bound cells_summable finite_cells sourceValue source_tendsto from
  H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Sonine.Physical.Projection.ExtendedSonine.Source.Action.Finite.Pairing.CoPoisson.Ward.CountedJointStrong

local notation "finite" => fun d (v : BurnolL2) (N : Nat) =>
  (∑ n ∈ Finset.Ico 1 N, ContinuousChannels.channel d (n : ℝ) v) -
    ∫ a : ℝ in Ioc 0 (N : ℝ), ContinuousChannels.channel d a v

private theorem cell_power_tail (M : Nat) (positive : 0 < M) :
    (∑' j : Nat, ((j+M : Nat) + 1 : ℝ)^(-(3/2 : ℝ))) ≤ 2*(M : ℝ)^(-(1/2 : ℝ)) := by
  have start : 0 < (M : ℝ) := by exact_mod_cast positive
  let power := fun x : ℝ => x^(-(3/2 : ℝ))
  have decreasing : AntitoneOn power (Ici (M : ℝ)) := fun _ hx _ _ ordered =>
    Real.rpow_le_rpow_of_nonpos (start.trans_le hx) ordered (by norm_num)
  have integral := integrableOn_Ioi_rpow_of_lt (a := -(3/2 : ℝ)) (by norm_num) start
  calc
    _ ≤ ∫ x in Ioi (M : ℝ), x^(-(3/2 : ℝ)) := by
      simpa only [power, Nat.cast_add, Nat.cast_one] using
        decreasing.tsum_comp_add_le_integral M integral
          (fun x hx => Real.rpow_nonneg (start.trans hx).le _)
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : -(3/2 : ℝ) < -1) start,
        show -(3/2 : ℝ)+1 = -(1/2 : ℝ) by norm_num]
      ring

/-- The paid whole-cell Euler action bounds the tail of the same counting
sequence, with the derivative price of the actual channel. -/
theorem directional_source_tail (direction : ℝ) (state velocity : BurnolL2)
    (source : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h state) velocity 0) :
    ∃ limit : BurnolL2, Tendsto (finite direction state) atTop (𝓝 limit) ∧
      ∀ M : Nat, 0 < M → ‖limit-finite direction state (M+1)‖ ≤
        (2*(M : ℝ)^(-(1/2 : ℝ)))*‖direction • velocity-(1/2 : ℝ) • state‖ := by
  refine ⟨sourceValue direction state, source_tendsto direction state velocity source, ?_⟩
  intro M positive
  have tail : sourceValue direction state-finite direction state (M+1) =
      ∑' j : Nat, cell direction state (j+M) := by
    dsimp only
    rw [finite_cells direction state velocity source M, sourceValue,
      ← (cells_summable direction state velocity source).sum_add_tsum_nat_add M]
    abel
  let cost := ‖direction • velocity-(1/2 : ℝ) • state‖
  have summable : Summable (fun j : Nat => ((j+M : Nat)+1 : ℝ)^(-(3/2 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using
      (summable_nat_add_iff (M+1)).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ) < -1))
  rw [tail]
  calc
    _ ≤ ∑' j : Nat, ((j+M : Nat)+1 : ℝ)^(-(3/2 : ℝ))*cost :=
      tsum_of_norm_bounded (summable.mul_right cost).hasSum
        (fun j => cell_bound direction state velocity source (j+M))
    _ ≤ _ := by
      rw [tsum_mul_right]
      exact mul_le_mul_of_nonneg_right (cell_power_tail M positive) (norm_nonneg _)

/-- A real R image generates its own channel velocity and the full reverse
counting tail bound. -/
theorem actual_resolvent_reverse_tail (c : BurnolCompletedMellinCoordinate) (input : BurnolL2) :
    let output := burnolDirectRightResolventCLM c input
    ∃ limit : BurnolL2, Tendsto (fun N => DualSource.source N output) atTop (𝓝 limit) ∧
      ∀ M : Nat, 0 < M → ‖limit-DualSource.source (M+1) output‖ ≤
        (2*(M : ℝ)^(-(1/2 : ℝ)))*‖c.value • output+(2 : ℂ) • input‖ := by
  let output := burnolDirectRightResolventCLM c input
  let speed := -((c.value-1/2) • output+(2 : ℂ) • input)
  have parameter : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  have derivative : HasDerivAt (fun h : ℝ => burnolMultiplicativeDilation h output) speed 0 := by
    have orbit := burnolDirectRightResolventOrbit_hasDerivAt (c.value/2) parameter input
    have actual := orbit.scomp_of_eq 0 ((hasDerivAt_id (0 : ℝ)).const_mul (-2)) (by norm_num)
    simp only [mul_one, Function.comp_def, id_eq] at actual
    have path : (fun h : ℝ => burnolMultiplicativeDilation (-(-2*h)/2)
        (burnolDirectRightResolvent (c.value/2) input)) =
        fun h => burnolMultiplicativeDilation h output := by
      funext h
      rw [show -(-2*h)/2=h by ring]
      rfl
    have slope : (-2 : ℝ) • ((c.value/2-1/4) • output+input) = speed := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      dsimp only [speed]
      push_cast
      module
    change HasDerivAt _ ((-2 : ℝ) • ((c.value/2-1/4) • output+input)) 0 at actual
    rw [path, slope] at actual
    exact actual
  obtain ⟨limit, converges, bound⟩ := directional_source_tail 1 output speed derivative
  refine ⟨limit, converges, ?_⟩
  intro M positive
  have cost : (1 : ℝ) • speed-(1/2 : ℝ) • output =
      -(c.value • output+(2 : ℂ) • input) := by
    rw [one_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    dsimp only [speed]
    push_cast
    module
  have paid := bound M positive
  rw [cost, norm_neg] at paid
  exact paid

end OriginalRieszFinitePairing.CoPoisson.Ward.CountedJointStrong
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.BurnolPhysicalState
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
