import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.OriginalCombClockCusp
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCofinalPaAction.Source
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.Projection

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear

open BurnolPhysicalState Filter Set
open scoped ComplexOrder InnerProductSpace Topology

open private response response_derivative orbit orbit_mem orbit_pair width_pos from
  H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.LocalPaAdjointSmear
open private literal_raw sourceIndex from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionConductor

local notation "R" => burnolDirectRightResolventCLM
local notation "E" => OriginalKCombCofinalPaAction.E
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)
local notation "J" => Ioo (-(2 * Real.log 2)) (2 * Real.log 2)

private def mode (c : BurnolCompletedMellinCoordinate) (n : Nat) (h : ℝ) : ℂ :=
  response (((R c)^n) seed) h

private theorem mode_derivative (c : BurnolCompletedMellinCoordinate) (n : Nat) (h : ℝ) :
    HasDerivAt (mode c (n+1)) ((c.value/2-1/4) * mode c (n+1) h + mode c n h) h := by
  unfold mode
  rw [pow_succ', mul_apply_eq_comp]
  exact response_derivative c _ h

private theorem clock_coefficients_separate (c : BurnolCompletedMellinCoordinate) (N : Nat)
    (a : Nat → ℂ) (quiet : ∀ h ∈ J, (∑ n ∈ Finset.range N, a n * mode c n h) = 0) :
    ∀ k < N, a k = 0 := by
  induction N generalizing a with
  | zero => intro k inside; omega
  | succ N previous =>
    let tail (h : ℝ) := ∑ n ∈ Finset.range N, a (n+1) * mode c (n+1) h
    let shifted (h : ℝ) := ∑ n ∈ Finset.range N, a (n+1) * mode c n h
    let decay := c.value/2-1/4
    have split (h : ℝ) (inside : h ∈ J) : tail h + a 0 * mode c 0 h = 0 := by
      simpa only [Finset.sum_range_succ', tail] using quiet h inside
    have differentiated (h : ℝ) : HasDerivAt tail (decay * tail h + shifted h) h := by
      have piece (n : Nat) (_ : n ∈ Finset.range N) :
          HasDerivAt (fun t => a (n+1) * mode c (n+1) t)
            (a (n+1) * (decay * mode c (n+1) h + mode c n h)) h :=
        (mode_derivative c n h).const_mul _
      have finite := HasDerivAt.sum piece
      have arrange :
          (∑ n ∈ Finset.range N, a (n+1) * (decay * mode c (n+1) h + mode c n h)) =
            decay * tail h + shifted h := by
        simp only [mul_add, Finset.sum_add_distrib, tail, shifted, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro n _
        ring
      have same : (∑ n ∈ Finset.range N, fun t => a (n+1) * mode c (n+1) t) = tail := by
        funext t
        simp only [Finset.sum_apply, tail]
      rw [arrange, same] at finite
      exact finite
    have head : a 0 = 0 := by
      by_contra nonzero
      have zeroInside : (0 : ℝ) ∈ J := ⟨by linarith [width_pos], width_pos⟩
      have represented : mode c 0 =ᶠ[𝓝 0] (fun h => (a 0)⁻¹ • (-tail h)) := by
        filter_upwards [Ioo_mem_nhds zeroInside.1 zeroInside.2] with h hh
        rw [smul_eq_mul, mul_comm, ← div_eq_mul_inv]
        apply (eq_div_iff nonzero).mpr
        have balance := split h hh
        linear_combination balance
      have smoothTail := ((differentiated 0).differentiableAt.neg).const_smul (a 0)⁻¹
      have smooth := smoothTail.congr_of_eventuallyEq represented
      have origin : mode c 0 = response seed := by
        funext h
        simp only [mode, pow_zero, one_apply_eq_self]
      rw [origin] at smooth
      exact seed_response_not_differentiable smooth
    have silent (h : ℝ) (inside : h ∈ J) : tail h = 0 := by
      simpa only [head, zero_mul, add_zero] using split h inside
    have lower (h : ℝ) (inside : h ∈ J) : shifted h = 0 := by
      have flat : tail =ᶠ[𝓝 h] fun _ => (0:ℂ) :=
        Filter.Eventually.mono (Ioo_mem_nhds inside.1 inside.2) fun _ hh => silent _ hh
      have derivativeZero := (hasDerivAt_const h (0:ℂ)).congr_of_eventuallyEq flat
      have paid := (differentiated h).unique derivativeZero
      simpa only [silent h inside, mul_zero, zero_add] using paid
    intro k inside
    cases k with
    | zero => exact head
    | succ k => exact previous (fun n => a (n+1)) lower k (Nat.lt_of_succ_lt_succ inside)

/-- Every original Pa projection of the counted R orbit contributes a new independent slot. -/
theorem original_R_Pa_linearIndependent (c : BurnolCompletedMellinCoordinate) :
    LinearIndependent ℂ (fun n : Nat => E (((R c)^n) seed)) := by
  classical
  rw [linearIndependent_iff']
  intro indices coefficients vanished i inside
  obtain ⟨N, within⟩ := indices.exists_nat_subset_range
  let padded (k : Nat) := if k ∈ indices then coefficients k else 0
  have clockVanished (h : ℝ) (locality : h ∈ J) :
      (∑ k ∈ indices, coefficients k * mode c k h) = 0 := by
    obtain ⟨test, testIn, native⟩ := Submodule.mem_map.mp (orbit_mem (Ioo_subset_Ioc_self locality))
    change (test : BurnolL2) = orbit h at native
    have read := congrArg (fun value : BurnolPaAmbientCarrier => inner ℂ test value) vanished
    simpa only [inner_sum, inner_smul_right, inner_zero_right,
      OriginalKCombCofinalPaAction.wholePa_normal_read _ _ testIn, native, orbit_pair, mode] using read
  have full (h : ℝ) (locality : h ∈ J) : (∑ k ∈ Finset.range N, padded k * mode c k h) = 0 := by
    rw [← Finset.sum_subset within (fun k _ outside => by simp [padded, outside])]
    calc
      _ = ∑ k ∈ indices, coefficients k * mode c k h :=
        Finset.sum_congr rfl fun k member => by simp [padded, member]
      _ = 0 := clockVanished h locality
  have paid := clock_coefficients_separate c N padded full i (Finset.mem_range.mp (within inside))
  simpa only [padded, if_pos inside] using paid

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "actualPa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth

/-- The independent Pa family is restricted to the actual Xi-indexed Division history. -/
theorem actual_division_Pa_linearIndependent : LinearIndependent ℂ actualPa := by
  have selected : Function.Injective (sourceIndex observation) := by
    intro i j same
    dsimp only [sourceIndex] at same
    omega
  have actual : actualPa = (fun n : Nat => E (((R c)^n) seed)) ∘ sourceIndex observation := by
    funext ordinal
    rw [OriginalKCombCofinalPaAction.actualPa, literal_raw observation nontrivial half depth]
    rfl
  rw [actual]
  exact (original_R_Pa_linearIndependent c).comp _ selected

/-- Every finite collection of literal Pa slots has a strictly positive definite original Gram. -/
theorem actual_division_Pa_gram_positive (indices : Finset Nat) :
    Matrix.PosDef (Matrix.gram ℂ (fun i : indices => actualPa i.val)) :=
  Matrix.posDef_gram_of_linearIndependent
    ((actual_division_Pa_linearIndependent observation nontrivial half depth).comp _ Subtype.val_injective)

end OriginalKFiniteOrderRelease.PositionGapCayley.LocalPaSmear
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
