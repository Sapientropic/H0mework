import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResolventConductor
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor

open BurnolPhysicalState MeasureTheory Set Filter
open CombConductor CofinalCanonicalSourceMaterial
open OriginalGamma.Source.RelativeConductorGapReadback OriginalGamma.Source.WeightedRadialKernel
open OriginalGamma.Source.KGamma OriginalGamma.Source.KGamma.Iterated OriginalGamma.Source.ConductorDual
open OriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.CutPower
open scoped InnerProductSpace ENNReal

open private conductor_unique from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ConductorBranches
open private gamma_pair_fourier from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKElementaryArithmeticAction.PeriodicPower.Quarter.Whole.ComplementDual.Joint.Gamma.Source.KGammaSource

local notation "R" => burnolDirectRightResolventCLM
local notation "F" => fourierL2
local notation "seed" => (burnolPaCombApproximation 0 : BurnolL2)

private theorem seed_gamma_even : reflectL2 seedGamma = seedGamma := by
  have once := gamma_pair_fourier _ _ actual_comb_seed_gamma
  have twice := gamma_pair_fourier _ _ once
  simp only [fourierL2_fourierL2] at twice
  have even : reflectL2 seed = seed :=
    mem_evenL2ClosedFace_iff.mp (burnolPaCombApproximation 0).property.2
  rw [even] at twice
  exact conductor_unique _ _ _ twice actual_comb_seed_gamma

variable (observation : GeneratedRiemannZeroObservation)
variable (half : OriginalKCombCalculation.Half observation)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "gamma" => gammaAt observation half

private def gammaPredecessor (ordinal : Nat) : BurnolL2 :=
  ((R c)^(m+(ordinal+1))) seedGamma

local notation "pre" => gammaPredecessor observation half

private theorem gamma_predecessor_even (ordinal : Nat) : reflectL2 (pre ordinal) = pre ordinal := by
  rw [gammaPredecessor, ← actual_iterate_power]
  exact actual_iterate_even c _ seed_gamma_even _

private theorem gamma_predecessor_action (ordinal : Nat) : R c (pre ordinal) = gamma ordinal := by
  change R c (((R c)^(m+(ordinal+1))) seedGamma) = ((R c)^(m+(ordinal+2))) seedGamma
  rw [show m+(ordinal+2) = (m+(ordinal+1))+1 by omega, pow_succ', mul_apply_eq_comp]

/-- The same cofinal index applies the bounded original conductor after its literal final R. -/
def secondGammaAt (ordinal : Nat) : BurnolL2 :=
  gammaR c (pre ordinal)

theorem actual_division_second_conductor (ordinal : Nat) :
    GammaPair (gamma ordinal) (secondGammaAt observation half ordinal) := by
  rw [← gamma_predecessor_action observation half]
  exact actual_gamma_R c (pre ordinal) (gamma_predecessor_even observation half ordinal)

variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (depth : Nat)

local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "second" => secondGammaAt observation half

include nontrivial depth in
theorem actual_division_second_step (ordinal : Nat) :
    second (ordinal+1) = R c (second ordinal) := by
  have old := actual_division_second_conductor observation half ordinal
  have written := actual_Gamma_R c _ _ old
  have same := (actual_division_conductor_step observation nontrivial half depth ordinal).1
  rw [← same] at written
  exact conductor_unique _ _ _ (actual_division_second_conductor observation half (ordinal+1)) written

/-- The second full write is paired with the literal original raw field through its strong two logs. -/
theorem actual_division_second_energy (ordinal : Nat) :
    inner ℂ (raw ordinal) (second ordinal) = (‖gamma ordinal‖ ^ 2 : ℝ) := by
  have original := actual_division_conductor observation nontrivial half depth ordinal
  have paid := actual_gamma_R_dual c (pre ordinal) (raw ordinal) (gamma ordinal) _ _
    (gamma_predecessor_even observation half ordinal) original.1 original.2.1 original.2.2
  rw [gamma_predecessor_action observation half] at paid
  refine paid.symm.trans ?_
  simpa only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (gamma ordinal))

include nontrivial depth in
/-- The original nonzero center mean generates a nonzero logarithmic origin term. -/
theorem actual_division_conductor_ne_zero (ordinal : Nat) : gamma ordinal ≠ 0 := by
  let k := canonicalRaw observation half ordinal 0
  have constant : ∀ᵐ x : ℝ ∂volume, |x| < (1/4 : ℝ) → (raw ordinal) x = k := by
    filter_upwards [actual_raw_source observation nontrivial half depth ordinal] with x read inside
    exact read.trans (canonical_source_gap observation half ordinal inside.le)
  have live : k ≠ 0 := canonical_source_mean_ne observation half ordinal
  have graph := (actual_division_conductor observation nontrivial half depth ordinal).1
  obtain ⟨budget, budgetNonnegative, origin⟩ := actual_constant_gap_gamma_origin _ _ k graph constant
  intro gone
  rw [gone] at origin
  have normPositive : 0 < ‖k‖ := norm_pos_iff.mpr live
  let radius := min (1/8 : ℝ) (Real.exp (-(budget/‖k‖+1)))
  have radiusPositive : 0 < radius := lt_min (by norm_num) (Real.exp_pos _)
  have nonnull : (volume : Measure ℝ) (Ioo 0 radius) ≠ 0 := by
    rw [Real.volume_Ioo, sub_zero]
    exact (ENNReal.ofReal_pos.mpr radiusPositive).ne'
  have aebound : ∀ᵐ x : ℝ ∂volume.restrict (Ioo 0 radius), |Real.log x| * ‖k‖ ≤ budget := by
    filter_upwards [ae_restrict_of_ae (s := Ioo 0 radius) origin,
      ae_restrict_of_ae (s := Ioo 0 radius) (Lp.coeFn_zero (α := ℝ) (E := ℂ) (p := 2) (μ := volume)),
      ae_restrict_mem measurableSet_Ioo] with x near zero inside
    have paid := near ⟨inside.1, inside.2.trans_le (min_le_left _ _)⟩
    have zeroRead : (0 : BurnolL2) x = (0 : ℂ) := by simpa only [Pi.zero_apply] using zero
    rwa [zeroRead, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos inside.1] at paid
  obtain ⟨x, inside, bounded⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae nonnull aebound
  have smaller : Real.log x < -(budget/‖k‖+1) :=
    (Real.log_lt_iff_lt_exp inside.1).mpr (inside.2.trans_le (min_le_right _ _))
  have negative : Real.log x < 0 := smaller.trans_le (by
    have h := div_nonneg budgetNonnegative normPositive.le
    linarith)
  have forced := mul_lt_mul_of_pos_right (neg_lt_neg smaller) normPositive
  rw [neg_neg, add_mul, div_mul_cancel₀ _ normPositive.ne', one_mul] at forced
  rw [abs_of_neg negative] at bounded
  linarith

theorem actual_division_second_energy_positive (ordinal : Nat) :
    0 < (inner ℂ (raw ordinal) (second ordinal)).re := by
  rw [actual_division_second_energy observation half nontrivial depth]
  simpa only [Complex.ofReal_re] using
    pow_pos (norm_pos_iff.mpr (actual_division_conductor_ne_zero observation half nontrivial depth ordinal)) 2

/-- A second, independently chosen original K tests the whole conductor write. -/
theorem actual_division_second_K_price (ordinal : Nat) (test : BurnolCompletedMellinCoordinate) :
    inner ℂ (actualSecondGammaKernel test) (raw ordinal) =
      inner ℂ (burnolCompletedMellinRieszVector test : BurnolL2) (second ordinal) := by
  have original := actual_division_conductor observation nontrivial half depth ordinal
  have once := actual_kernel_complete_log_sources test
  have twice := actual_gamma_kernel_complete_log_sources test
  have dual := actual_gamma_R_dual c (pre ordinal) (burnolCompletedMellinRieszVector test : BurnolL2)
    (actualGammaKernel test) _ _ (gamma_predecessor_even observation half ordinal)
    (actual_gamma_original_kernel test) once.1 once.2
  rw [gamma_predecessor_action observation half] at dual
  exact (whole_conductor_dual _ _ _ _ _ _ _ _ (actual_second_gamma_kernel test)
    original.1 twice.1 twice.2 original.2.1 original.2.2).trans dual

end OriginalKFiniteOrderRelease.PositionGapCayley.DivisionConductor
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
