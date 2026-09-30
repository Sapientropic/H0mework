import H0mework.Chemistry.LAlaninePropagation.GeneratedElectronicDynamics
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Analytic.CPolynomialDef
import Mathlib.Tactic.NoncommRing

/-!
# Short-time response from the source Hamiltonian

Unitary conjugation preserves the norm of the first commutator. Consequently
the quadratic remainder is controlled by the Hamiltonian norm, without a
caller-supplied trajectory or second-derivative certificate.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Propagation.Dynamics.ShortTime

open Interface
open _root_.SaturationMonoid.AffineRelaxation
open Set

noncomputable section

def generator (source : ElectronicPropagationSource) : ElectronicOperator :=
  -(Complex.I • hamiltonian source)

def tangent (source : ElectronicPropagationSource) (observable : ElectronicOperator) :
    ElectronicOperator :=
  generator source * observable - observable * generator source

def conjugated (source : ElectronicPropagationSource) (observable : ElectronicOperator)
    (time : ℝ) : ElectronicOperator :=
  propagator source time * observable * propagator source (-time)

@[simp] theorem conjugated_zero (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) : conjugated source observable 0 = observable := by
  simp [conjugated]

theorem generator_norm (source : ElectronicPropagationSource) :
    ‖generator source‖ = ‖hamiltonian source‖ := by
  simp [generator, norm_smul]

theorem conjugated_norm (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) (time : ℝ) :
    ‖conjugated source observable time‖ = ‖observable‖ := by
  rw [conjugated, CStarRing.norm_mul_mem_unitary _ (propagator_unitary source (-time)),
    CStarRing.norm_mem_unitary_mul _ (propagator_unitary source time)]

theorem tangent_norm_le (source : ElectronicPropagationSource) (observable : ElectronicOperator) :
    ‖tangent source observable‖ ≤ 2 * ‖hamiltonian source‖ * ‖observable‖ := by
  calc
    ‖tangent source observable‖ ≤
        ‖generator source * observable‖ + ‖observable * generator source‖ := norm_sub_le _ _
    _ ≤ ‖generator source‖ * ‖observable‖ + ‖observable‖ * ‖generator source‖ :=
      add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = 2 * ‖hamiltonian source‖ * ‖observable‖ := by rw [generator_norm]; ring

theorem propagator_hasDerivAt_right (source : ElectronicPropagationSource) (time : ℝ) :
    HasDerivAt (propagator source) (propagator source time * generator source) time := by
  change HasDerivAt (fun t => propagator source t) _ time
  simpa only [propagator_eq_realExp, generator] using!
    boundedHamiltonian_exponentialSlice_hasDerivAt_operator_right (hamiltonian source) time

theorem conjugated_hasDerivAt (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) (time : ℝ) :
    HasDerivAt (conjugated source observable)
      (conjugated source (tangent source observable) time) time := by
  have backward : HasDerivAt (fun t : ℝ => propagator source (-t))
      (-(generator source * propagator source (-time))) time := by
    simpa [generator] using!
      (propagator_hasDerivAt source (-time)).scomp time ((hasDerivAt_id time).neg)
  have derivative := ((propagator_hasDerivAt_right source time).mul_const observable).mul backward
  change HasDerivAt (conjugated source observable) _ time at derivative
  apply derivative.congr_deriv
  simp only [conjugated, tangent]
  ext state i
  simp
  ring

theorem conjugated_contDiff (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) : ContDiff ℝ 2 (conjugated source observable) := by
  have expSmooth : ContDiff ℝ 2 (NormedSpace.exp : ElectronicOperator → ElectronicOperator) :=
    (show AnalyticOnNhd ℝ NormedSpace.exp univ from
      fun point _ => NormedSpace.exp_analytic point).contDiff
  have propagatorSmooth : ContDiff ℝ 2 (propagator source) := by
    have same : propagator source = fun time : ℝ => NormedSpace.exp (time • generator source) :=
      funext (propagator_eq_realExp source)
    rw [same]
    exact expSmooth.comp (contDiff_id.smul contDiff_const)
  exact (propagatorSmooth.mul contDiff_const).mul (propagatorSmooth.comp contDiff_neg)

theorem conjugated_derivWithin (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) {duration time : ℝ} (positive : 0 < duration)
    (inside : time ∈ Icc (0 : ℝ) duration) :
    derivWithin (conjugated source observable) (Icc (0 : ℝ) duration) time =
      conjugated source (tangent source observable) time :=
  (conjugated_hasDerivAt source observable time).hasDerivWithinAt.derivWithin
    (uniqueDiffOn_Icc positive time inside)

theorem conjugated_secondDerivWithin (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) {duration time : ℝ} (positive : 0 < duration)
    (inside : time ∈ Icc (0 : ℝ) duration) :
    iteratedDerivWithin 2 (conjugated source observable) (Icc (0 : ℝ) duration) time =
      conjugated source (tangent source (tangent source observable)) time := by
  rw [show 2 = 1 + 1 from rfl, iteratedDerivWithin_succ]
  simp only [iteratedDerivWithin_one]
  rw [derivWithin_congr
    (fun t ht => conjugated_derivWithin source observable positive ht)
    (conjugated_derivWithin source observable positive inside)]
  exact conjugated_derivWithin source (tangent source observable) positive inside

/-- A source-derived second-derivative bound, tightened by unitary conjugation. -/
theorem conjugated_remainder_bound (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) {time : ℝ} (positive : 0 < time) :
    ‖conjugated source observable time -
      (observable + time • tangent source observable)‖ ≤
      (2 * ‖hamiltonian source‖ * ‖tangent source observable‖) * time ^ 2 := by
  have remainder := taylor_mean_remainder_bound
    (f := conjugated source observable) (a := 0) (b := time) (n := 1)
    positive.le (conjugated_contDiff source observable).contDiffOn
    (show time ∈ Icc (0 : ℝ) time from ⟨positive.le, le_rfl⟩)
    (C := 2 * ‖hamiltonian source‖ * ‖tangent source observable‖)
    (by
      intro t ht
      rw [conjugated_secondDerivWithin source observable positive ht, conjugated_norm]
      exact tangent_norm_le source (tangent source observable))
  simpa [iteratedDerivWithin_one, conjugated_derivWithin source observable positive
    (show (0 : ℝ) ∈ Icc 0 time from ⟨le_rfl, positive.le⟩)] using! remainder

/-- The commutator norm cancels: nonreturn does not require a chosen entry's magnitude. -/
theorem conjugated_ne_self_of_shortTime (source : ElectronicPropagationSource)
    (observable : ElectronicOperator) (nonzero : tangent source observable ≠ 0)
    {time : ℝ} (positive : 0 < time) (short : 2 * ‖hamiltonian source‖ * time < 1) :
    conjugated source observable time ≠ observable := by
  intro same
  have estimate := conjugated_remainder_bound source observable positive
  have cancel : observable - (observable + time • tangent source observable) =
      -(time • tangent source observable) := by abel
  rw [same, cancel, norm_neg, norm_smul, Real.norm_of_nonneg positive.le] at estimate
  have leadingPositive : 0 < time * ‖tangent source observable‖ :=
    mul_pos positive (norm_pos_iff.mpr nonzero)
  have strict := mul_lt_mul_of_pos_right short leadingPositive
  nlinarith

theorem tangent_initialDensity (source : ElectronicPropagationSource) :
    tangent source (initialDensity source) = densityTangent source := by
  ext state i
  simp [tangent, generator, densityTangent]
  ring

theorem initialTangent_ne_of_integer (source : ElectronicPropagationSource)
    (i j : Basis) (nonzero : integerCommutator source i j ≠ 0) :
    tangent source (initialDensity source) ≠ 0 := by
  rw [tangent_initialDensity]
  intro zero
  have smulZero : Complex.I • (hamiltonian source * initialDensity source -
      initialDensity source * hamiltonian source) = 0 := neg_eq_zero.mp zero
  exact operatorCommutator_ne_of_integer source i j nonzero
    ((smul_eq_zero.mp smulZero).resolve_left Complex.I_ne_zero)

/-- Every positive time inside this source Hamiltonian bound changes the native density. -/
theorem density_response_of_shortTime (source : ElectronicPropagationSource)
    (i j : Basis) (nonzero : integerCommutator source i j ≠ 0)
    {time : ℝ} (positive : 0 < time) (short : 2 * ‖hamiltonian source‖ * time < 1) :
    densityEvolution source time ≠ initialDensity source :=
  conjugated_ne_self_of_shortTime source (initialDensity source)
    (initialTangent_ne_of_integer source i j nonzero) positive short

def rationalDuration (bound : ℚ) : ℚ := 1 / (4 * bound)

theorem rationalDuration_positive {bound : ℚ} (positive : 0 < bound) :
    0 < rationalDuration bound := by
  unfold rationalDuration
  positivity

/-- A source-certified rational operator-norm bound generates a positive responding duration. -/
theorem density_response_at_rationalDuration (source : ElectronicPropagationSource)
    (i j : Basis) (nonzero : integerCommutator source i j ≠ 0)
    (bound : ℚ) (positive : 0 < bound) (coefficientBound : ‖hamiltonian source‖ ≤ (bound : ℝ)) :
    0 < rationalDuration bound ∧
      densityEvolution source (rationalDuration bound : ℝ) ≠ initialDensity source := by
  have realPositive : (0 : ℝ) < (bound : ℝ) := by exact_mod_cast positive
  have timePositive : (0 : ℝ) < (rationalDuration bound : ℝ) := by
    exact_mod_cast rationalDuration_positive positive
  refine ⟨rationalDuration_positive positive,
    density_response_of_shortTime source i j nonzero timePositive ?_⟩
  calc
    2 * ‖hamiltonian source‖ * (rationalDuration bound : ℝ) ≤
        2 * (bound : ℝ) * (rationalDuration bound : ℝ) := by gcongr
    _ = (1 : ℝ) / 2 := by
      simp only [rationalDuration, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat]
      field_simp
      ring
    _ < 1 := by norm_num

end

end LAlanine40K2025.Propagation.Dynamics.ShortTime
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
