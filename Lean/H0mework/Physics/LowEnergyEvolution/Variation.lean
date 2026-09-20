import H0mework.Physics.LowEnergyEvolution.UniformUniqueness
import H0mework.Physics.LowEnergySpectrum.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The original drifting source orbit, its true Jacobian exponential, and its nonlinear remainder. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation
open Set Filter Metric Asymptotics Stage9C.Material.SpinPair
open scoped Topology ContDiff
noncomputable section

def baseState : State := Evolution.seed 0
def phaseDrift : State := Pi.single 6 frequency
def background (time : ℝ) : State := baseState+time • phaseDrift
def jacobian : State →L[ℝ] State := fderiv ℝ generator baseState
def linearFlow (time : ℝ) : State →L[ℝ] State := NormedSpace.exp (time • jacobian)
def centeredGenerator (x : State) : State := generator (baseState+x)-phaseDrift

theorem linearFlow_zero : linearFlow 0 = 1 := by simp [linearFlow]

theorem linearFlow_derivative (v : State) (time : ℝ) :
    HasDerivAt (fun t => linearFlow t v) (jacobian (linearFlow time v)) time := by
  have derivative := (hasDerivAt_exp_smul_const' jacobian time).clm_apply (hasDerivAt_const time v)
  convert! derivative using 1
  simp only [map_zero, add_zero, mul_apply_eq_comp]
  rfl

theorem centered_zero : centeredGenerator 0 = 0 := by
  simp only [centeredGenerator, add_zero, baseState, Spectrum.generator_origin_phase, phaseDrift, sub_self]

theorem centered_derivative : HasFDerivAt centeredGenerator jacobian 0 := by
  have dg := (generator_contDiffAt baseState (seed_admissible 0)).differentiableAt (by simp) |>.hasFDerivAt
  have dg' : HasFDerivAt generator jacobian (baseState+(0:State)) := by
    convert! dg using 1
    simp
  have composed := dg'.comp 0 ((hasFDerivAt_id (0:State)).const_add baseState)
  convert! composed.sub_const phaseDrift using 1

theorem centered_remainder :
    (fun x => centeredGenerator x-jacobian x) =o[𝓝 (0:State)] fun x => x := by
  simpa only [zero_add, centered_zero, sub_zero] using
    hasFDerivAt_iff_isLittleO_nhds_zero.mp centered_derivative

theorem background_derivative (time : ℝ) : HasDerivAt background phaseDrift time := by
  convert! ((hasDerivAt_id time).smul_const phaseDrift).const_add baseState using 1
  simp

private def backgroundSolution (radius : ℝ) (positive : 0 < radius) : Solution baseState where
  radius := radius
  positive := positive
  curve := background
  starts := by simp [background]
  evolves := fun t _ => Spectrum.background_orbit t
  admissible := by
    intro t _
    have same : Admissible (background t) ↔ Admissible baseState := by
      simp [background, phaseDrift, Admissible, denominator, contorsion, gaugeEnergy]
    exact same.mpr (seed_admissible 0)
  smooth := (by unfold background; fun_prop : ContDiff ℝ ∞ background).contDiffOn

theorem uniform_background (family : UniformDevelopment baseState) (time : ℝ)
    (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    family.curve baseState time = background time := by
  have baseInside : baseState ∈ closedBall baseState family.initialRadius :=
    mem_closedBall_self (le_of_lt family.initialPositive)
  have equal := (family.solution baseState baseInside).unique_on_overlap
    (backgroundSolution family.timeRadius family.timePositive)
  exact equal (by simpa only [UniformDevelopment.solution, backgroundSolution, min_self] using inside)

def displacement (family : UniformDevelopment baseState) (initial : State) (time : ℝ) : State :=
  family.curve initial time-background time

theorem displacement_initial (family : UniformDevelopment baseState) (initial : State)
    (inside : initial ∈ closedBall baseState family.initialRadius) :
    displacement family initial 0 = initial-baseState := by
  simp [displacement, family.starts initial inside, background]

theorem displacement_derivative (family : UniformDevelopment baseState) (initial : State)
    (initialInside : initial ∈ closedBall baseState family.initialRadius) (time : ℝ)
    (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    HasDerivAt (displacement family initial)
      (centeredGenerator (displacement family initial time)) time := by
  have derivative := (family.evolves initial initialInside time inside).sub (background_derivative time)
  convert! derivative using 1
  unfold centeredGenerator
  congr 1
  have shifted := Spectrum.generator_phase_translation (baseState+displacement family initial time) time
  have identity : baseState+displacement family initial time+time • phaseDrift = family.curve initial time := by
    unfold displacement background
    abel
  change generator (baseState+displacement family initial time+time • phaseDrift) = _ at shifted
  rw [identity] at shifted
  exact shifted.symm

theorem displacement_bound (family : UniformDevelopment baseState) (initial : State)
    (initialInside : initial ∈ closedBall baseState family.initialRadius) (time : ℝ)
    (inside : time ∈ Ioo (-family.timeRadius) family.timeRadius) :
    ‖displacement family initial time‖ ≤ family.dependenceConstant*‖initial-baseState‖ := by
  have bound := family.norm_control initial baseState initialInside
    (mem_closedBall_self (le_of_lt family.initialPositive)) time inside
  rw [uniform_background family time inside] at bound
  exact bound

end
end SaturationMonoid.PhysicsCore.LowEnergy.Evolution.Variation
