import H0mework.Versions.R2.Physics.RadialDynamics.Acceptance
import Mathlib.Analysis.ODE.ExistUnique

/-! The nonlinear generator is the canonical vector field of the original
Legendre energy, together with the source Dirac phase equation. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear

open SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Dynamics Stage9C.Material.SpinPair
open scoped ContDiff

noncomputable section

abbrev PhaseSpace := ℝ × ℝ × ℝ

def hamiltonian (state : PhaseSpace) : ℝ := energy state.1 state.2.1

def generator (state : PhaseSpace) : PhaseSpace :=
  (deriv (energy state.1) state.2.1,
    -deriv (fun amplitude => energy amplitude state.2.1) state.1,
    3*lapse/2*(spinScale-state.1))

theorem energy_momentum (amplitude canonicalMomentum : ℝ) :
    HasDerivAt (energy amplitude) (canonicalMomentum/inertia) canonicalMomentum := by
  rw [show energy amplitude = fun p => p^2/(2*inertia) + potential amplitude from
    funext (energy_eq amplitude)]
  convert (((hasDerivAt_id canonicalMomentum).pow 2).div_const (2*inertia)).add_const
    (potential amplitude) using 1
  all_goals first | rfl | simp only [id_eq]; ring

theorem energy_position (amplitude canonicalMomentum : ℝ) :
    HasDerivAt (fun q => energy q canonicalMomentum) (restoring amplitude) amplitude := by
  simp_rw [energy_eq]
  rw [restoring_eq]
  exact (potential_hasDerivAt amplitude).const_add _

theorem generator_eq (state : PhaseSpace) :
    generator state = (state.2.1/inertia, -restoring state.1, 3*lapse/2*(spinScale-state.1)) := by
  rw [generator, (energy_momentum _ _).deriv, (energy_position _ _).deriv]

theorem generator_contDiff : ContDiff ℝ 1 generator := by
  rw [show generator = fun state : PhaseSpace =>
    (state.2.1/inertia, -(3/(sourceCoupling*lapse)*state.1^3 - 6*lapse*spinScale),
      3*lapse/2*(spinScale-state.1)) from funext (fun state => by rw [generator_eq, restoring_eq])]
  have position : ContDiff ℝ 1 (fun state : PhaseSpace => state.1) := contDiff_fst
  have momentum : ContDiff ℝ 1 (fun state : PhaseSpace => state.2.1) := contDiff_snd.fst
  exact (momentum.div_const inertia).prodMk
    (((contDiff_const.mul (position.pow 3)).sub contDiff_const).neg.prodMk
      (contDiff_const.mul (contDiff_const.sub position)))

def seed (canonicalImpulse : ℝ) : PhaseSpace := (gaugeScale, canonicalImpulse, 0)

structure LocalOrbit (initial : PhaseSpace) (initialTime : ℝ) where
  radius : ℝ
  positive : 0 < radius
  curve : ℝ → PhaseSpace
  starts : curve initialTime = initial
  evolves : ∀ time ∈ Set.Ioo (initialTime-radius) (initialTime+radius),
    HasDerivAt curve (generator (curve time)) time

theorem localOrbit_exists (initial : PhaseSpace) (initialTime : ℝ) :
    Nonempty (LocalOrbit initial initialTime) := by
  obtain ⟨curve, starts, radius, positive, evolves⟩ :=
    generator_contDiff.contDiffAt.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ initialTime
      (x₀ := initial)
  exact ⟨⟨radius, positive, curve, starts, evolves⟩⟩

def orbit (canonicalImpulse : ℝ) : LocalOrbit (seed canonicalImpulse) 0 :=
  Classical.choice (localOrbit_exists (seed canonicalImpulse) 0)

theorem orbit_source (canonicalImpulse : ℝ) :
    (orbit canonicalImpulse).curve 0 = (gaugeScale, canonicalImpulse, 0) :=
  (orbit canonicalImpulse).starts

end
end SaturationMonoid.PhysicsCore.Stage10.GaugeSpectrum.Nonlinear
