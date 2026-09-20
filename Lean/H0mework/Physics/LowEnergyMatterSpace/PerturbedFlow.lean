import H0mework.Physics.LowEnergyMatterSpace.PerturbedNorm

/-! The generated finite-coupling developments give a genuine two-time unitary propagator. -/
set_option autoImplicit false
open Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

structure PerturbedDevelopment (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) where
  radius : ℝ
  positive : 0<radius
  curve : ℝ → ℝ → MatterL2 → ℝ → MatterL2
  starts : ∀ epsilon start initial, |epsilon|≤1 → start ∈ Ioo (-radius) radius →
    curve epsilon start initial start=initial
  evolves : ∀ epsilon start initial, |epsilon|≤1 → start ∈ Ioo (-radius) radius →
    ∀ time ∈ Ioo (-radius) radius,
      HasDerivAt (curve epsilon start initial)
        (interactionGenerator perturbation epsilon time (curve epsilon start initial time)) time

def perturbedDevelopment (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation) : PerturbedDevelopment perturbation := Classical.choice (by
  obtain ⟨radius,positive,family,generated⟩ := perturbedFamily_exists perturbation continuousPerturbation
  exact ⟨⟨radius,positive,family,fun epsilon start initial coupling located =>
    (generated epsilon start initial coupling located).1,
    fun epsilon start initial coupling located => (generated epsilon start initial coupling located).2⟩⟩)

theorem perturbed_curve_unique (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (epsilon delta start : ℝ) (located : start ∈ Ioo (-delta) delta)
    (first second : ℝ → MatterL2)
    (firstEquation : ∀ time ∈ Ioo (-delta) delta,
      HasDerivAt first (interactionGenerator perturbation epsilon time (first time)) time)
    (secondEquation : ∀ time ∈ Ioo (-delta) delta,
      HasDerivAt second (interactionGenerator perturbation epsilon time (second time)) time)
    (initial : first start=second start) : EqOn first second (Ioo (-delta) delta) := by
  have difference (time : ℝ) (inside : time ∈ Ioo (-delta) delta) :
      HasDerivAt (fun t => first t-second t)
        (interactionGenerator perturbation epsilon time (first time-second time)) time := by
    convert! (firstEquation time inside).sub (secondEquation time inside) using 1
    simp only [map_sub]
  intro time inside
  have same := perturbed_curve_norm perturbation symmetric epsilon delta
    (fun t => first t-second t) difference time start inside located
  simpa only [initial,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using same

namespace PerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : PerturbedDevelopment perturbation)
    (symmetric : ∀ time, IsSelfAdjoint (perturbation time))
    (epsilon : ℝ) (coupling : |epsilon|≤1)
    (start time : ℝ) (atStart : start ∈ Ioo (-development.radius) development.radius)
    (atTime : time ∈ Ioo (-development.radius) development.radius)

include symmetric coupling atStart atTime

theorem norm (initial : MatterL2) : ‖development.curve epsilon start initial time‖=‖initial‖ := by
  have same := perturbed_curve_norm perturbation symmetric epsilon development.radius
    (development.curve epsilon start initial)
    (development.evolves epsilon start initial coupling atStart) time start atTime atStart
  simpa only [development.starts epsilon start initial coupling atStart] using same

theorem add (u v : MatterL2) : development.curve epsilon start (u+v) time=
    development.curve epsilon start u time+development.curve epsilon start v time := by
  apply perturbed_curve_unique perturbation symmetric epsilon development.radius start atStart
    (development.curve epsilon start (u+v))
    (fun t => development.curve epsilon start u t+development.curve epsilon start v t)
    (development.evolves epsilon start (u+v) coupling atStart) _ _ atTime
  · intro t inside
    convert! (development.evolves epsilon start u coupling atStart t inside).add
        (development.evolves epsilon start v coupling atStart t inside) using 1
    simp only [map_add]
  · simp only [development.starts epsilon start _ coupling atStart]

theorem smul (scalar : ℂ) (u : MatterL2) : development.curve epsilon start (scalar • u) time=
    scalar • development.curve epsilon start u time := by
  apply perturbed_curve_unique perturbation symmetric epsilon development.radius start atStart
    (development.curve epsilon start (scalar • u))
    (fun t => scalar • development.curve epsilon start u t)
    (development.evolves epsilon start (scalar • u) coupling atStart) _ _ atTime
  · intro t inside
    convert! (development.evolves epsilon start u coupling atStart t inside).const_smul scalar using 1
    simp only [map_smul]
  · simp only [development.starts epsilon start _ coupling atStart]

theorem compose (middle : ℝ) (atMiddle : middle ∈ Ioo (-development.radius) development.radius)
    (initial : MatterL2) :
    development.curve epsilon middle (development.curve epsilon start initial middle) time=
      development.curve epsilon start initial time := by
  exact perturbed_curve_unique perturbation symmetric epsilon development.radius middle atMiddle
    (development.curve epsilon middle (development.curve epsilon start initial middle))
    (development.curve epsilon start initial)
    (development.evolves epsilon middle _ coupling atMiddle)
    (development.evolves epsilon start initial coupling atStart)
    (development.starts epsilon middle _ coupling atMiddle) atTime

def unitary : MatterL2 ≃ₗᵢ[ℂ] MatterL2 where
  toFun u := development.curve epsilon start u time
  invFun u := development.curve epsilon time u start
  map_add' := development.add symmetric epsilon coupling start time atStart atTime
  map_smul' := development.smul symmetric epsilon coupling start time atStart atTime
  left_inv u := (development.compose symmetric epsilon coupling start start atStart atStart time atTime u).trans
    (development.starts epsilon start u coupling atStart)
  right_inv u := (development.compose symmetric epsilon coupling time time atTime atTime start atStart u).trans
    (development.starts epsilon time u coupling atTime)
  norm_map' := development.norm symmetric epsilon coupling start time atStart atTime

@[simp] theorem unitary_apply (initial : MatterL2) :
    development.unitary symmetric epsilon coupling start time atStart atTime initial=
      development.curve epsilon start initial time := rfl

end PerturbedDevelopment
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
