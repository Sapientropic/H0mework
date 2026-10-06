import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.GlobalGlue
import H0mework.Versions.AB.Physics.LowEnergyMatterSpace.PerturbedResponse

/-! The source-generated global flow is unitary for every real coupling and every pair of times. -/
set_option autoImplicit false
open Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
noncomputable section

structure GlobalPerturbedDevelopment (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2) where
  curve : ℝ → ℝ → MatterL2 → ℝ → MatterL2
  starts : ∀ epsilon start initial, curve epsilon start initial start=initial
  evolves : ∀ epsilon start initial time,
    HasDerivAt (curve epsilon start initial)
      (interactionGenerator perturbation epsilon time (curve epsilon start initial time)) time

def globalPerturbedDevelopment (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (continuousPerturbation : Continuous perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) : GlobalPerturbedDevelopment perturbation :=
  Classical.choice (by
    have generated := perturbed_global_exists perturbation continuousPerturbation symmetric
    choose curve starts evolves using generated
    exact ⟨⟨curve,starts,evolves⟩⟩)

theorem global_curve_norm (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon : ℝ) (curve : ℝ → MatterL2)
    (evolves : ∀ t, HasDerivAt curve (interactionGenerator perturbation epsilon t (curve t)) t)
    (first second : ℝ) : ‖curve first‖=‖curve second‖ := by
  have squared (t : ℝ) : HasDerivAt (fun s => ‖curve s‖^2) 0 t :=
    perturbed_norm_derivative perturbation symmetric epsilon t curve (evolves t)
  have constant := is_const_of_deriv_eq_zero
    (fun t => (squared t).differentiableAt) (fun t => (squared t).deriv) first second
  nlinarith [norm_nonneg (curve first),norm_nonneg (curve second)]

theorem global_curve_unique (perturbation : ℝ → MatterL2 →L[ℂ] MatterL2)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon start : ℝ)
    (first second : ℝ → MatterL2)
    (firstEquation : ∀ t, HasDerivAt first (interactionGenerator perturbation epsilon t (first t)) t)
    (secondEquation : ∀ t, HasDerivAt second (interactionGenerator perturbation epsilon t (second t)) t)
    (initial : first start=second start) : first=second := by
  have difference (t : ℝ) : HasDerivAt (fun s => first s-second s)
      (interactionGenerator perturbation epsilon t (first t-second t)) t := by
    convert! (firstEquation t).sub (secondEquation t) using 1
    simp only [map_sub]
  funext t
  have same := global_curve_norm perturbation symmetric epsilon (fun s => first s-second s) difference t start
  simpa only [initial,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using same

namespace GlobalPerturbedDevelopment
variable {perturbation : ℝ → MatterL2 →L[ℂ] MatterL2}
    (development : GlobalPerturbedDevelopment perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon start time : ℝ)

include symmetric in
theorem norm (initial : MatterL2) : ‖development.curve epsilon start initial time‖=‖initial‖ := by
  have same := global_curve_norm perturbation symmetric epsilon (development.curve epsilon start initial)
    (development.evolves epsilon start initial) time start
  simpa only [development.starts] using same

include symmetric in
theorem add (u v : MatterL2) : development.curve epsilon start (u+v) time=
    development.curve epsilon start u time+development.curve epsilon start v time := by
  apply congrFun (global_curve_unique perturbation symmetric epsilon start
    (development.curve epsilon start (u+v))
    (fun t => development.curve epsilon start u t+development.curve epsilon start v t)
    (development.evolves epsilon start (u+v)) _ _) time
  · intro t
    convert! (development.evolves epsilon start u t).add (development.evolves epsilon start v t) using 1
    simp only [map_add]
  · simp only [development.starts]

include symmetric in
theorem smul (c : ℂ) (u : MatterL2) : development.curve epsilon start (c • u) time=
    c • development.curve epsilon start u time := by
  apply congrFun (global_curve_unique perturbation symmetric epsilon start
    (development.curve epsilon start (c • u)) (fun t => c • development.curve epsilon start u t)
    (development.evolves epsilon start (c • u)) _ _) time
  · intro t
    convert! (development.evolves epsilon start u t).const_smul c using 1
    simp only [map_smul]
  · simp only [development.starts]

include symmetric in
theorem compose (middle : ℝ) (initial : MatterL2) :
    development.curve epsilon middle (development.curve epsilon start initial middle) time=
      development.curve epsilon start initial time := by
  exact congrFun (global_curve_unique perturbation symmetric epsilon middle _ _
    (development.evolves epsilon middle (development.curve epsilon start initial middle))
    (development.evolves epsilon start initial) (development.starts epsilon middle _)) time

def unitary : MatterL2 ≃ₗᵢ[ℂ] MatterL2 where
  toFun u := development.curve epsilon start u time
  invFun u := development.curve epsilon time u start
  map_add' := development.add symmetric epsilon start time
  map_smul' := development.smul symmetric epsilon start time
  left_inv u := (development.compose symmetric epsilon start start time u).trans (development.starts epsilon start u)
  right_inv u := (development.compose symmetric epsilon time time start u).trans (development.starts epsilon time u)
  norm_map' := development.norm symmetric epsilon start time

/-- The restriction retains the same global curve, including outside the restricted interval. -/
def window (radius : ℝ) (positive : 0<radius) : PerturbedDevelopment perturbation where
  radius := radius
  positive := positive
  curve := development.curve
  starts := fun epsilon start initial _ _ => development.starts epsilon start initial
  evolves := fun epsilon start initial _ _ t _ => development.evolves epsilon start initial t

def physicalCurve (initial : MatterL2) : MatterL2 :=
  spatialUnitary time (development.curve epsilon start (spatialUnitary (-start) initial) time)

def physicalUnitary : MatterL2 ≃ₗᵢ[ℂ] MatterL2 :=
  ((spatialUnitary (-start)).trans (development.unitary symmetric epsilon start time)).trans (spatialUnitary time)

@[simp] theorem physicalUnitary_apply (initial : MatterL2) :
    development.physicalUnitary symmetric epsilon start time initial=
      development.physicalCurve epsilon start time initial := rfl

end GlobalPerturbedDevelopment
end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response
