import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Glue

/-! The source-generated global flow is unitary for every real coupling and every pair of times. -/
set_option autoImplicit false
open Set
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

structure Development (perturbation : ℝ → E →L[ℂ] E) where
  curve : ℝ → ℝ → E → ℝ → E
  starts : ∀ epsilon start initial, curve epsilon start initial start=initial
  evolves : ∀ epsilon start initial time,
    HasDerivAt (curve epsilon start initial)
      (generator perturbation epsilon time (curve epsilon start initial time)) time

def development (perturbation : ℝ → E →L[ℂ] E)
    (continuousPerturbation : ∀ v, Continuous (fun t => perturbation t v))
    (boundedHistory : ∀ radius, 0<radius → ∃ M, ∀ t ∈ Icc (-radius) radius, ‖perturbation t‖≤M)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) : Development perturbation :=
  Classical.choice (by
    have generated := global_exists perturbation continuousPerturbation boundedHistory symmetric
    choose curve starts evolves using generated
    exact ⟨⟨curve,starts,evolves⟩⟩)

theorem global_curve_norm (perturbation : ℝ → E →L[ℂ] E)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon : ℝ) (curve : ℝ → E)
    (evolves : ∀ t, HasDerivAt curve (generator perturbation epsilon t (curve t)) t)
    (first second : ℝ) : ‖curve first‖=‖curve second‖ := by
  have squared (t : ℝ) : HasDerivAt (fun s => ‖curve s‖^2) 0 t :=
    norm_derivative perturbation symmetric epsilon t curve (evolves t)
  have constant := is_const_of_deriv_eq_zero
    (fun t => (squared t).differentiableAt) (fun t => (squared t).deriv) first second
  nlinarith [norm_nonneg (curve first),norm_nonneg (curve second)]

theorem global_curve_unique (perturbation : ℝ → E →L[ℂ] E)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon start : ℝ)
    (first second : ℝ → E)
    (firstEquation : ∀ t, HasDerivAt first (generator perturbation epsilon t (first t)) t)
    (secondEquation : ∀ t, HasDerivAt second (generator perturbation epsilon t (second t)) t)
    (initial : first start=second start) : first=second := by
  have difference (t : ℝ) : HasDerivAt (fun s => first s-second s)
      (generator perturbation epsilon t (first t-second t)) t := by
    convert! (firstEquation t).sub (secondEquation t) using 1
    simp only [map_sub]
  funext t
  have same := global_curve_norm perturbation symmetric epsilon (fun s => first s-second s) difference t start
  simpa only [initial,sub_self,norm_zero,norm_eq_zero,sub_eq_zero] using same

namespace Development
variable {perturbation : ℝ → E →L[ℂ] E}
    (development : Development perturbation)
    (symmetric : ∀ t, IsSelfAdjoint (perturbation t)) (epsilon start time : ℝ)

include symmetric in
theorem norm (initial : E) : ‖development.curve epsilon start initial time‖=‖initial‖ := by
  have same := global_curve_norm perturbation symmetric epsilon (development.curve epsilon start initial)
    (development.evolves epsilon start initial) time start
  simpa only [development.starts] using same

include symmetric in
theorem add (u v : E) : development.curve epsilon start (u+v) time=
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
theorem smul (c : ℂ) (u : E) : development.curve epsilon start (c • u) time=
    c • development.curve epsilon start u time := by
  apply congrFun (global_curve_unique perturbation symmetric epsilon start
    (development.curve epsilon start (c • u)) (fun t => c • development.curve epsilon start u t)
    (development.evolves epsilon start (c • u)) _ _) time
  · intro t
    convert! (development.evolves epsilon start u t).const_smul c using 1
    simp only [map_smul]
  · simp only [development.starts]

include symmetric in
theorem compose (middle : ℝ) (initial : E) :
    development.curve epsilon middle (development.curve epsilon start initial middle) time=
      development.curve epsilon start initial time := by
  exact congrFun (global_curve_unique perturbation symmetric epsilon middle _ _
    (development.evolves epsilon middle (development.curve epsilon start initial middle))
    (development.evolves epsilon start initial) (development.starts epsilon middle _)) time

def unitary : E ≃ₗᵢ[ℂ] E where
  toFun u := development.curve epsilon start u time
  invFun u := development.curve epsilon time u start
  map_add' := development.add symmetric epsilon start time
  map_smul' := development.smul symmetric epsilon start time
  left_inv u := (development.compose symmetric epsilon start start time u).trans (development.starts epsilon start u)
  right_inv u := (development.compose symmetric epsilon time time start u).trans (development.starts epsilon time u)
  norm_map' := development.norm symmetric epsilon start time

end Development
end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
