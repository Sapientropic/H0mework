import H0mework.Physics.LowEnergyMatterSpace.Weak
import Mathlib.Analysis.Calculus.MeanValue

/-! The same generated spatial action gives existence and uniqueness for L² initial data. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
noncomputable section

def spatialDevelopment (initial : MatterL2) (forcing : ℝ → MatterL2) (t : ℝ) : MatterL2 :=
  spatialUnitary t (initial+interactionIntegral forcing t)

theorem spatialDevelopment_zero (initial : MatterL2) (forcing : ℝ → MatterL2) :
    spatialDevelopment initial forcing 0=initial := by
  simp [spatialDevelopment,interactionIntegral,spatialUnitary_zero]

theorem spatialDevelopment_interaction (initial : MatterL2) (forcing : ℝ → MatterL2) (t : ℝ) :
    spatialUnitary (-t) (spatialDevelopment initial forcing t)=initial+interactionIntegral forcing t := by
  rw [spatialDevelopment,← spatialUnitary_add,neg_add_cancel,spatialUnitary_zero]

theorem spatialDevelopment_derivative (initial : MatterL2) (forcing : ℝ → MatterL2)
    (continuousForcing : Continuous forcing) (t : ℝ) :
    HasDerivAt (fun time => spatialUnitary (-time) (spatialDevelopment initial forcing time))
      (spatialUnitary (-t) (forcing t)) t := by
  simp only [spatialDevelopment_interaction]
  convert! (hasDerivAt_const t initial).add
    (interactionIntegral_derivative forcing continuousForcing t) using 1
  simp only [zero_add]
  rfl

theorem spatialDevelopment_unique (initial : MatterL2) (forcing solution : ℝ → MatterL2)
    (continuousForcing : Continuous forcing) (initialValue : solution 0=initial)
    (equation : ∀ t, HasDerivAt (fun time => spatialUnitary (-time) (solution time))
      (spatialUnitary (-t) (forcing t)) t) :
    solution=spatialDevelopment initial forcing := by
  let difference := fun t => spatialUnitary (-t) (solution t)-interactionIntegral forcing t
  have derivative (t : ℝ) : HasDerivAt difference 0 t := by
    have d := (equation t).sub (interactionIntegral_derivative forcing continuousForcing t)
    convert! d using 1
    simp only [interactionForcing,sub_self]
  have same (t : ℝ) := is_const_of_deriv_eq_zero
    (fun time => (derivative time).differentiableAt) (fun time => (derivative time).deriv) t 0
  funext t
  apply (spatialUnitary (-t)).injective
  rw [spatialDevelopment_interaction]
  have actual := same t
  change spatialUnitary (-t) (solution t)-interactionIntegral forcing t =
    spatialUnitary (-0) (solution 0)-interactionIntegral forcing 0 at actual
  simp only [neg_zero,spatialUnitary_zero,initialValue,interactionIntegral,
    intervalIntegral.integral_same,sub_zero] at actual
  exact sub_eq_iff_eq_add.mp actual

theorem duhamel_is_unique_zero_initial (forcing solution : ℝ → MatterL2)
    (continuousForcing : Continuous forcing) (initialValue : solution 0=0)
    (equation : ∀ t, HasDerivAt (fun time => spatialUnitary (-time) (solution time))
      (spatialUnitary (-t) (forcing t)) t) :
    solution=duhamel forcing := by
  have generated := spatialDevelopment_unique 0 forcing solution continuousForcing initialValue equation
  rw [generated]
  funext t
  change spatialUnitary t (0+interactionIntegral forcing t)=spatialUnitary t (interactionIntegral forcing t)
  rw [zero_add]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
