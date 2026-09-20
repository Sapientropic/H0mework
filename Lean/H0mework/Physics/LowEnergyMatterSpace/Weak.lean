import H0mework.Physics.LowEnergyMatterSpace.Duhamel
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! The generated mild solution pays the actual generator's weak equation. -/
set_option autoImplicit false
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
noncomputable section

theorem spatial_pair_transfer (t : ℝ) (v w : MatterL2) :
    inner ℂ (spatialUnitary (-t) v) w = inner ℂ v (spatialUnitary t w) := by
  have paired := (spatialUnitary t).inner_map_map (spatialUnitary (-t) v) w
  rw [← spatialUnitary_add,add_neg_cancel,spatialUnitary_zero] at paired
  exact paired.symm

theorem duhamel_weak_pair (forcing : ℝ → MatterL2) (test : MatterL2) (t : ℝ) :
    inner ℂ test (duhamel forcing t) =
      inner ℂ (spatialUnitary (-t) test) (interactionIntegral forcing t) :=
  (spatial_pair_transfer t test (interactionIntegral forcing t)).symm

theorem duhamel_weak_derivative (forcing : ℝ → MatterL2)
    (continuousForcing : Continuous forcing)
    (test : Quantum.Generator.domain spatialAction) (t : ℝ) :
    HasDerivAt (fun time => inner ℂ (test : MatterL2) (duhamel forcing time))
      (-inner ℂ (Quantum.Generator.generator spatialAction test) (duhamel forcing t) +
        inner ℂ (test : MatterL2) (forcing t)) t := by
  have negd : HasDerivAt (fun s : ℝ => -s) (-1) t := by
    convert! (hasDerivAt_id t).neg using 1
  have left := (spatial_domain_derivative test (-t)).scomp t negd
  have paired := left.inner ℂ (interactionIntegral_derivative forcing continuousForcing t)
  simp only [duhamel_weak_pair]
  convert! paired using 1
  simp only [Function.comp_apply,neg_smul,one_smul,inner_neg_left]
  rw [spatial_pair_transfer]
  change _ = inner ℂ (spatialUnitary (-t) (test : MatterL2))
    (spatialUnitary (-t) (forcing t)) + _
  rw [(spatialUnitary (-t)).inner_map_map]
  exact add_comm _ _

theorem duhamel_weak_schrodinger (forcing : ℝ → MatterL2)
    (continuousForcing : Continuous forcing)
    (test : Quantum.Generator.domain spatialAction) (t : ℝ) :
    HasDerivAt (fun time => inner ℂ (test : MatterL2) (duhamel forcing time))
      (-Complex.I*inner ℂ (Quantum.Generator.hamiltonian spatialAction test) (duhamel forcing t) +
        inner ℂ (test : MatterL2) (forcing t)) t := by
  convert duhamel_weak_derivative forcing continuousForcing test t using 1
  simp [Quantum.Generator.hamiltonian,inner_smul_left]
  ring_nf
  simp [Complex.I_sq]

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
