import H0mework.Quantum.Generator.Invariance
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A source Hamiltonian residual bounds the actual time-orbit error after
removing its energy phase. The bound uses the original derivative domain. -/

set_option autoImplicit false

namespace SaturationMonoid.Quantum.Generator

noncomputable section

def energyPhase (energy t : ℝ) : ℂ := Complex.exp ((t : ℂ) * energy * Complex.I)

theorem energyPhase_norm (energy t : ℝ) : ‖energyPhase energy t‖ = 1 := by
  simp [energyPhase, Complex.norm_exp]

theorem energyPhase_zero (energy : ℝ) : energyPhase energy 0 = 1 := by
  simp [energyPhase]

theorem energyPhase_cancel (energy t : ℝ) :
    energyPhase energy t * energyPhase energy (-t) = 1 := by
  rw [energyPhase, energyPhase, ← Complex.exp_add]
  have zero : (t : ℂ) * energy * Complex.I + ((-t : ℝ) : ℂ) * energy * Complex.I = 0 := by
    push_cast
    ring
  rw [zero, Complex.exp_zero]

theorem energyPhase_hasDerivAt (energy t : ℝ) :
    HasDerivAt (energyPhase energy) (energyPhase energy t * (energy * Complex.I)) t := by
  have raw := ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const
    ((energy : ℂ) * Complex.I)).cexp
  change HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * energy * Complex.I))
    (Complex.exp ((t : ℂ) * energy * Complex.I) * (energy * Complex.I)) t
  simpa only [energyPhase, Complex.ofRealCLM_apply, Complex.ofReal_one, one_mul, mul_assoc] using raw

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H))

private theorem shifted_derivative (v : domain U) (energy t : ℝ) :
    HasDerivAt (fun s => energyPhase energy s • orbit U v.val s)
      (energyPhase energy t • (-Complex.I •
        orbit U (hamiltonian U v - (energy : ℂ) • v.val) t)) t := by
  have raw := (energyPhase_hasDerivAt energy t).smul (orbit_hasDerivAt U v t)
  convert! raw using 1
  have generator_value : generator U v = -Complex.I • hamiltonian U v := by
    simp [hamiltonian, smul_smul]
  rw [generator_value]
  simp only [orbit, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_sub, smul_smul]
  module

theorem orbit_energy_error (v : domain U) (energy t : ℝ) :
    ‖orbit U v.val t - energyPhase energy (-t) • v.val‖ ≤
      |t| * ‖hamiltonian U v - (energy : ℂ) • v.val‖ := by
  have derivativeBound (s : ℝ) :
      ‖energyPhase energy s • (-Complex.I •
        orbit U (hamiltonian U v - (energy : ℂ) • v.val) s)‖ ≤
      ‖hamiltonian U v - (energy : ℂ) • v.val‖ := by
    rw [norm_smul, energyPhase_norm, one_mul, norm_smul, norm_neg, Complex.norm_I, one_mul]
    exact (U (Multiplicative.ofAdd s)).norm_map _ |>.le
  have bound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_ : s ∈ Set.univ) => (shifted_derivative U v energy s).hasDerivWithinAt)
    (fun s _ => derivativeBound s) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
    (Set.mem_univ 0) (Set.mem_univ t)
  have same : energyPhase energy t • (orbit U v.val t - energyPhase energy (-t) • v.val) =
      energyPhase energy t • orbit U v.val t - v.val := by
    rw [smul_sub, smul_smul, energyPhase_cancel, one_smul]
  rw [energyPhase_zero, orbit_zero, one_smul, sub_zero, Real.norm_eq_abs, ← same,
    norm_smul, energyPhase_norm, one_mul] at bound
  exact bound.trans_eq (mul_comm _ _)

end
end SaturationMonoid.Quantum.Generator
