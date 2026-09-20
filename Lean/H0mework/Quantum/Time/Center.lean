import H0mework.Quantum.Generator.Approximate
import H0mework.Quantum.Algebra.Action

/-! Subtracting a source-generated energy changes the vector time by its
scalar phase, while leaving the entire observable conjugation action equal. -/

set_option autoImplicit false

namespace SaturationMonoid.Quantum.Time

open Generator

noncomputable section

theorem energyPhase_add (energy s t : ℝ) :
    energyPhase energy (s + t) = energyPhase energy s * energyPhase energy t := by
  simp [energyPhase, Complex.ofReal_add, add_mul, Complex.exp_add]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def phaseUnitary (energy t : ℝ) : H ≃ₗᵢ[ℂ] H where
  __ := LinearEquiv.smulOfNeZero ℂ H (energyPhase energy t)
    (fun zero => by simpa [zero] using energyPhase_norm energy t)
  norm_map' x := by
    change ‖energyPhase energy t • x‖ = ‖x‖
    rw [norm_smul, energyPhase_norm, one_mul]

variable (U : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H)) (energy : ℝ)

def centered : Multiplicative ℝ →* (H ≃ₗᵢ[ℂ] H) where
  toFun t := phaseUnitary energy t.toAdd * U t
  map_one' := by
    ext x
    change energyPhase energy 0 • U 1 x = x
    rw [energyPhase_zero, map_one, one_smul]
    rfl
  map_mul' s t := by
    ext x
    change energyPhase energy (s.toAdd + t.toAdd) • U (s * t) x =
      energyPhase energy s.toAdd • U s (energyPhase energy t.toAdd • U t x)
    rw [energyPhase_add, map_mul, map_smul, smul_smul]
    rfl

theorem centered_apply (t : Multiplicative ℝ) (x : H) :
    centered U energy t x = energyPhase energy t.toAdd • U t x := rfl

theorem centered_symm_apply (t : Multiplicative ℝ) (x : H) :
    (centered U energy t).symm x = energyPhase energy (-t.toAdd) • (U t).symm x := by
  have inverse : (centered U energy t).symm = centered U energy t⁻¹ := by
    change (centered U energy t)⁻¹ = centered U energy t⁻¹
    rw [map_inv]
  rw [inverse, centered_apply, map_inv U t]
  rfl

theorem centered_conjugation [CompleteSpace H] (t : Multiplicative ℝ) (A : H →L[ℂ] H) :
    (centered U energy t).conjStarAlgEquiv A = (U t).conjStarAlgEquiv A := by
  ext x
  change centered U energy t (A ((centered U energy t).symm x)) = U t (A ((U t).symm x))
  rw [centered_symm_apply, centered_apply, map_smul, map_smul, smul_smul,
    energyPhase_cancel, one_smul]

theorem centered_continuous (continuousOrbit : ∀ x, Continuous (Generator.orbit U x)) (x : H) :
    Continuous (Generator.orbit (centered U energy) x) := by
  have phaseContinuous : Continuous (energyPhase energy) :=
    (show Differentiable ℝ (energyPhase energy) from
      fun t => (energyPhase_hasDerivAt energy t).differentiableAt).continuous
  exact phaseContinuous.smul (continuousOrbit x)

theorem centered_error (v : H) (t : ℝ) :
    ‖Generator.orbit (centered U energy) v t - v‖ =
      ‖Generator.orbit U v t - energyPhase energy (-t) • v‖ := by
  have same : energyPhase energy t •
      (Generator.orbit U v t - energyPhase energy (-t) • v) =
        Generator.orbit (centered U energy) v t - v := by
    rw [smul_sub, smul_smul, energyPhase_cancel, one_smul]
    rfl
  rw [← same, norm_smul, energyPhase_norm, one_mul]

variable (E : ℕ → Type*) [∀ k, NormedAddCommGroup (E k)] [∀ k, InnerProductSpace ℂ (E k)]
  [∀ k, CompleteSpace (E k)] [∀ k, Nontrivial (E k)]

theorem centered_bounded_action
    (family : ∀ k, Multiplicative ℝ →* (E k ≃ₗᵢ[ℂ] E k)) (floor : ℕ → ℝ) :
    Dynamics.action E (fun k => centered (family k) (floor k)) = Dynamics.action E family := by
  apply MonoidHom.ext
  intro t
  apply StarAlgEquiv.ext
  intro A
  apply lp.ext
  funext k
  exact centered_conjugation (family k) (floor k) t (A k)

end
end SaturationMonoid.Quantum.Time
