import H0mework.Physics.LowEnergyFockDynamics.Retarded

/-! The actual half-axis integral for complex growth and oscillation rates.
The source time derivative is lambda=eta-iE, not the normalized u coordinate. -/
set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
open MeasureTheory
noncomputable section

def laplaceParameter (energy damping : ℝ) : ℂ := (damping : ℂ)-Complex.I*(energy : ℂ)
def weight (energy damping time : ℝ) : ℂ := Complex.exp (-laplaceParameter energy damping*(time : ℂ))
def mode (rate : ℂ) (time : ℝ) : ℂ := Complex.exp (rate*(time : ℂ))

theorem original_clock (energy damping : ℝ) : laplaceParameter energy damping=
    -Complex.I*((energy : ℂ)+Complex.I*(damping : ℂ)) := by
  unfold laplaceParameter
  ring_nf
  simp [Complex.I_sq]

theorem weighted_mode (rate : ℂ) (energy damping time : ℝ) :
    weight energy damping time*mode rate time=
      Complex.exp ((rate-laplaceParameter energy damping)*(time : ℂ)) := by
  rw [weight,mode,← Complex.exp_add]
  congr 1
  ring

theorem mode_integrable (rate : ℂ) (energy damping : ℝ) (decay : rate.re<damping) :
    IntegrableOn (fun t => weight energy damping t*mode rate t) (Set.Ioi 0) := by
  simp only [weighted_mode]
  apply integrableOn_exp_mul_complex_Ioi
  simpa [laplaceParameter] using sub_neg.mpr decay

theorem mode_transform (rate : ℂ) (energy damping : ℝ) (decay : rate.re<damping) :
    (∫ t : ℝ in Set.Ioi 0, weight energy damping t*mode rate t)=
      (laplaceParameter energy damping-rate)⁻¹ := by
  simp only [weighted_mode]
  have negative : (rate-laplaceParameter energy damping).re<0 := by
    simpa [laplaceParameter] using sub_neg.mpr decay
  rw [integral_exp_mul_complex_Ioi negative 0]
  simp only [Complex.ofReal_zero,mul_zero,Complex.exp_zero]
  rw [show laplaceParameter energy damping-rate= -(rate-laplaceParameter energy damping) by ring,inv_neg]
  simp only [neg_div,one_div]

theorem finite_mode_integrable {ι : Type*} [Fintype ι] (coefficient rate : ι → ℂ)
    (energy damping : ℝ) (decay : ∀ i, (rate i).re<damping) :
    IntegrableOn (fun t => weight energy damping t*∑ i, coefficient i*mode (rate i) t) (Set.Ioi 0) := by
  simp only [Finset.mul_sum]
  have term (i : ι) (t : ℝ) : weight energy damping t*(coefficient i*mode (rate i) t)=
      coefficient i*(weight energy damping t*mode (rate i) t) := by ring
  simp_rw [term]
  apply integrable_finsetSum
  intro i _
  exact (mode_integrable (rate i) energy damping (decay i)).const_mul (coefficient i)

theorem finite_mode_transform {ι : Type*} [Fintype ι] (coefficient rate : ι → ℂ)
    (energy damping : ℝ) (decay : ∀ i, (rate i).re<damping) :
    (∫ t : ℝ in Set.Ioi 0, weight energy damping t*∑ i, coefficient i*mode (rate i) t)=
      ∑ i, coefficient i*(laplaceParameter energy damping-rate i)⁻¹ := by
  simp only [Finset.mul_sum]
  have term (i : ι) (t : ℝ) : weight energy damping t*(coefficient i*mode (rate i) t)=
      coefficient i*(weight energy damping t*mode (rate i) t) := by ring
  simp_rw [term]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul,mode_transform (rate i) energy damping (decay i)]
  · intro i _
    exact (mode_integrable (rate i) energy damping (decay i)).const_mul (coefficient i)

end
end SaturationMonoid.PhysicsCore.LowEnergy.BosonCausal
