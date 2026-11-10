import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.GenericFoundation.Quantum.Dynamics.Smearing.Integral

/-! Vectorwise measurable bounded kernels generate bounded operator-valued L1 integration without operator-norm measurability. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory

namespace SaturationMonoid.Quantum.Dynamics.Smearing
noncomputable section
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H] [NormedSpace ℂ H]
  [CompleteSpace H] (μ : Measure X) (K : X → H →L[ℂ] H)
  (measurable : ∀ v, AEStronglyMeasurable (fun p => K p v) μ)
  (C : ℝ) (nonnegative : 0 ≤ C) (bounded : ∀ p, ‖K p‖ ≤ C)

def onVector (v : H) : Lp ℂ 1 μ →L[ℂ] H :=
  integralMap μ (fun p => K p v) (measurable v) (C*‖v‖)
    (fun p => (K p).le_of_opNorm_le (bounded p) v)

theorem onVector_integral (v : H) (f : Lp ℂ 1 μ) :
    onVector μ K measurable C bounded v f = ∫ p, f p • K p v ∂μ := integralMap_apply _ _ _ _ _ _

include measurable bounded in
omit [CompleteSpace H] in
theorem onVector_integrable (v : H) (f : Lp ℂ 1 μ) : Integrable (fun p => f p • K p v) μ :=
  kernel_integrable μ (fun p => K p v) (measurable v) (C*‖v‖)
    (fun p => (K p).le_of_opNorm_le (bounded p) v) f

theorem onVector_bound (v : H) (f : Lp ℂ 1 μ) :
    ‖onVector μ K measurable C bounded v f‖ ≤ (C*‖f‖)*‖v‖ := by
  rw [onVector_integral]
  calc
    _ ≤ ∫ p, ‖f p • K p v‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ p, ‖f p‖ * (C*‖v‖) ∂μ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall (fun p => norm_nonneg _)
      · exact (L1.integrable_coeFn f).norm.mul_const _
      · exact Filter.Eventually.of_forall (fun p => by
          dsimp only
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left ((K p).le_of_opNorm_le (bounded p) v) (norm_nonneg _))
    _ = _ := by rw [integral_mul_const, ← L1.norm_eq_integral_norm]; ring

def onL1 : Lp ℂ 1 μ →L[ℂ] (H →L[ℂ] H) :=
  LinearMap.mkContinuous
    { toFun f := LinearMap.mkContinuous
        { toFun v := onVector μ K measurable C bounded v f
          map_add' v w := by
            simp only [onVector_integral, map_add, smul_add]
            exact integral_add (onVector_integrable μ K measurable C bounded v f)
              (onVector_integrable μ K measurable C bounded w f)
          map_smul' c v := by
            simp only [onVector_integral, map_smul]
            simp_rw [smul_comm (f _) c]
            exact integral_smul c _ }
        (C*‖f‖) (onVector_bound μ K measurable C bounded · f)
      map_add' f g := by
        ext v
        exact (onVector μ K measurable C bounded v).map_add f g
      map_smul' c f := by
        ext v
        exact (onVector μ K measurable C bounded v).map_smul c f }
    C (fun f => ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg nonnegative (norm_nonneg f))
      (onVector_bound μ K measurable C bounded · f))

theorem onL1_integral (f : Lp ℂ 1 μ) (v : H) :
    onL1 μ K measurable C nonnegative bounded f v = ∫ p, f p • K p v ∂μ :=
  onVector_integral μ K measurable C bounded v f

end
end SaturationMonoid.Quantum.Dynamics.Smearing
