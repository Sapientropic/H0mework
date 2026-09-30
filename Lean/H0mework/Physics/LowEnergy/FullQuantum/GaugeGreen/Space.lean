import H0mework.Physics.LowEnergy.FullQuantum.GaugeGreen.Free

/-! The source free resolvent satisfies its coercive imaginary-pair identity on full spatial L². -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
open FullSpace YangMills.FullPairing ProofFreeRicherAnholonomicSource
noncomputable section

def momentumFree (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    FullMatterL2 →L[ℂ] FullMatterL2 :=
  multiplier (fun frequency => freeValue point (physicalMomentum frequency) energy damping)
    ((freeValue_continuous point energy damping positive).comp physicalMomentum_continuous)
    damping⁻¹ (fun frequency => freeValue_bound point (physicalMomentum frequency) energy damping positive)
    (inv_nonneg.mpr positive.le)

theorem momentumFree_ae (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    momentumFree point energy damping positive source=ᵐ[volume] fun frequency =>
      freeValue point (physicalMomentum frequency) energy damping (source frequency) :=
  multiplierValue_ae (fun frequency => freeValue point (physicalMomentum frequency) energy damping)
    ((freeValue_continuous point energy damping positive).comp physicalMomentum_continuous)
    damping⁻¹ (fun frequency => freeValue_bound point (physicalMomentum frequency) energy damping positive) source

def freeR (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  fourier.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((momentumFree point energy damping positive).comp fourier.toContinuousLinearEquiv.toContinuousLinearMap)

theorem freeR_fourier (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    fourier (freeR point energy damping positive source)=momentumFree point energy damping positive (fourier source) :=
  fourier.apply_symm_apply _

theorem freeR_fourier_ae (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) (source : FullMatterL2) :
    fourier (freeR point energy damping positive source)=ᵐ[volume] fun frequency =>
      freeValue point (physicalMomentum frequency) energy damping (fourier source frequency) := by
  rw [freeR_fourier]
  exact momentumFree_ae point energy damping positive (fourier source)

theorem momentumFree_imaginary_pair (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) :
    (inner ℂ (momentumFree point energy damping positive source) source).im=
      damping*‖momentumFree point energy damping positive source‖^2 := by
  have integrable := L2.integrable_inner (𝕜 := ℂ) (momentumFree point energy damping positive source) source
  rw [L2.inner_def]
  change RCLike.im (∫ frequency, inner ℂ (momentumFree point energy damping positive source frequency) (source frequency))=_
  rw [← integral_im integrable,← MatterSpace.norm_square_integral volume,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [momentumFree_ae point energy damping positive source] with frequency applied
  rw [applied]
  exact freeValue_imaginary_pair point (physicalMomentum frequency) energy damping positive (source frequency)

theorem freeR_imaginary_pair (point : BasePoint) (energy damping : ℝ) (positive : 0<damping)
    (source : FullMatterL2) :
    (inner ℂ (freeR point energy damping positive source) source).im=
      damping*‖freeR point energy damping positive source‖^2 := by
  have paired := fourier.inner_map_map (freeR point energy damping positive source) source
  have norm := fourier.norm_map (freeR point energy damping positive source)
  rw [← paired,← norm,freeR_fourier]
  exact momentumFree_imaginary_pair point energy damping positive (fourier source)

theorem freeR_bound (point : BasePoint) (energy damping : ℝ) (positive : 0<damping) :
    ‖freeR point energy damping positive‖≤damping⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr positive.le)
  intro source
  have bound := norm_of_imaginary_pair damping (freeR point energy damping positive source) source
    (freeR_imaginary_pair point energy damping positive source)
  exact (le_div_iff₀ positive).mpr (by simpa only [mul_comm] using bound) |>.trans_eq (by ring)

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeGreen
