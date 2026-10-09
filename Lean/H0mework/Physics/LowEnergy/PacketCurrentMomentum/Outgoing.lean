import H0mework.Physics.LowEnergy.PacketCurrentMomentum.Density
import Mathlib.Analysis.Fourier.FourierTransform

/-! The original local quadratic current has a genuine continuous outgoing
momentum transform. Its zero component recovers the certified spatial current. -/
set_option autoImplicit false
open MeasureTheory FourierTransform
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
open FullQuantum FullSpace PacketField PacketNoise
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def outgoing (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) (momentum : Position) : ℂ :=
  𝓕 (fun position : Position => (density current field position : ℂ)) (physicalTransfer momentum)

theorem outgoing_continuous (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) :
    Continuous (outgoing current field) := by
  have continuousFourier : Continuous (𝓕 (fun position : Position => (density current field position : ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
      (density_integrable current field).ofReal
  have transfer : Continuous physicalTransfer := by unfold physicalTransfer; fun_prop
  exact continuousFourier.comp transfer

theorem outgoing_zero (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) :
    outgoing current field 0=(localQuadratic current field : ℂ) := by
  simp [outgoing,physicalTransfer,Real.fourier_eq,integral_complex_ofReal,density_integral]

theorem outgoing_physical (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) (momentum : Position) :
    outgoing current field momentum=∫ position : Position,
      Complex.exp (((-(∑ j : Fin 3, momentum j*position j) : ℝ) : ℂ)*Complex.I)*
        (density current field position : ℂ) := by
  unfold outgoing
  rw [Real.fourier_eq']
  congr 1
  funext position
  have physical := physicalPhase_argument (physicalTransfer momentum) position
  simp_rw [physicalTransfer_correct] at physical
  have exponent : -2*Real.pi*inner ℝ position (physicalTransfer momentum)=
      -(∑ j : Fin 3, momentum j*position j) := by
    rw [real_inner_comm]
    linarith
  simp only [exponent,smul_eq_mul]

theorem outgoing_positive_near_zero (current : Matrix ι ι ℝ) (field : ι → FieldSpace E)
    (positive : 0<localQuadratic current field) :
    ∀ᶠ momentum : Position in nhds 0, 0<(outgoing current field momentum).re := by
  have origin : 0<(outgoing current field 0).re := by rw [outgoing_zero,Complex.ofReal_re]; exact positive
  exact (Complex.continuous_re.comp (outgoing_continuous current field)).continuousAt.eventually (Ioi_mem_nhds origin)

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
