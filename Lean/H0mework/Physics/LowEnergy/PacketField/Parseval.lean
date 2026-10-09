import H0mework.Physics.LowEnergy.PacketFourier.Native
import Mathlib.Analysis.Fourier.LpSpace

/-! Spatial Plancherel acts on the induced field position, with values in the
original matter Hilbert space. These two spatial variables remain distinct. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

abbrev FieldSpace (E : Type*) [NormedAddCommGroup E] := Lp E 2 (volume : Measure Position)

def spatialFourier : FieldSpace E ≃ₗᵢ[ℂ] FieldSpace E := Lp.fourierTransformₗᵢ Position E

theorem spatial_pair (left right : FieldSpace E) :
    (∫ position : Position, (inner ℂ (spatialFourier left position) (spatialFourier right position)).re)=
      ∫ position : Position, (inner ℂ (left position) (right position)).re := by
  simp only [← RCLike.re_eq_complex_re]
  rw [integral_re (L2.integrable_inner (𝕜 := ℂ) (spatialFourier left) (spatialFourier right)),
    integral_re (L2.integrable_inner (𝕜 := ℂ) left right),← L2.inner_def,← L2.inner_def]
  exact congrArg Complex.re (spatialFourier.inner_map_map left right)

def localQuadratic {ι : Type*} [Fintype ι] (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) : ℝ :=
  (1/2 : ℝ)*∑ first, ∑ second, current first second*
    ∫ position : Position, (inner ℂ (field first position) (field second position)).re

theorem localQuadratic_fourier {ι : Type*} [Fintype ι] (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) :
    localQuadratic current (fun i => spatialFourier (field i))=localQuadratic current field := by
  unfold localQuadratic
  simp_rw [spatial_pair]

theorem localQuadratic_inverse {ι : Type*} [Fintype ι] (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) :
    localQuadratic current (fun i => spatialFourier.symm (field i))=localQuadratic current field := by
  have generated := localQuadratic_fourier current (fun i => spatialFourier.symm (field i))
  simp only [LinearIsometryEquiv.apply_symm_apply] at generated
  exact generated.symm

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
