import H0mework.Physics.LowEnergy.PacketField.Native

/-! The complete primitive quadratic current is an actual spatial L¹ density
on the same source state, before any outgoing momentum is selected. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
open FullQuantum FullSpace PacketField
noncomputable section
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def density (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) (position : Position) : ℝ :=
  (1/2 : ℝ)*∑ first, ∑ second, current first second*(inner ℂ (field first position) (field second position)).re

theorem density_integrable (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) :
    Integrable (density current field) (volume : Measure Position) := by
  apply Integrable.const_mul
  apply integrable_finsetSum
  intro first _
  apply integrable_finsetSum
  intro second _
  exact (L2.integrable_inner (𝕜 := ℂ) (field first) (field second)).re.const_mul (current first second)

theorem density_integral (current : Matrix ι ι ℝ) (field : ι → FieldSpace E) :
    (∫ position : Position, density current field position)=localQuadratic current field := by
  have term (first second : ι) : Integrable (fun position : Position =>
      current first second*(inner ℂ (field first position) (field second position)).re) volume :=
    (L2.integrable_inner (𝕜 := ℂ) (field first) (field second)).re.const_mul (current first second)
  unfold density localQuadratic
  rw [integral_const_mul,integral_finsetSum _ (fun first _ => integrable_finsetSum _ (fun second _ => term first second))]
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  rw [integral_finsetSum _ (fun second _ => term first second)]
  simp_rw [integral_const_mul]

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketCurrentMomentum
