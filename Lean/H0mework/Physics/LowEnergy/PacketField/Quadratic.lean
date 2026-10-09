import H0mework.Physics.LowEnergy.PacketField.Spatial

/-! The original finite current Hessian acts on genuine reconstructed fields;
its spatial integral equals the same primitive quadratic form on the band. -/
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.PacketField
open FullQuantum FullSpace PacketPairResponse
noncomputable section
attribute [local irreducible] retardedField
variable {ι : Type*} [Fintype ι]

def quadraticDensity (current : Matrix ι ι ℝ) (field : ι → FullMatterL2) : ℝ :=
  (1/2 : ℝ)*∑ first, ∑ second, current first second*(inner ℂ (field first) (field second)).re

theorem retardedPair_integrable (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) (first second : ι) :
    Integrable (fun point : LightBand => (inner ℂ
      (retardedField circleY circleZ numerator energy damping positive time point first)
      (retardedField circleY circleZ numerator energy damping positive time point second)).re) bandMeasure := by
  obtain ⟨leftBound,_,left⟩ := retardedField_bounded circleY circleZ numerator energy damping positive time first
  obtain ⟨rightBound,rightNonnegative,right⟩ := retardedField_bounded circleY circleZ numerator energy damping positive time second
  have measurable := (retardedField_stronglyMeasurable circleY circleZ numerator energy damping positive time first).inner
    (𝕜 := ℂ) (retardedField_stronglyMeasurable circleY circleZ numerator energy damping positive time second)
  have whole : Integrable (fun point : LightBand => inner ℂ
      (retardedField circleY circleZ numerator energy damping positive time point first)
      (retardedField circleY circleZ numerator energy damping positive time point second)) bandMeasure := by
    apply Integrable.of_bound measurable.aestronglyMeasurable (leftBound*rightBound)
    filter_upwards with point
    exact (norm_inner_le_norm _ _).trans (mul_le_mul (left point) (right point) (norm_nonneg _) (by
      exact (norm_nonneg _).trans (left point)))
  exact whole.re

theorem quadraticDensity_integral (current : Matrix ι ι ℝ)
    (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    (∫ point : LightBand, quadraticDensity current
      (retardedField circleY circleZ numerator energy damping positive time point) ∂bandMeasure)=
      (1/2 : ℝ)*∑ first, ∑ second, current first second*
        ∫ point : LightBand, (inner ℂ
          (retardedField circleY circleZ numerator energy damping positive time point first)
          (retardedField circleY circleZ numerator energy damping positive time point second)).re ∂bandMeasure := by
  have term (first second : ι) :=
    (retardedPair_integrable circleY circleZ numerator energy damping positive time first second).const_mul (current first second)
  unfold quadraticDensity
  rw [integral_const_mul,integral_finsetSum _ (fun first _ => integrable_finsetSum _ (fun second _ => term first second))]
  congr 1
  apply Finset.sum_congr rfl
  intro first _
  rw [integral_finsetSum _ (fun second _ => term first second)]
  simp_rw [integral_const_mul]

theorem reconstructedField_current (current : Matrix ι ι ℝ)
    (circleY circleZ : CircleData ι) (numerator : ι → List PoleTerm)
    (energy damping : ℝ) (positive : 0 < damping) (time : ℝ) :
    localQuadratic current (reconstructedField circleY circleZ numerator energy damping positive time)=
      fourierDensity*∫ point : LightBand, quadraticDensity current
        (retardedField circleY circleZ numerator energy damping positive time point) ∂bandMeasure := by
  rw [quadraticDensity_integral,localQuadratic]
  simp_rw [reconstructedField_pair]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring

end
end SaturationMonoid.PhysicsCore.LowEnergy.PacketField
