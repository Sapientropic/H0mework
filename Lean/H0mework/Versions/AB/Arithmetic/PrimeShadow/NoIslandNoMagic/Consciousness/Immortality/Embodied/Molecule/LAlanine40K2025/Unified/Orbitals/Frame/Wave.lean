import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Frame.Sections

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.Frame
open SaturationMonoid.PhysicsCore ProofFreeRicherAnholonomicSource
open BasinRefinement SourceGaussianModel SourceFiniteData MeasureTheory UnifiedAction YangMills.FullPairing
open scoped InnerProductSpace BigOperators Matrix
noncomputable section

def sourceWave (v : Basis → ℂ) (time : ℝ) (x : Point) : Hilbert :=
  ∑ b : Basis, v b • normalizedSection b time x

theorem wave_pair (v w : Basis → ℂ) (time : ℝ) (x : Point) :
    inner ℂ (sourceWave v time x) (sourceWave w time x) =
      ∑ b : Basis, ∑ c : Basis, (star (v b)*w c) *
        (normalizedOrbital b x*normalizedOrbital c x : ℝ) := by
  simp only [sourceWave,sum_inner,inner_sum,inner_smul_left,inner_smul_right,normalizedSection_pair,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  change w c * (star (v b) * _) = _
  ring

theorem wave_pair_integrable (v w : Basis → ℂ) (time : ℝ) :
    Integrable (fun x : Point => inner ℂ (sourceWave v time x) (sourceWave w time x)) := by
  simp_rw [wave_pair]
  exact integrable_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ =>
    (normalized_pair_integrable b c).ofReal.const_mul _))

theorem wave_pair_integral (positive : actualGram.PosDef) (v w : Basis → ℂ) (time : ℝ) :
    (∫ x : Point, inner ℂ (sourceWave v time x) (sourceWave w time x)) = star v ⬝ᵥ w := by
  have each (b c : Basis) : Integrable (fun x : Point => (star (v b)*w c)*
      (normalizedOrbital b x*normalizedOrbital c x : ℝ)) :=
    (normalized_pair_integrable b c).ofReal.const_mul _
  simp_rw [wave_pair]
  rw [integral_finsetSum _ (fun b _ => integrable_finsetSum _ (fun c _ => each b c))]
  unfold dotProduct
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_finsetSum _ (fun c _ => each b c)]
  simp only [integral_const_mul,integral_complex_ofReal,normalized_pair positive,Pi.star_apply]
  rw [Finset.sum_eq_single b]
  · simp
  · intro c _ different
    simp [Ne.symm different]
  · simp

theorem source_matrix_response (positive : actualGram.PosDef)
    (A : Matrix Basis Basis ℂ) (v w : Basis → ℂ) (time : ℝ) :
    (∫ x : Point, inner ℂ (sourceWave v time x) (sourceWave (A*ᵥw) time x)) = star v ⬝ᵥ (A*ᵥw) :=
  wave_pair_integral positive _ _ _

theorem source_unitary_preserves (positive : actualGram.PosDef)
    (U : Matrix.unitaryGroup Basis ℂ) (v w : Basis → ℂ) (time : ℝ) :
    (∫ x : Point, inner ℂ (sourceWave ((U : Matrix Basis Basis ℂ)*ᵥv) time x)
      (sourceWave ((U : Matrix Basis Basis ℂ)*ᵥw) time x)) = star v ⬝ᵥ w := by
  rw [wave_pair_integral positive]
  rw [Matrix.star_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_vecMul]
  have unit : (star (U : Matrix Basis Basis ℂ))*(U : Matrix Basis Basis ℂ) = 1 := by
    exact (Unitary.mem_iff.mp U.property).1
  change star v ᵥ* (star (U : Matrix Basis Basis ℂ)*(U : Matrix Basis Basis ℂ)) ⬝ᵥ w = _
  rw [unit,Matrix.vecMul_one]

end
end LAlanine40K2025.UnifiedOrbitals.Frame
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
