import H0mework.Versions.R2.Physics.QuantumState.StateSource

/-! Common frame changes act on both the source preparation and its effects.
The matrix incidence and every weight commute with the same unitary. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage9DEF.State

open Matrix ProofFreeRicherAnholonomicSource
open scoped ComplexOrder
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
  LAlanine40K2025.Thermal.Preparation

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem pureMatrix_mulVec (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    pureMatrix (M *ᵥ v) = M * pureMatrix v * star M := by
  simp only [pureMatrix, Matrix.star_mulVec, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.star_eq_conjTranspose]

theorem unitary_preserves_inner (U : Matrix.unitaryGroup ι ℂ) (v : ι → ℂ) :
    (∑ i, star (((U : Matrix ι ι ℂ) *ᵥ v) i) * ((U : Matrix ι ι ℂ) *ᵥ v) i) =
      ∑ i, star (v i) * v i := by
  rw [← pureMatrix_trace, pureMatrix_mulVec, unitary_conjugation_trace, pureMatrix_trace]

theorem vectorEvaluation_unitary (U : Matrix.unitaryGroup ι ℂ)
    (v : ι → ℂ) (A : Matrix ι ι ℂ) :
    vectorEvaluation ((U : Matrix ι ι ℂ) *ᵥ v)
      ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)) =
      vectorEvaluation v A := by
  rw [vectorEvaluation_eq_trace, pureMatrix_mulVec, vectorEvaluation_eq_trace]
  have composition :
      ((U : Matrix ι ι ℂ) * pureMatrix v * star (U : Matrix ι ι ℂ)) *
        ((U : Matrix ι ι ℂ) * A * star (U : Matrix ι ι ℂ)) =
      (U : Matrix ι ι ℂ) * (pureMatrix v * A) * star (U : Matrix ι ι ℂ) := by
    simp only [mul_assoc, ← mul_assoc (star (U : Matrix ι ι ℂ)) (U : Matrix ι ι ℂ),
      Unitary.coe_star_mul_self, one_mul]
  rw [composition, unitary_conjugation_trace]

def Effect.inFrame (effect : Effect) (U : Matrix.unitaryGroup Source.Index ℂ) : Effect where
  matrix := (U : Observable) * effect.matrix * star (U : Observable)
  positive := effect.positive.mul_mul_conjTranspose_same _
  complement_positive := by
    have complement : 1 - (U : Observable) * effect.matrix * star (U : Observable) =
        (U : Observable) * (1 - effect.matrix) * star (U : Observable) := by
      rw [mul_sub, Matrix.mul_one, sub_mul, ← Unitary.coe_star, Unitary.coe_mul_star_self]
    rw [complement]
    exact effect.complement_positive.mul_mul_conjTranspose_same _

def frameDensity (point : BasePoint) (U : Matrix.unitaryGroup Source.Index ℂ) : Observable :=
  normalizedGram (column ((U : Observable) *ᵥ Source.vector point) (0, 0))

theorem frameDensity_eq (point : BasePoint) (U : Matrix.unitaryGroup Source.Index ℂ) :
    frameDensity point U = (U : Observable) * density point * star (U : Observable) := by
  have normalized :
      (∑ i, star (((U : Observable) *ᵥ Source.vector point) i) *
        ((U : Observable) *ᵥ Source.vector point) i) = 1 :=
    (unitary_preserves_inner U _).trans (Source.vector_inner_self point)
  rw [frameDensity, normalizedGram_column _ _ normalized,
    pureMatrix_mulVec, density_eq_pureMatrix]

theorem sourceEffect_inFrame (point : BasePoint)
    (U : Matrix.unitaryGroup Source.Index ℂ) :
    ((sourceEffect point).inFrame U).matrix =
      pureMatrix ((U : Observable) *ᵥ Source.vector point) :=
  (pureMatrix_mulVec _ _).symm

theorem effectWeight_inFrame (point : BasePoint) (effect : Effect)
    (U : Matrix.unitaryGroup Source.Index ℂ) :
    (vectorEvaluation ((U : Observable) *ᵥ Source.vector point)
      (effect.inFrame U).matrix).re = effectWeight point effect := by
  change (vectorEvaluation ((U : Observable) *ᵥ Source.vector point)
    ((U : Observable) * effect.matrix * star (U : Observable))).re = _
  rw [vectorEvaluation_unitary]
  rfl

end
end SaturationMonoid.PhysicsCore.Stage9DEF.State
