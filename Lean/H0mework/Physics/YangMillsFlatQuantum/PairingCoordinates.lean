import H0mework.Physics.RootRuntime.RecoveryConsumer
import Mathlib.LinearAlgebra.Basis.Prod

/-! The original exterior bases fix the positive full-matter coordinates.
The older chooseBasis coordinates do not define this physical inner product. -/

set_option autoImplicit false
open scoped InnerProductSpace

namespace SaturationMonoid.PhysicsCore.YangMills.FullPairing

open Module DiracCliffordRepresentation DiracExteriorMatterAction SU7ExteriorMatterRepresentation
open SU7ExteriorMatterRestriction
open StageNineHolonomicField Stage9C.Material.SpinPair Stage9DEF
open StageNineFullDiracAdjointMaterial ProofFreeRicherAnholonomicSource

noncomputable section

abbrev Sector := ExteriorBasisIndex 6 ⊕ ExteriorBasisIndex 2 ⊕ ExteriorBasisIndex 4
abbrev Index := DiracSpinorIndex × Sector
abbrev Hilbert := EuclideanSpace ℂ Index

private def internalBasis : Basis Sector ℂ SU7ExteriorSpinorMatterCarrier :=
  (su7ExteriorBasis 6).prod ((su7ExteriorBasis 2).prod (su7ExteriorBasis 4))

private def internalCoordinates : SU7ExteriorSpinorMatterCarrier ≃ₗ[ℂ] (Sector → ℂ) :=
  internalBasis.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite ℂ ℂ Sector

private def flatten : (DiracSpinorIndex → Sector → ℂ) ≃ₗ[ℂ] (Index → ℂ) where
  toFun f i := f i.1 i.2
  invFun f spin sector := f (spin, sector)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def naturalCoordinates : DiracExteriorMatterCarrier ≃ₗ[ℂ] Hilbert :=
  (LinearEquiv.piCongrRight (fun _ : DiracSpinorIndex => internalCoordinates)) ≪≫ₗ flatten ≪≫ₗ
    (WithLp.linearEquiv 2 ℂ (Index → ℂ)).symm

theorem naturalCoordinates_apply (matter : DiracExteriorMatterCarrier) (spin : DiracSpinorIndex)
    (sector : Sector) : naturalCoordinates matter (spin, sector) = internalBasis.repr (matter spin) sector := rfl

theorem natural_inner (first second : DiracExteriorMatterCarrier) :
    inner ℂ (naturalCoordinates first) (naturalCoordinates second) =
      ∑ spin, fullInternalPair (first spin) (second spin) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Index, naturalCoordinates second i * star (naturalCoordinates first i)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, naturalCoordinates_apply,
    internalBasis, Basis.prod_repr_inl, Basis.prod_repr_inr]
  apply Finset.sum_congr rfl
  intro spin _
  unfold fullInternalPair exteriorCoordinatePair
  rw [add_assoc]
  refine congrArg₂ (· + ·) ?_ (congrArg₂ (· + ·) ?_ ?_)
  all_goals
    apply Finset.sum_congr rfl
    intro index _
    exact mul_comm _ _

theorem inner_embed (values : Source.Index → ℂ) (matter : DiracExteriorMatterCarrier) :
    inner ℂ (naturalCoordinates (Compatibility.embed values)) (naturalCoordinates matter) =
      ∑ i, star (values i) * Compatibility.coordinates matter i := by
  rw [natural_inner, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro spin _
  change fullInternalPair (∑ color, values (spin, color) • sourceColorDoubletMatter color) (matter spin) = _
  simp [fullInternalPair, exteriorCoordinatePair, sourceColorDoubletMatter,
    sourceColorDoubletDual, Compatibility.coordinates, add_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_eq_single (sourceColorDoubletIndex 0)]
    · simp
    · intro index _ different
      simp [Ne.symm different]
    · simp
  · rw [Finset.sum_eq_single (sourceColorDoubletIndex 1)]
    · simp
    · intro index _ different
      simp [Ne.symm different]
    · simp

def prepared (point : BasePoint) : Hilbert :=
  naturalCoordinates (Compatibility.embed (Source.vector point))

theorem actual_eq_twice_prepared (point : BasePoint) :
    naturalCoordinates (actual.matter point) = (2 : ℂ) • prepared point := by
  have same : actual.matter point = (2 : ℂ) • Compatibility.embed (Source.vector point) := by
    rw [← Source.amplitude_reconstruction]
    change Compatibility.embed (Source.amplitude point) = _
    rw [← map_smul]
    exact congrArg Compatibility.embed (funext (Source.amplitude_eq_twice_vector point))
  exact (congrArg naturalCoordinates same).trans (map_smul naturalCoordinates _ _)

theorem prepared_norm (point : BasePoint) : ‖prepared point‖ = 1 := by
  have same : inner ℂ (prepared point) (prepared point) = 1 := by
    rw [prepared, inner_embed, Compatibility.coordinates_embed]
    exact Source.vector_inner_self point
  have square : ‖prepared point‖ ^ 2 = 1 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) (prepared point)).trans (congrArg Complex.re same)
  nlinarith [norm_nonneg (prepared point)]

end
end SaturationMonoid.PhysicsCore.YangMills.FullPairing
