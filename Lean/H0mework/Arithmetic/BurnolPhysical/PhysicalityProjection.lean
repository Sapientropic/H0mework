import H0mework.Realization.Topology.CompressedUnitaryDefectPort
import H0mework.Arithmetic.BurnolCarrier.ConstantGapFourier

/-!
# Canonical Burnol physicality projection

The closed even constant-gap face determines a canonical orthogonal
projection.  The complementary residual records precisely the information
which has not entered that physical face.  Admission is therefore the exact
equation `residual = 0`, not a branch selector or a caller-supplied flag.

Both coordinates commute with the actual Fourier action, so quotienting a
presentation cannot silently erase the Fourier/Tate relation.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace NoIslandNoMagic
namespace CanonicalRiemann
namespace ClozelGeneralizedDual
namespace BurnolPhysicalState

open SourceGeneratedCompressedUnitaryDefectPort

noncomputable section

abbrev EvenBurnolPhysicalCarrier (radius : ℝ) :=
  (evenBurnolClosedFace radius).toSubmodule

def evenBurnolPhysicalProjection (radius : ℝ) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  (evenBurnolClosedFace radius).toSubmodule.starProjection

def evenBurnolPhysicalResidual (radius : ℝ) :
    BurnolL2 →L[ℂ] BurnolL2 :=
  ContinuousLinearMap.id ℂ BurnolL2 - evenBurnolPhysicalProjection radius

/-- The same discarded information in its exact orthogonal carrier. -/
def evenBurnolOrthogonalResidual (radius : ℝ) :
    BurnolL2 →L[ℂ]
      Submodule.orthogonal (evenBurnolClosedFace radius).toSubmodule :=
  (Submodule.orthogonal
    (evenBurnolClosedFace radius).toSubmodule).orthogonalProjectionOnto

/-- Full read/write port: admitted state and inverse-fibre residual together
are isometrically equivalent to the original kinematical state. -/
def evenBurnolAdmissionPort (radius : ℝ) :
    BurnolL2 ≃ₗᵢ[ℂ]
      WithLp 2 (EvenBurnolPhysicalCarrier radius ×
        Submodule.orthogonal (evenBurnolClosedFace radius).toSubmodule) :=
  (evenBurnolClosedFace radius).toSubmodule.orthogonalDecomposition

@[simp] theorem evenBurnolAdmissionPort_fst
    (radius : ℝ) (value : BurnolL2) :
    (evenBurnolAdmissionPort radius value).fst =
      (evenBurnolClosedFace radius).toSubmodule.orthogonalProjectionOnto value := by
  exact Submodule.fst_orthogonalDecomposition_apply _ _

@[simp] theorem evenBurnolAdmissionPort_snd
    (radius : ℝ) (value : BurnolL2) :
    (evenBurnolAdmissionPort radius value).snd =
      evenBurnolOrthogonalResidual radius value := by
  exact Submodule.snd_orthogonalDecomposition_apply _ _

@[simp] theorem evenBurnolAdmissionPort_eq_zero_iff
    (radius : ℝ) (value : BurnolL2) :
    evenBurnolAdmissionPort radius value = 0 ↔ value = 0 := by
  constructor
  · intro portZero
    apply (evenBurnolAdmissionPort radius).injective
    simpa using portZero
  · rintro rfl
    exact map_zero (evenBurnolAdmissionPort radius)

theorem evenBurnolAdmissionPort_ne_zero_iff
    (radius : ℝ) (value : BurnolL2) :
    evenBurnolAdmissionPort radius value ≠ 0 ↔ value ≠ 0 := by
  rw [Ne, Ne, evenBurnolAdmissionPort_eq_zero_iff]

theorem evenBurnolOrthogonalResidual_eq_zero_iff
    (radius : ℝ) (value : BurnolL2) :
    evenBurnolOrthogonalResidual radius value = 0 ↔
      value ∈ evenBurnolClosedFace radius := by
  change (Submodule.orthogonal
      (evenBurnolClosedFace radius).toSubmodule).orthogonalProjectionOnto
        value = 0 ↔
    value ∈ (evenBurnolClosedFace radius).toSubmodule
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff,
    Submodule.orthogonal_orthogonal]

theorem evenBurnolPhysicalResidual_eq_zero_iff
    (radius : ℝ) (value : BurnolL2) :
    evenBurnolPhysicalResidual radius value = 0 ↔
      value ∈ evenBurnolClosedFace radius := by
  change value -
      (evenBurnolClosedFace radius).toSubmodule.starProjection value = 0 ↔
    value ∈ (evenBurnolClosedFace radius).toSubmodule
  rw [sub_eq_zero]
  simpa only [eq_comm] using
    ((evenBurnolClosedFace radius).toSubmodule.starProjection_eq_self_iff
      (v := value))

theorem evenBurnolPhysicalProjection_add_residual
    (radius : ℝ) (value : BurnolL2) :
    evenBurnolPhysicalProjection radius value +
        evenBurnolPhysicalResidual radius value = value := by
  simp [evenBurnolPhysicalProjection, evenBurnolPhysicalResidual]

theorem evenBurnolFace_map_fourier (radius : ℝ) :
    (evenBurnolClosedFace radius).toSubmodule.map
        fourierL2.toLinearEquiv.toLinearMap =
      (evenBurnolClosedFace radius).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨value, membership, rfl⟩
    exact fourierL2_mem_evenBurnolClosedFace membership
  · intro value membership
    refine ⟨fourierL2 value,
      fourierL2_mem_evenBurnolClosedFace membership, ?_⟩
    change fourierL2 (fourierL2 value) = value
    rw [fourierL2_fourierL2]
    exact mem_evenL2ClosedFace_iff.mp membership.2

theorem evenBurnolFourierBalanced (radius : ℝ) :
    IsBalancedFace (evenBurnolClosedFace radius) fourierL2 where
  map_eq := evenBurnolFace_map_fourier radius

theorem evenFaceFourier_involutive (radius : ℝ)
    (value : EvenBurnolPhysicalCarrier radius) :
    evenFaceFourier radius (evenFaceFourier radius value) = value := by
  apply Subtype.ext
  change fourierL2 (fourierL2 (value : BurnolL2)) = value
  rw [fourierL2_fourierL2]
  exact mem_evenL2ClosedFace_iff.mp value.property.2

/-- Fourier is a genuine involutive unitary on the admitted face, not only
an ambient map which happens to preserve its norm. -/
def evenFaceFourierEquiv (radius : ℝ) :
    EvenBurnolPhysicalCarrier radius ≃ₗᵢ[ℂ]
      EvenBurnolPhysicalCarrier radius where
  toFun := evenFaceFourier radius
  invFun := evenFaceFourier radius
  left_inv := evenFaceFourier_involutive radius
  right_inv := evenFaceFourier_involutive radius
  map_add' := (evenFaceFourier radius).map_add
  map_smul' := (evenFaceFourier radius).map_smul
  norm_map' := (evenFaceFourier radius).norm_map

theorem fourierL2_evenBurnolPhysicalProjection
    (radius : ℝ) (value : BurnolL2) :
    fourierL2 (evenBurnolPhysicalProjection radius value) =
      evenBurnolPhysicalProjection radius (fourierL2 value) := by
  exact balanced_starProjection (evenBurnolClosedFace radius) fourierL2
    (evenBurnolFourierBalanced radius) value

theorem fourierL2_evenBurnolPhysicalResidual
    (radius : ℝ) (value : BurnolL2) :
    fourierL2 (evenBurnolPhysicalResidual radius value) =
      evenBurnolPhysicalResidual radius (fourierL2 value) := by
  change fourierL2 (value - evenBurnolPhysicalProjection radius value) =
    fourierL2 value - evenBurnolPhysicalProjection radius (fourierL2 value)
  rw [map_sub, fourierL2_evenBurnolPhysicalProjection]

end
end BurnolPhysicalState
end ClozelGeneralizedDual
end CanonicalRiemann
end NoIslandNoMagic
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
