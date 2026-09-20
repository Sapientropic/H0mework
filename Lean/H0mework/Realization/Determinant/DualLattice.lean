import Mathlib.Data.Int.Order.Units
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import H0mework.Foundation.Arithmetic.IncidenceFace
import H0mework.Realization.Determinant.LatticeTrivialization

/-!
# Root-generated dual-lattice determinant state

This is the mixed-lattice arithmetic determinant kernel.  Its source data are
two actual integral lattice families and one actual bilinear pairing

`Left × Right → K`.

The kernel extends that pairing to the scalar realizations, consumes a
generated nondegeneracy calculation, and produces the basis-free morphism

`det(Left_K) ⊗ det(Right_K) → K`.

Matrices and scalar determinant coordinates occur only after a downstream
consumer installs one left frame and one right frame.  The former
positive-definite self-pairing engine is recovered by the diagonal
restriction `Left = Right`; it is not a second arithmetic determinant.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace DualLatticeDeterminant

open RootGeneratedExteriorDeterminantLine
open DerivedArithmeticAxiomFreeCore
open LatticeDeterminantTrivialization
open scoped TensorProduct

attribute [local instance 2000] Algebra.toModule

universe t u v w

/-- The mixed integral pairing represented on a single product carrier.  The
unused coordinates are zero, so its left/right restrictions are exactly the
original pairing. -/
def productPairing
    {K : Type t} {Left : Type u} {Right : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup Left] [AddCommGroup Right]
    (pairing : Left →ₗ[ℤ] Right →ₗ[ℤ] K) :
    LinearMap.BilinMap ℤ (Left × Right) K :=
  LinearMap.mk₂ ℤ (fun source target => pairing source.1 target.2)
    (fun _ _ _ => by simp) (fun integer source target => by
      simp only [Prod.smul_fst, LinearMap.map_smul]
      induction integer using Int.induction_on with
      | zero => simp [Algebra.smul_def]
      | succ integer hypothesis =>
          rw [add_zsmul, LinearMap.add_apply, hypothesis]
          simp [Algebra.smul_def]
          ring
      | pred integer hypothesis =>
          rw [sub_zsmul, LinearMap.add_apply, LinearMap.neg_apply,
            hypothesis]
          simp [Algebra.smul_def]
          ring)
    (fun _ _ _ => by simp) (fun _ _ _ => by simp)

/-- Canonical inclusions of the two integral lattices into the product
carrier used only to construct the mixed scalar extension. -/
def leftProductInclusion
    {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right] :
    Left →ₗ[ℤ] Left × Right where
  toFun left := (left, 0)
  map_add' left right := by simp
  map_smul' scalar left := by simp

def rightProductInclusion
    {Left : Type u} {Right : Type v}
    [AddCommGroup Left] [AddCommGroup Right] :
    Right →ₗ[ℤ] Left × Right where
  toFun right := (0, right)
  map_add' left right := by simp
  map_smul' scalar right := by simp

/-- Canonical scalar extension of an integral mixed pairing. -/
noncomputable def scalarExtendDualPairing
    {K : Type t} {Left : Type u} {Right : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup Left]
    [AddCommGroup Right]
    (pairing : Left →ₗ[ℤ] Right →ₗ[ℤ] K) :
    IntegralScalarExtension K Left →ₗ[K]
      IntegralScalarExtension K Right →ₗ[K] K :=
  (scalarExtendPairing (productPairing pairing)).compl₁₂
    (leftProductInclusion.baseChange K)
    (rightProductInclusion.baseChange K)

@[simp] theorem scalarExtendDualPairing_tmul
    {K : Type t} {Left : Type u} {Right : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup Left]
    [AddCommGroup Right]
    (pairing : Left →ₗ[ℤ] Right →ₗ[ℤ] K)
    (leftScalar rightScalar : K) (left : Left) (right : Right) :
    scalarExtendDualPairing pairing
        (@TensorProduct.tmul ℤ _ K Left _ _ Algebra.toModule inferInstance
          leftScalar left)
        (@TensorProduct.tmul ℤ _ K Right _ _ Algebra.toModule inferInstance
          rightScalar right) =
      leftScalar * rightScalar * pairing left right := by
  simp [scalarExtendDualPairing, productPairing, leftProductInclusion,
    rightProductInclusion, scalarExtendPairing_tmul]

/-- On the diagonal, the mixed scalar extension is exactly the former
self-pairing scalar extension. -/
theorem scalarExtendDualPairing_self_eq
    {K : Type t} {L : Type u}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup L]
    (pairing : LinearMap.BilinMap ℤ L K) :
    scalarExtendDualPairing pairing = scalarExtendPairing pairing := by
  ext left right
  induction left using TensorProduct.induction_on with
  | zero => simp
  | tmul leftScalar leftPoint =>
      induction right using TensorProduct.induction_on with
      | zero => simp
      | tmul rightScalar rightPoint =>
          simp only [scalarExtendDualPairing_tmul, scalarExtendPairing_tmul]
          rfl
      | add first second first_hypothesis second_hypothesis =>
          simp only [map_add, first_hypothesis, second_hypothesis]
  | add first second first_hypothesis second_hypothesis =>
      simp only [map_add, LinearMap.add_apply,
        first_hypothesis, second_hypothesis]

/-- The root-owned mixed pairing face.  The face is indexed by the two actual
lattice occurrence families and by the actual pairing occurrence.  It stores
no basis, matrix, determinant, regulator, or nondegeneracy premise. -/
structure RootGeneratedDualLatticePairingAt
    {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup Left]
    [AddCommGroup Right]
    (rootOccurrence : RootedAccountedUnfolding Root)
    (leftOccurrences : Left → RootedAccountedUnfolding Left)
    (rightOccurrences : Right → RootedAccountedUnfolding Right)
    (pairingOccurrence :
      RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)) : Type where
  private mk ::
  core : RootGeneratedDualIncidenceAt rootOccurrence leftOccurrences
    rightOccurrences pairingOccurrence

namespace RootGeneratedDualLatticePairingAt

variable {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
variable [CommRing K] [Algebra ℤ K]
variable [AddCommGroup Left]
variable [AddCommGroup Right]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {leftOccurrences : Left → RootedAccountedUnfolding Left}
variable {rightOccurrences : Right → RootedAccountedUnfolding Right}
variable {pairingOccurrence :
  RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)}

def generate : RootGeneratedDualLatticePairingAt rootOccurrence
    leftOccurrences rightOccurrences pairingOccurrence :=
  ⟨RootGeneratedDualIncidenceAt.generate⟩

theorem core_preserves_occurrences
    (face : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    face.core.root = rootOccurrence ∧
      face.core.left = leftOccurrences ∧
      face.core.right = rightOccurrences ∧
      face.core.pairing = pairingOccurrence :=
  ⟨rfl, rfl, rfl, rfl⟩

def root
    (_face : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    RootedAccountedUnfolding Root :=
  rootOccurrence

def leftLattices
    (_face : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    Left → RootedAccountedUnfolding Left :=
  leftOccurrences

def rightLattices
    (_face : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    Right → RootedAccountedUnfolding Right :=
  rightOccurrences

def actualPairing
    (_face : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K) :=
  pairingOccurrence

/-- The pairing carried by the actual source occurrence, extended without a
caller-owned scalar pairing family. -/
noncomputable def scalarPairing
    (_face : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) :
    IntegralScalarExtension K Left →ₗ[K]
      IntegralScalarExtension K Right →ₗ[K] K :=
  scalarExtendDualPairing pairingOccurrence.root

end RootGeneratedDualLatticePairingAt

/-- Generated calculation receipt for two-sided separation.  This is a
dependent calculation face above the actual pairing occurrence, not source
data supplied to the determinant face. -/
structure RootGeneratedDualLatticeNondegeneracyCalculationAt
    {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
    [Field K] [Algebra ℤ K]
    [AddCommGroup Left]
    [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence :
      RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)}
    (pairingFace : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) : Prop where
  nondegenerate : pairingFace.scalarPairing.Nondegenerate

namespace RootGeneratedDualLatticeNondegeneracyCalculationAt

variable {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
variable [Field K] [Algebra ℤ K]
variable [AddCommGroup Left]
variable [AddCommGroup Right]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {leftOccurrences : Left → RootedAccountedUnfolding Left}
variable {rightOccurrences : Right → RootedAccountedUnfolding Right}
variable {pairingOccurrence :
  RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)}
variable {pairingFace : RootGeneratedDualLatticePairingAt rootOccurrence
  leftOccurrences rightOccurrences pairingOccurrence}

theorem generate (nondegenerate : pairingFace.scalarPairing.Nondegenerate) :
    RootGeneratedDualLatticeNondegeneracyCalculationAt pairingFace :=
  ⟨nondegenerate⟩

end RootGeneratedDualLatticeNondegeneracyCalculationAt

/-- Basis-free determinant face generated from the mixed pairing face. -/
structure RootGeneratedDualLatticeDeterminantTrivializationAt
    {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup Left]
    [AddCommGroup Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence :
      RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)}
    (pairingFace : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence) : Type where
  private mk ::

namespace RootGeneratedDualLatticeDeterminantTrivializationAt

variable {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
variable [CommRing K] [Algebra ℤ K]
variable [AddCommGroup Left]
variable [AddCommGroup Right]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {leftOccurrences : Left → RootedAccountedUnfolding Left}
variable {rightOccurrences : Right → RootedAccountedUnfolding Right}
variable {pairingOccurrence :
  RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)}
variable {pairingFace : RootGeneratedDualLatticePairingAt rootOccurrence
  leftOccurrences rightOccurrences pairingOccurrence}

def generate :
    RootGeneratedDualLatticeDeterminantTrivializationAt pairingFace :=
  ⟨⟩

def pairing
    (_face : RootGeneratedDualLatticeDeterminantTrivializationAt pairingFace) :
    RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence :=
  pairingFace

end RootGeneratedDualLatticeDeterminantTrivializationAt

/-- Realized derived arithmetic determinant state.  It consumes the generated
nondegeneracy receipt and exposes no constructor-owned frame or coordinate. -/
structure RootGeneratedDualLatticeDeterminantRealizationAt
    {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
    [Field K] [Algebra ℤ K]
    [AddCommGroup Left] [Module.Free ℤ Left]
    [Module.Finite ℤ Left]
    [AddCommGroup Right] [Module.Free ℤ Right]
    [Module.Finite ℤ Right]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {leftOccurrences : Left → RootedAccountedUnfolding Left}
    {rightOccurrences : Right → RootedAccountedUnfolding Right}
    {pairingOccurrence :
      RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)}
    {pairingFace : RootGeneratedDualLatticePairingAt rootOccurrence
      leftOccurrences rightOccurrences pairingOccurrence}
    (determinantFace :
      RootGeneratedDualLatticeDeterminantTrivializationAt pairingFace)
    (calculation :
      RootGeneratedDualLatticeNondegeneracyCalculationAt pairingFace) : Type where
  private mk ::

namespace RootGeneratedDualLatticeDeterminantRealizationAt

variable {K : Type t} {Root : Type w} {Left : Type u} {Right : Type v}
variable [Field K] [Algebra ℤ K]
variable [AddCommGroup Left] [Module.Free ℤ Left]
variable [Module.Finite ℤ Left]
variable [AddCommGroup Right] [Module.Free ℤ Right]
variable [Module.Finite ℤ Right]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {leftOccurrences : Left → RootedAccountedUnfolding Left}
variable {rightOccurrences : Right → RootedAccountedUnfolding Right}
variable {pairingOccurrence :
  RootedAccountedUnfolding (Left →ₗ[ℤ] Right →ₗ[ℤ] K)}
variable {pairingFace : RootGeneratedDualLatticePairingAt rootOccurrence
  leftOccurrences rightOccurrences pairingOccurrence}
variable {determinantFace :
  RootGeneratedDualLatticeDeterminantTrivializationAt pairingFace}
variable {calculation :
  RootGeneratedDualLatticeNondegeneracyCalculationAt pairingFace}

def realize : RootGeneratedDualLatticeDeterminantRealizationAt
    determinantFace calculation :=
  ⟨⟩

/-- The actual scalar pairing read from the source occurrence. -/
noncomputable def scalarPairing
    (_realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    IntegralScalarExtension K Left →ₗ[K]
      IntegralScalarExtension K Right →ₗ[K] K :=
  pairingFace.scalarPairing

theorem scalarPairing_nondegenerate
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    realization.scalarPairing.Nondegenerate :=
  calculation.nondegenerate

theorem leftToRightDual_injective
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    Function.Injective realization.scalarPairing := by
  rw [← LinearMap.ker_eq_bot]
  exact LinearMap.separatingLeft_iff_ker_eq_bot.mp
    realization.scalarPairing_nondegenerate.1

theorem rightToLeftDual_injective
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    Function.Injective realization.scalarPairing.flip := by
  rw [← LinearMap.ker_eq_bot]
  exact LinearMap.separatingRight_iff_flip_ker_eq_bot.mp
    realization.scalarPairing_nondegenerate.2

/-- Two-sided generated separation forces equality of the scalar ranks. -/
theorem scalarFinrank_eq
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    Module.finrank K (IntegralScalarExtension K Left) =
      Module.finrank K (IntegralScalarExtension K Right) := by
  apply le_antisymm
  · have rank_le := LinearMap.finrank_le_finrank_of_injective
      realization.leftToRightDual_injective
    simpa using rank_le
  · have rank_le := LinearMap.finrank_le_finrank_of_injective
      realization.rightToLeftDual_injective
    simpa using rank_le

/-- Pairing-induced equivalence from the left scalar lattice to the dual of
the right scalar lattice. -/
noncomputable def leftToRightDual
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    IntegralScalarExtension K Left ≃ₗ[K]
      Module.Dual K (IntegralScalarExtension K Right) :=
  LinearMap.linearEquivOfInjective realization.scalarPairing
    realization.leftToRightDual_injective (by
      simpa using realization.scalarFinrank_eq)

/-- Basis-free determinant-line equivalence generated by the mixed pairing. -/
noncomputable def determinantLineEquiv
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    TopExteriorLine K (IntegralScalarExtension K Left) ≃ₗ[K]
      TopExteriorLine K
        (Module.Dual K (IntegralScalarExtension K Right)) := by
  let lineMap := exteriorPower.map
    (Module.finrank K (IntegralScalarExtension K Left))
    realization.leftToRightDual.toLinearMap
  have lineMapBijective : Function.Bijective lineMap :=
    ⟨exteriorPower.map_injective_field realization.leftToRightDual.injective,
      exteriorPower.map_surjective realization.leftToRightDual.surjective⟩
  change
    (⋀[K]^(Module.finrank K (IntegralScalarExtension K Left))
        (IntegralScalarExtension K Left)) ≃ₗ[K]
      ⋀[K]^(Module.finrank K
        (Module.Dual K (IntegralScalarExtension K Right)))
        (Module.Dual K (IntegralScalarExtension K Right))
  rw [← realization.leftToRightDual.finrank_eq]
  exact LinearEquiv.ofBijective lineMap lineMapBijective

/-- The canonical determinant pairing
`det(Left_K) → det(Right_K)ᵛ`. -/
noncomputable def determinantLineMorphism
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    TopExteriorLine K (IntegralScalarExtension K Left) →ₗ[K]
      Module.Dual K (TopExteriorLine K
        (IntegralScalarExtension K Right)) := by
  let pairedDual := exteriorPower.pairingDual K
    (IntegralScalarExtension K Right)
    (Module.finrank K (IntegralScalarExtension K Right))
  have lineMap :
      TopExteriorLine K (IntegralScalarExtension K Left) →ₗ[K]
        ⋀[K]^(Module.finrank K (IntegralScalarExtension K Right))
          (Module.Dual K (IntegralScalarExtension K Right)) := by
    have map := realization.determinantLineEquiv.toLinearMap
    change
      (⋀[K]^(Module.finrank K (IntegralScalarExtension K Left))
          (IntegralScalarExtension K Left)) →ₗ[K]
        ⋀[K]^(Module.finrank K
          (Module.Dual K (IntegralScalarExtension K Right)))
          (Module.Dual K (IntegralScalarExtension K Right)) at map
    rw [Subspace.dual_finrank_eq] at map
    exact map
  exact pairedDual.comp lineMap

/-- The basis-free derived determinant state in its intrinsic tensor form. -/
noncomputable def determinantTensorMorphism
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation) :
    (TopExteriorLine K (IntegralScalarExtension K Left) ⊗[K]
      TopExteriorLine K (IntegralScalarExtension K Right)) →ₗ[K] K :=
  TensorProduct.lift realization.determinantLineMorphism

/-- A matrix exists only after installing independent left and right frames. -/
noncomputable def installedTwoFrameMatrix
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation)
    (leftBasis : Module.Basis Index K (IntegralScalarExtension K Left))
    (rightBasis : Module.Basis Index K (IntegralScalarExtension K Right)) :
    Matrix Index Index K :=
  LinearMap.toMatrix₂ leftBasis rightBasis realization.scalarPairing

/-- The scalar determinant/regulator coordinate in installed two frames. -/
noncomputable def installedTwoFrameDeterminantCoordinate
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation)
    (leftBasis : Module.Basis Index K (IntegralScalarExtension K Left))
    (rightBasis : Module.Basis Index K (IntegralScalarExtension K Right)) : K :=
  Matrix.det (realization.installedTwoFrameMatrix leftBasis rightBasis)

/-- Independent left/right frame changes act by `det(P) * det(Q)`. -/
theorem installedTwoFrameDeterminantCoordinate_change
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation)
    (oldLeft newLeft :
      Module.Basis Index K (IntegralScalarExtension K Left))
    (oldRight newRight :
      Module.Basis Index K (IntegralScalarExtension K Right)) :
    realization.installedTwoFrameDeterminantCoordinate newLeft newRight =
      Matrix.det (oldLeft.toMatrix newLeft) *
        Matrix.det (oldRight.toMatrix newRight) *
          realization.installedTwoFrameDeterminantCoordinate oldLeft oldRight := by
  unfold installedTwoFrameDeterminantCoordinate installedTwoFrameMatrix
  rw [← LinearMap.toMatrix₂_mul_basis_toMatrix oldLeft oldRight
      newLeft newRight realization.scalarPairing,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Integral frames are installed by canonical scalar extension. -/
noncomputable def installedIntegralLeftFrame
    {Index : Type*} (basis : Module.Basis Index ℤ Left) :
    Module.Basis Index K (IntegralScalarExtension K Left) :=
  basis.baseChange K

noncomputable def installedIntegralRightFrame
    {Index : Type*} (basis : Module.Basis Index ℤ Right) :
    Module.Basis Index K (IntegralScalarExtension K Right) :=
  basis.baseChange K

set_option linter.style.haveILetI false in
omit [Module.Free ℤ Left] [Module.Finite ℤ Left]
    [Module.Free ℤ Right] [Module.Finite ℤ Right] in
private theorem determinant_integralFrameChange
    {L : Type*} [AddCommGroup L]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (left right : Module.Basis Index ℤ L) :
    Matrix.det ((left.baseChange K).toMatrix (right.baseChange K)) = 1 ∨
      Matrix.det ((left.baseChange K).toMatrix (right.baseChange K)) = -1 := by
  have matrix_eq :
      (left.baseChange K).toMatrix (right.baseChange K) =
        (left.toMatrix right).map (algebraMap ℤ K) := by
    ext row column
    simp [Algebra.smul_def, Module.Basis.toMatrix_apply]
  have det_eq :
      Matrix.det ((left.toMatrix right).map (algebraMap ℤ K)) =
        algebraMap ℤ K (Matrix.det (left.toMatrix right)) := by
    exact (RingHom.map_det (algebraMap ℤ K)
      (left.toMatrix right)).symm
  rw [matrix_eq, det_eq]
  letI := Module.Basis.invertibleToMatrix left right
  obtain ⟨unit, unit_eq⟩ :=
    Matrix.isUnit_det_of_invertible (left.toMatrix right)
  rw [← unit_eq]
  rcases Int.units_eq_one_or unit with rfl | rfl <;> norm_num

/-- Two integral frame changes preserve the determinant coordinate up to the
intrinsic product of their two unit signs. -/
theorem installedIntegralTwoFrameCoordinate_unit
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation)
    (oldLeft newLeft : Module.Basis Index ℤ Left)
    (oldRight newRight : Module.Basis Index ℤ Right) :
    ∃ leftUnit rightUnit : K,
      (leftUnit = 1 ∨ leftUnit = -1) ∧
      (rightUnit = 1 ∨ rightUnit = -1) ∧
      realization.installedTwoFrameDeterminantCoordinate
          (newLeft.baseChange K) (newRight.baseChange K) =
        leftUnit * rightUnit *
          realization.installedTwoFrameDeterminantCoordinate
            (oldLeft.baseChange K) (oldRight.baseChange K) := by
  refine ⟨Matrix.det ((oldLeft.baseChange K).toMatrix
      (newLeft.baseChange K)),
    Matrix.det ((oldRight.baseChange K).toMatrix
      (newRight.baseChange K)), ?_, ?_, ?_⟩
  · exact determinant_integralFrameChange oldLeft newLeft
  · exact determinant_integralFrameChange oldRight newRight
  · exact realization.installedTwoFrameDeterminantCoordinate_change
      (oldLeft.baseChange K) (newLeft.baseChange K)
      (oldRight.baseChange K) (newRight.baseChange K)

/-- A polarization or isogeny installs a map from the left lattice into the
right lattice of one already generated dual arithmetic determinant state.
The face is a restriction/transport of that state: it does not carry a
second pairing or determinant occurrence. -/
structure RootGeneratedDualLatticePolarizedRestrictionAt
    (realization : RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation)
    (restrictionOccurrence :
      RootedAccountedUnfolding (Left →ₗ[ℤ] Right)) : Type where
  private mk ::

namespace RootGeneratedDualLatticePolarizedRestrictionAt

variable {realization : RootGeneratedDualLatticeDeterminantRealizationAt
  determinantFace calculation}
variable {restrictionOccurrence :
  RootedAccountedUnfolding (Left →ₗ[ℤ] Right)}

def generate : RootGeneratedDualLatticePolarizedRestrictionAt realization
    restrictionOccurrence :=
  ⟨⟩

/-- Every polarization restriction points definitionally to the same dual
arithmetic determinant state. -/
def determinantState
    (_restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence) :
    RootGeneratedDualLatticeDeterminantRealizationAt
      determinantFace calculation :=
  realization

def actualRestriction
    (_restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence) :
    RootedAccountedUnfolding (Left →ₗ[ℤ] Right) :=
  restrictionOccurrence

/-- Scalar extension of the actual polarization/isogeny map. -/
noncomputable def scalarRestriction
    (_restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence) :
    IntegralScalarExtension K Left →ₗ[K]
      IntegralScalarExtension K Right :=
  restrictionOccurrence.root.baseChange K

/-- The self-pairing seen through a polarization is derived by restricting
the right input of the intrinsic dual pairing. -/
noncomputable def restrictedSelfPairing
    (restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence) :
    LinearMap.BilinForm K (IntegralScalarExtension K Left) :=
  realization.scalarPairing.compl₂ restriction.scalarRestriction

/-- Basis-free determinant-line transport generated by the actual
polarization/isogeny map. -/
noncomputable def determinantLineTransport
    (restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence) :
    TopExteriorLine K (IntegralScalarExtension K Left) →ₗ[K]
      TopExteriorLine K (IntegralScalarExtension K Right) := by
  change
    (⋀[K]^(Module.finrank K (IntegralScalarExtension K Left))
      (IntegralScalarExtension K Left)) →ₗ[K]
    ⋀[K]^(Module.finrank K (IntegralScalarExtension K Right))
      (IntegralScalarExtension K Right)
  rw [← realization.scalarFinrank_eq]
  exact exteriorPower.map
    (Module.finrank K (IntegralScalarExtension K Left))
    restriction.scalarRestriction

/-- A single installed left frame reads the polarization-restricted
self-pairing. -/
noncomputable def installedRestrictedFrameMatrix
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence)
    (basis : Module.Basis Index K (IntegralScalarExtension K Left)) :
    Matrix Index Index K :=
  LinearMap.toMatrix₂ basis basis restriction.restrictedSelfPairing

noncomputable def installedRestrictedFrameCoordinate
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence)
    (basis : Module.Basis Index K (IntegralScalarExtension K Left)) : K :=
  Matrix.det (restriction.installedRestrictedFrameMatrix basis)

/-- Installing any reference frame on the right exposes the exact transport
law: the restricted matrix is the intrinsic dual matrix followed by the
polarization matrix. -/
theorem installedRestrictedFrameMatrix_eq_dual_mul_transport
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence)
    (leftBasis : Module.Basis Index K (IntegralScalarExtension K Left))
    (rightBasis : Module.Basis Index K (IntegralScalarExtension K Right)) :
    restriction.installedRestrictedFrameMatrix leftBasis =
      realization.installedTwoFrameMatrix leftBasis rightBasis *
        LinearMap.toMatrix leftBasis rightBasis
          restriction.scalarRestriction := by
  unfold installedRestrictedFrameMatrix restrictedSelfPairing
  unfold installedTwoFrameMatrix
  exact LinearMap.toMatrix₂_compl₂ leftBasis rightBasis leftBasis
    realization.scalarPairing restriction.scalarRestriction

/-- At scalar-coordinate level, a polarization contributes only its
determinant transport factor to the one intrinsic dual determinant state. -/
theorem installedRestrictedFrameCoordinate_eq_dual_mul_transport
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (restriction : RootGeneratedDualLatticePolarizedRestrictionAt realization
      restrictionOccurrence)
    (leftBasis : Module.Basis Index K (IntegralScalarExtension K Left))
    (rightBasis : Module.Basis Index K (IntegralScalarExtension K Right)) :
    restriction.installedRestrictedFrameCoordinate leftBasis =
      realization.installedTwoFrameDeterminantCoordinate
          leftBasis rightBasis *
        Matrix.det (LinearMap.toMatrix leftBasis rightBasis
          restriction.scalarRestriction) := by
  unfold installedRestrictedFrameCoordinate
  rw [restriction.installedRestrictedFrameMatrix_eq_dual_mul_transport,
    Matrix.det_mul]
  rfl

/-- Two polarization restrictions share the arithmetic determinant state;
only their transport occurrences differ. -/
theorem restrictions_share_determinantState
    {firstOccurrence secondOccurrence :
      RootedAccountedUnfolding (Left →ₗ[ℤ] Right)}
    (first : RootGeneratedDualLatticePolarizedRestrictionAt realization
      firstOccurrence)
    (second : RootGeneratedDualLatticePolarizedRestrictionAt realization
      secondOccurrence) :
    first.determinantState = second.determinantState :=
  rfl

end RootGeneratedDualLatticePolarizedRestrictionAt

/-- Strict self-dual matrix recovery: installing the same frame on both
sides gives exactly the former bilinear-form matrix. -/
theorem installedTwoFrameMatrix_self_eq
    {L : Type*} [AddCommGroup L]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (pairing : LinearMap.BilinMap ℤ L K)
    (basis : Module.Basis Index K (IntegralScalarExtension K L)) :
    LinearMap.toMatrix₂ basis basis (scalarExtendDualPairing pairing) =
      LinearMap.BilinForm.toMatrix basis (scalarExtendPairing pairing) := by
  rw [scalarExtendDualPairing_self_eq]
  rfl

/-- Strict self-dual scalar-coordinate recovery. -/
theorem installedTwoFrameDeterminantCoordinate_self_eq
    {L : Type*} [AddCommGroup L]
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (pairing : LinearMap.BilinMap ℤ L K)
    (basis : Module.Basis Index K (IntegralScalarExtension K L)) :
    Matrix.det (LinearMap.toMatrix₂ basis basis
      (scalarExtendDualPairing pairing)) =
      Matrix.det (LinearMap.BilinForm.toMatrix basis
        (scalarExtendPairing pairing)) := by
  rw [installedTwoFrameMatrix_self_eq pairing basis]

end RootGeneratedDualLatticeDeterminantRealizationAt

end DualLatticeDeterminant
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
