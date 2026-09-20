import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Finite
import H0mework.Realization.Arithmetic.NorthcottPositivity
import H0mework.Realization.Arithmetic.PolarizedPairing
import H0mework.Realization.Determinant.ExteriorLine

/-!
# Root-generated MW-free determinant-line trivialization

The cofinal quadratic state is first generated on the actual additive point
group.  Its polarization is therefore integer-bilinear.  Torsion lies in the
quadratic radical automatically, so the form descends canonically to the
Mordell--Weil free lattice `Point / torsion`.  Only then is that lattice
extended to the coefficient field and sent to its dual and top exterior line.

A matrix and its determinant appear only after a downstream consumer installs
a frame.  Neither is a field of any producer face.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace ResponsibilityLifecycle
namespace LivingLawEvolution
namespace ConstructiveRoot
namespace LatticeDeterminantTrivialization

open RootGeneratedExteriorDeterminantLine
open CofinalQuadraticEvaluation
open NorthcottLatticePositivity
open PolarizedPairing
open scoped InnerProductSpace TensorProduct

attribute [local instance 2000] Algebra.toModule

universe t u v w p q r

/-- Canonical torsion-free integral lattice generated from the additive point
group.  No complement or basis is chosen. -/
abbrev MWFreeLattice (Point : Type v) [AddCommGroup Point] :=
  Point ⧸ Submodule.torsion ℤ Point

/-- Scalar extension using the `ℤ → K` algebra module on the scalar factor.
The explicit abbreviation prevents accidental selection of an unrelated
integer-module instance. -/
abbrev IntegralScalarExtension
    (K : Type t) (L : Type v)
    [Ring K] [Algebra ℤ K]
    [AddCommGroup L] [Module ℤ L] : Type (max t v) :=
  @TensorProduct ℤ _ K L _ _ Algebra.toModule inferInstance

/-- Multiplication collapses the scalar-valued base change
`K ⊗ℤ K → K`. -/
def scalarMultiplication
    {K : Type t} [CommRing K] [Algebra ℤ K] :
    IntegralScalarExtension K K →ₗ[K] K :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.restrictScalarsₗ ℤ K K K K ∘ₗ LinearMap.lsmul K K)

/-- Canonical scalar extension of an integer-bilinear `K`-valued pairing. -/
def scalarExtendPairing
    {K : Type t} {L : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup L]
    (pairing : LinearMap.BilinMap ℤ L K) :
    LinearMap.BilinForm K (IntegralScalarExtension K L) :=
  (pairing.baseChange K).compr₂ scalarMultiplication

@[simp] theorem scalarExtendPairing_tmul
    {K : Type t} {L : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup L]
    (pairing : LinearMap.BilinMap ℤ L K)
    (leftScalar rightScalar : K) (left right : L) :
    scalarExtendPairing pairing
        (@TensorProduct.tmul ℤ _ K L _ _ Algebra.toModule inferInstance
          leftScalar left)
        (@TensorProduct.tmul ℤ _ K L _ _ Algebra.toModule inferInstance
          rightScalar right) =
      leftScalar * rightScalar * pairing left right := by
  simp [scalarExtendPairing, scalarMultiplication]

/-- Symmetry of the integral pairing survives scalar extension. -/
theorem scalarExtendPairing_symmetric_of_symmetric
    {K : Type t} {L : Type v}
    [CommRing K] [Algebra ℤ K]
    [AddCommGroup L]
    (pairing : LinearMap.BilinMap ℤ L K)
    (symmetric : ∀ left right, pairing left right = pairing right left)
    (left right : IntegralScalarExtension K L) :
    scalarExtendPairing pairing left right =
      scalarExtendPairing pairing right left := by
  induction left using TensorProduct.induction_on with
  | zero => simp
  | tmul leftScalar leftPoint =>
      induction right using TensorProduct.induction_on with
      | zero => simp
      | tmul rightScalar rightPoint =>
          simp only [scalarExtendPairing_tmul]
          rw [symmetric leftPoint rightPoint]
          ring
      | add right₁ right₂ induction₁ induction₂ =>
          simp only [map_add]
          simp only [LinearMap.add_apply, induction₁, induction₂]
  | add left₁ left₂ induction₁ induction₂ =>
      simp only [map_add]
      simp only [LinearMap.add_apply, induction₁, induction₂]

/-- For a symmetric bilinear pairing, a weighted Gram realization on the
diagonal generates the full two-variable commuting law by polarization.
Callers therefore need not restate the already generated pairing. -/
theorem scalarExtendPairing_eq_weightedGram_of_diagonal
    {L : Type v} {H : Type u}
    [AddCommGroup L]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (pairing : LinearMap.BilinMap ℤ L ℝ)
    (symmetric : ∀ left right, pairing left right = pairing right left)
    (weight : ℝ)
    (periodMap : IntegralScalarExtension ℝ L →ₗ[ℝ] H)
    (diagonal_commutes : ∀ point,
      scalarExtendPairing pairing point point =
        weight * ⟪periodMap point, periodMap point⟫_ℝ)
    (left right : IntegralScalarExtension ℝ L) :
    scalarExtendPairing pairing left right =
      weight * ⟪periodMap left, periodMap right⟫_ℝ := by
  have sumIdentity := diagonal_commutes (left + right)
  simp only [map_add, LinearMap.add_apply, inner_add_left,
    inner_add_right] at sumIdentity
  rw [scalarExtendPairing_symmetric_of_symmetric pairing symmetric right left,
    real_inner_comm (periodMap left) (periodMap right)] at sumIdentity
  have leftIdentity := diagonal_commutes left
  have rightIdentity := diagonal_commutes right
  linarith

/-- Positive definiteness of the scalar-extended diagonal generates
nondegeneracy of the pairing.  This is the preferred determinant mouth for
Archimedean height pairings: a domain proves positivity from its polarization,
while the generic kernel derives left and right separation. -/
theorem scalarExtendPairing_nondegenerate_of_posDef
    {K : Type t} {L : Type v}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra ℤ K]
    [AddCommGroup L]
    (pairing : LinearMap.BilinMap ℤ L K)
    (positive : (scalarExtendPairing pairing).toQuadraticMap.PosDef) :
    (scalarExtendPairing pairing).Nondegenerate := by
  constructor
  · intro point annihilates
    apply positive.anisotropic point
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    exact annihilates point
  · intro point annihilates
    apply positive.anisotropic point
    rw [LinearMap.BilinMap.toQuadraticMap_apply]
    exact annihilates point

/-- A source-generated injective period/polarization map whose pairing is a
positive multiple of a real Gram form generates positive definiteness. This
is the preferred geometry mouth above a raw `PosDef` proposition. -/
theorem scalarExtendPairing_posDef_of_weightedGram
    {L : Type v} {H : Type u}
    [AddCommGroup L]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (pairing : LinearMap.BilinMap ℤ L ℝ)
    (weight : ℝ) (weight_pos : 0 < weight)
    (periodMap : IntegralScalarExtension ℝ L →ₗ[ℝ] H)
    (periodMap_injective : Function.Injective periodMap)
    (gram_commutes : ∀ left right,
      scalarExtendPairing pairing left right =
        weight * ⟪periodMap left, periodMap right⟫_ℝ) :
    (scalarExtendPairing pairing).toQuadraticMap.PosDef := by
  intro point point_ne_zero
  rw [LinearMap.BilinMap.toQuadraticMap_apply,
    gram_commutes point point]
  apply mul_pos weight_pos
  rw [real_inner_self_pos]
  intro period_zero
  apply point_ne_zero
  exact periodMap_injective (period_zero.trans periodMap.map_zero.symm)

/-- Northcott finiteness and nonnegativity on a finite free integral lattice
generate positive definiteness after real scalar extension.  The chosen
bases below are internal calculation frames: the public conclusion is the
basis-free bilinear form, and no period or Gram realization is assumed. -/
theorem scalarExtendPairing_posDef_of_northcott
    {L : Type v} [AddCommGroup L] [Module.Finite ℤ L]
    [Module.IsTorsionFree ℤ L]
    (quadratic : QuadraticMap ℤ L ℝ) [Northcott quadratic]
    (quadratic_nonneg : ∀ point, 0 ≤ quadratic point) :
    (scalarExtendPairing quadratic.polarBilin).toQuadraticMap.PosDef := by
  let _ : Module.Free ℤ L := Module.free_of_finite_type_torsion_free'
  let integralBasis := Module.Free.chooseBasis ℤ L
  let realBasis := integralBasis.baseChange ℝ
  let coordinateBasis :=
    Pi.basisFun ℝ (Module.Free.ChooseBasisIndex ℤ L)
  let latticeBasis := coordinateBasis.restrictScalars ℤ
  let latticeEquiv : L ≃ₗ[ℤ]
      Submodule.span ℤ (Set.range coordinateBasis) :=
    integralBasis.equiv latticeBasis (Equiv.refl _)
  let height : Submodule.span ℤ (Set.range coordinateBasis) → ℝ :=
    fun point => quadratic (latticeEquiv.symm point)
  let heightNorthcott : Northcott height := by
    let _ : Filter.TendstoCofinite latticeEquiv.symm :=
      Filter.tendstoCofinite_of_injective latticeEquiv.symm.injective
    exact Northcott.comp_of_finite_fibers latticeEquiv.symm quadratic
  let _ : Northcott height := heightNorthcott
  let coordinatePairing : LinearMap.BilinForm ℝ
      (Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
    (scalarExtendPairing quadratic.polarBilin).comp
      realBasis.equivFun.symm.toLinearMap realBasis.equivFun.symm.toLinearMap
  let latticeCoordinateEmbedding : L →ₗ[ℤ]
      (Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
    (Submodule.subtype
      (Submodule.span ℤ (Set.range coordinateBasis))).comp
        latticeEquiv.toLinearMap
  let coordinateTensorEmbedding : L →ₗ[ℤ]
      IntegralScalarExtension ℝ L :=
    (realBasis.equivFun.symm.toLinearMap.restrictScalars ℤ).comp
      latticeCoordinateEmbedding
  have coordinateTensorEmbedding_eq :
      coordinateTensorEmbedding = TensorProduct.mk ℤ ℝ L 1 := by
    apply integralBasis.ext
    intro index
    simp [coordinateTensorEmbedding, latticeCoordinateEmbedding,
      latticeEquiv, latticeBasis, coordinateBasis, realBasis, integralBasis]
    rfl
  have coordinatePositive : coordinatePairing.toQuadraticMap.PosDef := by
    refine bilinForm_posDef_of_zspan_northcott coordinateBasis
      coordinatePairing ?_ height ?_ ?_
    · intro left right
      dsimp only [coordinatePairing]
      rw [LinearMap.BilinForm.comp_apply, LinearMap.BilinForm.comp_apply]
      exact scalarExtendPairing_symmetric_of_symmetric quadratic.polarBilin
        (fun first second => QuadraticMap.polar_comm quadratic first second)
        _ _
    · intro point
      let integralPoint := latticeEquiv.symm point
      have point_eq :
          realBasis.equivFun.symm (point :
            Module.Free.ChooseBasisIndex ℤ L → ℝ) =
            (1 : ℝ) ⊗ₜ[ℤ] integralPoint := by
        have point_lattice : latticeEquiv integralPoint = point := by
          simp [integralPoint]
        have point_coe :
            ((latticeEquiv integralPoint :
              Submodule.span ℤ (Set.range coordinateBasis)) :
                Module.Free.ChooseBasisIndex ℤ L → ℝ) =
              (point : Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
          congrArg Subtype.val point_lattice
        calc
          realBasis.equivFun.symm
              (point : Module.Free.ChooseBasisIndex ℤ L → ℝ) =
              realBasis.equivFun.symm
                ((latticeEquiv integralPoint :
                  Submodule.span ℤ (Set.range coordinateBasis)) :
                    Module.Free.ChooseBasisIndex ℤ L → ℝ) :=
            congrArg realBasis.equivFun.symm point_coe.symm
          _ = coordinateTensorEmbedding integralPoint := rfl
          _ = TensorProduct.mk ℤ ℝ L 1 integralPoint := by
            rw [coordinateTensorEmbedding_eq]
            rfl
          _ = (1 : ℝ) ⊗ₜ[ℤ] integralPoint := rfl
      dsimp only [coordinatePairing]
      rw [LinearMap.BilinForm.comp_apply]
      change
        scalarExtendPairing quadratic.polarBilin
          (realBasis.equivFun.symm (point :
            Module.Free.ChooseBasisIndex ℤ L → ℝ))
          (realBasis.equivFun.symm (point :
            Module.Free.ChooseBasisIndex ℤ L → ℝ)) =
          2 * quadratic integralPoint
      rw [point_eq, scalarExtendPairing_tmul]
      simp only [one_mul]
      change QuadraticMap.polar quadratic integralPoint integralPoint =
        2 * quadratic integralPoint
      rw [QuadraticMap.polar_self]
      simp [nsmul_eq_mul]
    · intro point
      exact quadratic_nonneg (latticeEquiv.symm point)
  intro point point_ne_zero
  change 0 < scalarExtendPairing quadratic.polarBilin point point
  have coordinate_ne_zero : realBasis.equivFun point ≠ 0 := by
    intro coordinate_zero
    apply point_ne_zero
    exact realBasis.equivFun.injective
      (coordinate_zero.trans realBasis.equivFun.map_zero.symm)
  have positive := coordinatePositive (realBasis.equivFun point)
    coordinate_ne_zero
  simpa [coordinatePairing] using positive

/-- Any torsion point lies in the radical of a `K`-valued integral quadratic
map when `K` has characteristic zero.  This is the generic MW-free descent,
not a domain-supplied quotient premise. -/
theorem torsion_le_quadraticRadical
    {K : Type t} {Point : Type v}
    [Field K] [CharZero K] [Algebra ℤ K]
    [AddCommGroup Point]
    (quadratic : QuadraticMap ℤ Point K) :
    Submodule.torsion ℤ Point ≤ quadratic.radical := by
  intro point point_torsion
  rcases point_torsion with ⟨integer, integer_point_eq_zero⟩
  change (integer : ℤ) • point = 0 at integer_point_eq_zero
  have integer_ne : (integer : ℤ) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp integer.property
  have integer_square_ne : (integer : ℤ) * integer ≠ 0 :=
    mul_ne_zero integer_ne integer_ne
  constructor
  · have scaled_q_eq_zero := congrArg quadratic integer_point_eq_zero
    rw [quadratic.map_smul, quadratic.map_zero] at scaled_q_eq_zero
    rw [Algebra.smul_def] at scaled_q_eq_zero
    exact (mul_eq_zero.mp scaled_q_eq_zero).resolve_left
      (by
        intro mapped_eq_zero
        rw [(algebraMap ℤ K).eq_intCast'] at mapped_eq_zero
        exact (Int.cast_ne_zero.mpr integer_square_ne) mapped_eq_zero)
  · apply LinearMap.ext
    intro other
    change quadratic.polarBilin point other = 0
    have scaled_pairing_eq_zero := congrArg
      (fun value => quadratic.polarBilin value other) integer_point_eq_zero
    rw [quadratic.polarBilin.map_smul₂, map_zero] at scaled_pairing_eq_zero
    rw [Algebra.smul_def] at scaled_pairing_eq_zero
    exact (mul_eq_zero.mp scaled_pairing_eq_zero).resolve_left
      (by
        intro mapped_eq_zero
        rw [(algebraMap ℤ K).eq_intCast'] at mapped_eq_zero
        exact (Int.cast_ne_zero.mpr integer_ne) mapped_eq_zero)

/-- The quadratic state descends canonically to the MW-free lattice. -/
noncomputable def mwFreeQuadraticState
    {K : Type t} {Point : Type v}
    [Field K] [CharZero K] [Algebra ℤ K]
    [AddCommGroup Point]
    (quadratic : QuadraticMap ℤ Point K) :
    QuadraticMap ℤ (MWFreeLattice Point) K :=
  quadratic.lift (Submodule.torsion ℤ Point)
    (torsion_le_quadraticRadical quadratic)

/-- Northcott finiteness descends to the canonical torsion quotient: every
MW-free sublevel is an image of the corresponding finite point sublevel. -/
theorem mwFreeQuadraticState_northcott
    {Point : Type v} [AddCommGroup Point]
    (quadratic : QuadraticMap ℤ Point ℝ) [Northcott quadratic] :
    Northcott (mwFreeQuadraticState quadratic) where
  finite_le := fun bound => by
    have source_finite :
        {point : Point | quadratic point ≤ bound}.Finite :=
      Northcott.finite_le (h := quadratic) bound
    refine (source_finite.image
      (fun point : Point =>
        (Submodule.Quotient.mk point : MWFreeLattice Point))).subset ?_
    intro point point_mem
    induction point using Quotient.inductionOn with
    | _ representative =>
        refine ⟨representative, ?_, rfl⟩
        change quadratic representative ≤ bound at point_mem
        exact point_mem

/-- Pointwise nonnegativity also descends through the same canonical
torsion quotient. -/
theorem mwFreeQuadraticState_nonneg
    {Point : Type v} [AddCommGroup Point]
    (quadratic : QuadraticMap ℤ Point ℝ)
    (nonnegative : ∀ point, 0 ≤ quadratic point)
    (point : MWFreeLattice Point) :
    0 ≤ mwFreeQuadraticState quadratic point := by
  induction point using Quotient.inductionOn with
  | _ representative => exact nonnegative representative

/-- The canonical integer pairing on the MW-free lattice. -/
noncomputable def mwFreePairing
    {K : Type t} {Point : Type v}
    [Field K] [CharZero K] [Algebra ℤ K]
    [AddCommGroup Point]
    (quadratic : QuadraticMap ℤ Point K) :
    LinearMap.BilinMap ℤ (MWFreeLattice Point) K :=
  (mwFreeQuadraticState quadratic).polarBilin

/-- A Northcott nonnegative quadratic producer on the actual point group
generates positive definiteness of its real MW-free scalar extension.  This
is the direct determinant mouth; no period map, Gram identity or caller-owned
positivity proposition remains. -/
theorem scalarExtendMWFreePairing_posDef_of_northcott
    {Point : Type v} [AddCommGroup Point] [Module.Finite ℤ Point]
    (quadratic : QuadraticMap ℤ Point ℝ) [Northcott quadratic]
    (nonnegative : ∀ point, 0 ≤ quadratic point) :
    (scalarExtendPairing (mwFreePairing quadratic)).toQuadraticMap.PosDef := by
  let freeQuadratic := mwFreeQuadraticState quadratic
  let freeNorthcott : Northcott freeQuadratic :=
    mwFreeQuadraticState_northcott quadratic
  let _ : Northcott freeQuadratic := freeNorthcott
  change
    (scalarExtendPairing freeQuadratic.polarBilin).toQuadraticMap.PosDef
  exact scalarExtendPairing_posDef_of_northcott freeQuadratic
    (mwFreeQuadraticState_nonneg quadratic nonnegative)

/-- If the generated quadratic state's zero fibre is exactly torsion, its
canonical MW-free descent has only the zero class in its zero fibre. -/
theorem mwFreeQuadraticState_eq_zero_iff_of_eq_zero_iff_torsion
    {K : Type t} {Point : Type v}
    [Field K] [CharZero K] [Algebra ℤ K]
    [AddCommGroup Point]
    (quadratic : QuadraticMap ℤ Point K)
    (zero_iff_torsion : ∀ point,
      quadratic point = 0 ↔ point ∈ Submodule.torsion ℤ Point)
    (point : MWFreeLattice Point) :
    mwFreeQuadraticState quadratic point = 0 ↔ point = 0 := by
  induction point using Quotient.inductionOn with
  | _ representative =>
      simp only [mwFreeQuadraticState]
      change quadratic representative = 0 ↔
        Submodule.Quotient.mk representative = 0
      rw [zero_iff_torsion representative,
        Submodule.Quotient.mk_eq_zero]

/-- Exact torsion zero fibre generates nondegeneracy of the integral MW-free
pairing; no pairing-level separation premise is supplied. -/
theorem mwFreePairing_nondegenerate_of_eq_zero_iff_torsion
    {K : Type t} {Point : Type v}
    [Field K] [CharZero K] [Algebra ℤ K]
    [AddCommGroup Point]
    (quadratic : QuadraticMap ℤ Point K)
    (zero_iff_torsion : ∀ point,
      quadratic point = 0 ↔ point ∈ Submodule.torsion ℤ Point) :
    (mwFreePairing quadratic).Nondegenerate := by
  have zero_iff :=
    mwFreeQuadraticState_eq_zero_iff_of_eq_zero_iff_torsion quadratic
      zero_iff_torsion
  constructor <;> intro point annihilates
  · have self_zero := annihilates point
    change QuadraticMap.polar (mwFreeQuadraticState quadratic)
      point point = 0 at self_zero
    rw [QuadraticMap.polar_self] at self_zero
    have quadratic_zero : mwFreeQuadraticState quadratic point = 0 := by
      have doubled : (2 : K) * mwFreeQuadraticState quadratic point = 0 := by
        simpa [nsmul_eq_mul] using self_zero
      exact (mul_eq_zero.mp doubled).resolve_left (by norm_num)
    exact (zero_iff point).mp quadratic_zero
  · have self_zero := annihilates point
    change QuadraticMap.polar (mwFreeQuadraticState quadratic)
      point point = 0 at self_zero
    rw [QuadraticMap.polar_self] at self_zero
    have quadratic_zero : mwFreeQuadraticState quadratic point = 0 := by
      have doubled : (2 : K) * mwFreeQuadraticState quadratic point = 0 := by
        simpa [nsmul_eq_mul] using self_zero
      exact (mul_eq_zero.mp doubled).resolve_left (by norm_num)
    exact (zero_iff point).mp quadratic_zero

/-- Structural determinant-line face generated from the exact pairing face.
Its lattice is definitionally the same point group's torsion quotient; the
face stores no lattice choice, basis, matrix, nondegeneracy proof or scalar
regulator. -/
structure RootGeneratedLatticeDeterminantTrivializationAt
    {Root : Type w} {Polarization : Type q} {Point : Type v}
    {Orbit : Type r} {Incidence : Type p}
    {rootOccurrence : RootedAccountedUnfolding Root}
    {polarizationOccurrence : RootedAccountedUnfolding Polarization}
    {pointOccurrences : Point → RootedAccountedUnfolding Point}
    {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
    {localIncidenceOccurrence : Point → RootedAccountedUnfolding Incidence}
    {evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence}
    (pairingFace : RootGeneratedPolarizedPairingAt evaluationFace) : Type where
  private mk ::

namespace RootGeneratedLatticeDeterminantTrivializationAt

variable {Root : Type w} {Polarization : Type q} {Point : Type v}
variable {Orbit : Type r} {Incidence : Type p}
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {polarizationOccurrence : RootedAccountedUnfolding Polarization}
variable {pointOccurrences : Point → RootedAccountedUnfolding Point}
variable {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
variable {localIncidenceOccurrence : Point → RootedAccountedUnfolding Incidence}
variable {evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt
  rootOccurrence polarizationOccurrence pointOccurrences
  multiplicationOrbitOccurrence localIncidenceOccurrence}
variable {pairingFace : RootGeneratedPolarizedPairingAt evaluationFace}

def generate :
    RootGeneratedLatticeDeterminantTrivializationAt pairingFace :=
  ⟨⟩

end RootGeneratedLatticeDeterminantTrivializationAt

/-- T1 realization of the determinant-line face.  Finite generation of the
actual point group makes its torsion quotient a finite free integral lattice;
the only mathematical mouth beyond the generated pairing is nondegeneracy of
its scalar extension. -/
structure RootGeneratedLatticeDeterminantTrivializationRealizationAt
    {K : Type t} {Root : Type w} {Point : Type v}
    {Polarization : Type q} {Orbit : Type r} {Incidence : Type p}
    [NontriviallyNormedField K] [CompleteSpace K]
    [CharZero K] [Algebra ℤ K]
    [AddCommGroup Point] [Module.Finite ℤ Point]
    {rootOccurrence : RootedAccountedUnfolding Root}
    {polarizationOccurrence : RootedAccountedUnfolding Polarization}
    {pointOccurrences : Point → RootedAccountedUnfolding Point}
    {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
    {localIncidenceOccurrence : Point → RootedAccountedUnfolding Incidence}
    {evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt rootOccurrence
      polarizationOccurrence pointOccurrences multiplicationOrbitOccurrence
      localIncidenceOccurrence}
    {recurrence : CofinalQuadraticRecurrence K Orbit Point Incidence}
    {evaluationRealization :
      RootGeneratedCofinalQuadraticRealizationAt evaluationFace recurrence}
    {pairingFace : RootGeneratedPolarizedPairingAt evaluationFace}
    (pairingRealization : RootGeneratedPolarizedPairingRealizationAt
      pairingFace evaluationRealization)
    (determinantFace :
      RootGeneratedLatticeDeterminantTrivializationAt pairingFace)
    (nondegenerate :
      (scalarExtendPairing
        (mwFreePairing evaluationRealization.quadraticState)).Nondegenerate) : Type where
  private mk ::

namespace RootGeneratedLatticeDeterminantTrivializationRealizationAt

variable {K : Type t} {Root : Type w} {Point : Type v}
variable {Polarization : Type q} {Orbit : Type r} {Incidence : Type p}
variable [NontriviallyNormedField K] [CompleteSpace K]
variable [CharZero K] [Algebra ℤ K]
variable [AddCommGroup Point] [Module.Finite ℤ Point]
variable {rootOccurrence : RootedAccountedUnfolding Root}
variable {polarizationOccurrence : RootedAccountedUnfolding Polarization}
variable {pointOccurrences : Point → RootedAccountedUnfolding Point}
variable {multiplicationOrbitOccurrence : RootedAccountedUnfolding Orbit}
variable {localIncidenceOccurrence : Point → RootedAccountedUnfolding Incidence}
variable {evaluationFace : RootGeneratedCofinalQuadraticEvaluationAt
  rootOccurrence polarizationOccurrence pointOccurrences
  multiplicationOrbitOccurrence localIncidenceOccurrence}
variable {recurrence : CofinalQuadraticRecurrence K Orbit Point Incidence}
variable {evaluationRealization :
  RootGeneratedCofinalQuadraticRealizationAt evaluationFace recurrence}
variable {pairingFace : RootGeneratedPolarizedPairingAt evaluationFace}
variable {pairingRealization : RootGeneratedPolarizedPairingRealizationAt
  pairingFace evaluationRealization}
variable {determinantFace :
  RootGeneratedLatticeDeterminantTrivializationAt pairingFace}
variable {nondegenerate :
  (scalarExtendPairing
    (mwFreePairing evaluationRealization.quadraticState)).Nondegenerate}

def realize :
    RootGeneratedLatticeDeterminantTrivializationRealizationAt
      pairingRealization determinantFace nondegenerate :=
  ⟨⟩

/-- Preferred Archimedean constructor: positivity generated by the
polarization is the mathematical input, and nondegeneracy is produced by the
generic kernel. -/
def realizeOfPositiveDefinite
    [LinearOrder K] [IsStrictOrderedRing K]
    (positive :
      (scalarExtendPairing
        (mwFreePairing evaluationRealization.quadraticState)).toQuadraticMap.PosDef) :
    RootGeneratedLatticeDeterminantTrivializationRealizationAt
      pairingRealization determinantFace
        (scalarExtendPairing_nondegenerate_of_posDef
          (mwFreePairing evaluationRealization.quadraticState) positive) :=
  ⟨⟩

/-- The generated pairing on the scalar extension of the canonical MW-free
lattice. -/
noncomputable def latticePairing
    (_realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate) :
    LinearMap.BilinForm K
      (IntegralScalarExtension K (MWFreeLattice Point)) :=
  scalarExtendPairing
    (mwFreePairing evaluationRealization.quadraticState)

theorem latticePairing_nondegenerate
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate) :
    realization.latticePairing.Nondegenerate :=
  nondegenerate

/-- Pairing-induced equivalence from the scalar-extended MW-free lattice to
its dual. -/
noncomputable def pairingToDual
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate) :
    IntegralScalarExtension K (MWFreeLattice Point) ≃ₗ[K]
      Module.Dual K (IntegralScalarExtension K (MWFreeLattice Point)) :=
  realization.latticePairing.toDual realization.latticePairing_nondegenerate

/-- Basis-free determinant-line morphism generated by the lattice pairing. -/
noncomputable def determinantLineMorphism
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate) :
    TopExteriorLine K
        (IntegralScalarExtension K (MWFreeLattice Point)) →ₗ[K]
      ⋀[K]^(Module.finrank K
        (IntegralScalarExtension K (MWFreeLattice Point)))
        (Module.Dual K
          (IntegralScalarExtension K (MWFreeLattice Point))) :=
  exteriorPower.map
    (Module.finrank K (IntegralScalarExtension K (MWFreeLattice Point)))
    realization.pairingToDual.toLinearMap

/-- Nondegeneracy upgrades the determinant-line morphism to its generated
trivialization. -/
noncomputable def determinantLineTrivialization
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate) :
    TopExteriorLine K
        (IntegralScalarExtension K (MWFreeLattice Point)) ≃ₗ[K]
      ⋀[K]^(Module.finrank K
        (IntegralScalarExtension K (MWFreeLattice Point)))
        (Module.Dual K
          (IntegralScalarExtension K (MWFreeLattice Point))) := by
  let dualEquiv := realization.pairingToDual
  let lineMap :=
    exteriorPower.map
      (Module.finrank K (IntegralScalarExtension K (MWFreeLattice Point)))
      dualEquiv.toLinearMap
  exact LinearEquiv.ofBijective lineMap
    ⟨exteriorPower.map_injective_field dualEquiv.injective,
      exteriorPower.map_surjective dualEquiv.surjective⟩

/-- Matrix installed only by a selected downstream frame. -/
noncomputable def installedFrameMatrix
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate)
    (basis : Module.Basis Index K
      (IntegralScalarExtension K (MWFreeLattice Point))) :
    Matrix Index Index K :=
  LinearMap.BilinForm.toMatrix basis realization.latticePairing

/-- Regulator coordinate in a selected frame. -/
noncomputable def regulatorCoordinate
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate)
    (basis : Module.Basis Index K
      (IntegralScalarExtension K (MWFreeLattice Point))) : K :=
  Matrix.det (realization.installedFrameMatrix basis)

/-- An arbitrary frame change acts on the scalar regulator coordinate by the
square of its determinant. This is a readout law, not a basis-independence
premise. -/
theorem regulatorCoordinate_change
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate)
    (left right : Module.Basis Index K
      (IntegralScalarExtension K (MWFreeLattice Point))) :
    realization.regulatorCoordinate right =
      Matrix.det (left.toMatrix right) *
        Matrix.det (left.toMatrix right) *
          realization.regulatorCoordinate left := by
  unfold regulatorCoordinate installedFrameMatrix
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix
      (b := left) right realization.latticePairing,
    Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  ring

/-- Integral bases install real/scalar frames by canonical base change. -/
noncomputable def installedIntegralFrame
    {Index : Type*}
    (basis : Module.Basis Index ℤ (MWFreeLattice Point)) :
    Module.Basis Index K
      (IntegralScalarExtension K (MWFreeLattice Point)) :=
  basis.baseChange K

set_option linter.style.haveILetI false in
omit [CompleteSpace K] [CharZero K] [Module.Finite ℤ Point] in
private theorem determinant_integralFrameChange_sq
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (left right : Module.Basis Index ℤ (MWFreeLattice Point)) :
    Matrix.det ((left.baseChange K).toMatrix (right.baseChange K)) *
        Matrix.det ((left.baseChange K).toMatrix (right.baseChange K)) = 1 := by
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

/-- Regulator coordinates in any two integral Mordell--Weil bases are equal.
The basis-independence proof is generated by the determinant functor and the
integer unit law; a domain never supplies it. -/
theorem regulatorCoordinate_integralBasis_independent
    {Index : Type*} [Fintype Index] [DecidableEq Index]
    (realization :
      RootGeneratedLatticeDeterminantTrivializationRealizationAt
        pairingRealization determinantFace nondegenerate)
    (left right : Module.Basis Index ℤ (MWFreeLattice Point)) :
    realization.regulatorCoordinate (left.baseChange K) =
      realization.regulatorCoordinate (right.baseChange K) := by
  rw [realization.regulatorCoordinate_change (left.baseChange K)
    (right.baseChange K), determinant_integralFrameChange_sq, one_mul]

end RootGeneratedLatticeDeterminantTrivializationRealizationAt

end LatticeDeterminantTrivialization
end ConstructiveRoot
end LivingLawEvolution
end ResponsibilityLifecycle
end SaturationMonoid
