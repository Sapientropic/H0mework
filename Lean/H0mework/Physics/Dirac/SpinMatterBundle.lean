import H0mework.Physics.Jets.StageEightFirstJet
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# Stage-9A nontrivial Spin action and physical matter bundle

`Spin⁺(1,3)` is represented by its standard `SL(2,ℂ)` matrix model.  This
module constructs the chiral Dirac representation

`g ↦ diag(g, (g†)⁻¹)`

on the existing four-component Dirac index, proves its group law, combines it
with the actual Stage-7 mother-SU(7) representation, and glues the existing
`DiracExteriorMatterCarrier` through the generated total transition.

The resulting associated bundle is no longer an internal-only matter bundle:
the Spin factor acts nontrivially.  The formal covering homomorphism to the
proper orthochronous Lorentz group and smooth spin-connection overlap descent
remain the final S9-A boundary.
-/

namespace SaturationMonoid.PhysicsCore.StageNineSpinMatterBundle

open DiracCliffordRepresentation
open DiracExteriorMatterAction
open SU7ExteriorMatterRepresentation
open SU7ExteriorBreakingYukawa
open StageNineEnrichedProofFreeSource
open StageNineGlobalBundle
open StageNineAssociatedBundles

open scoped MatrixGroups

noncomputable section

abbrev WeylSpinorIndex := Fin 2 ⊕ Fin 2

/-- Right-handed Weyl matrix `(g†)⁻¹ = (g⁻¹)†`. -/
def rightWeylMatrix (groupElement : SpinPlus13) : Matrix (Fin 2) (Fin 2) ℂ :=
  star (((groupElement⁻¹ : SpinPlus13) : Matrix (Fin 2) (Fin 2) ℂ))

@[simp] theorem rightWeylMatrix_one : rightWeylMatrix 1 = 1 := by
  simp [rightWeylMatrix]

theorem rightWeylMatrix_mul (first second : SpinPlus13) :
    rightWeylMatrix (first * second) =
      rightWeylMatrix first * rightWeylMatrix second := by
  simp [rightWeylMatrix, mul_inv_rev, star_mul]

def weylDiracBlockMatrix
    (groupElement : SpinPlus13) : Matrix WeylSpinorIndex WeylSpinorIndex ℂ :=
  Matrix.fromBlocks
    (groupElement : Matrix (Fin 2) (Fin 2) ℂ) 0 0
    (rightWeylMatrix groupElement)

@[simp] theorem weylDiracBlockMatrix_one : weylDiracBlockMatrix 1 = 1 := by
  ext row column
  rcases row with row | row <;> rcases column with column | column <;>
    simp [weylDiracBlockMatrix, Matrix.fromBlocks, Matrix.one_apply]

theorem weylDiracBlockMatrix_mul (first second : SpinPlus13) :
    weylDiracBlockMatrix (first * second) =
      weylDiracBlockMatrix first * weylDiracBlockMatrix second := by
  rw [weylDiracBlockMatrix, weylDiracBlockMatrix, weylDiracBlockMatrix]
  ext row column
  rcases row with row | row <;> rcases column with column | column <;>
    simp [Matrix.fromBlocks_multiply, rightWeylMatrix_mul]

def spinDiracMatrix (groupElement : SpinPlus13) : DiracMatrix :=
  Matrix.reindexRingEquiv ℂ finSumFinEquiv
    (weylDiracBlockMatrix groupElement)

@[simp] theorem spinDiracMatrix_one : spinDiracMatrix 1 = 1 := by
  simp [spinDiracMatrix]

theorem spinDiracMatrix_mul (first second : SpinPlus13) :
    spinDiracMatrix (first * second) =
      spinDiracMatrix first * spinDiracMatrix second := by
  rw [spinDiracMatrix, spinDiracMatrix, spinDiracMatrix,
    weylDiracBlockMatrix_mul, map_mul]

/-- Actual nontrivial Spin action on the existing Stage-8 Dirac matter
carrier. -/
def spinDiracMatterRepresentation :
    Representation ℂ SpinPlus13 DiracExteriorMatterCarrier where
  toFun groupElement := diracMatrixMatterAction (spinDiracMatrix groupElement)
  map_one' := by
    rw [spinDiracMatrix_one]
    apply LinearMap.ext
    intro field
    funext row
    simp [diracMatrixMatterAction, Matrix.one_apply]
  map_mul' first second := by
    rw [spinDiracMatrix_mul, diracMatrixMatterAction_mul]
    rfl

/-- Spin and internal mother actions commute because they act on different
indices. -/
theorem spinDiracMatter_commutes_internal
    (spinElement : SpinPlus13) (motherElement : SU7MotherGroup) :
    (spinDiracMatterRepresentation spinElement).comp
        (diracExteriorMatterGaugeRepresentation motherElement) =
      (diracExteriorMatterGaugeRepresentation motherElement).comp
        (spinDiracMatterRepresentation spinElement) :=
  diracMatrixMatterAction_commutes_internal
    (spinDiracMatrix spinElement)
    (su7ExteriorSpinorMatterRepresentation motherElement)

/-- Physical total representation on the exact Stage-8 Dirac-exterior
carrier. -/
def totalDiracExteriorMatterRepresentation :
    Representation ℂ TotalStructureGroup DiracExteriorMatterCarrier where
  toFun totalElement :=
    (spinDiracMatterRepresentation totalElement.1).comp
      (diracExteriorMatterGaugeRepresentation totalElement.2)
  map_one' := by
    change
      (spinDiracMatterRepresentation (1 : SpinPlus13)).comp
          (diracExteriorMatterGaugeRepresentation (1 : SU7MotherGroup)) = 1
    rw [map_one, map_one]
    rfl
  map_mul' first second := by
    change
      (spinDiracMatterRepresentation (first.1 * second.1)).comp
          (diracExteriorMatterGaugeRepresentation (first.2 * second.2)) =
        ((spinDiracMatterRepresentation first.1).comp
          (diracExteriorMatterGaugeRepresentation first.2)).comp
            ((spinDiracMatterRepresentation second.1).comp
              (diracExteriorMatterGaugeRepresentation second.2))
    rw [map_mul, map_mul]
    apply LinearMap.ext
    intro field
    change
      spinDiracMatterRepresentation first.1
          (spinDiracMatterRepresentation second.1
            (diracExteriorMatterGaugeRepresentation first.2
              (diracExteriorMatterGaugeRepresentation second.2 field))) =
        spinDiracMatterRepresentation first.1
          (diracExteriorMatterGaugeRepresentation first.2
            (spinDiracMatterRepresentation second.1
              (diracExteriorMatterGaugeRepresentation second.2 field)))
    exact congrArg (spinDiracMatterRepresentation first.1)
      (LinearMap.congr_fun
        (spinDiracMatter_commutes_internal second.1 first.2)
        (diracExteriorMatterGaugeRepresentation second.2 field))

abbrev PhysicalDiracMatterAssociatedBundle
    (source : SmoothUnifiedSource) :=
  GluedAssociatedBundle totalDiracExteriorMatterRepresentation source

/-- A concrete nonidentity `SL(2,ℂ)` element. -/
def spinDilation : SpinPlus13 := by
  refine ⟨Matrix.diagonal ![(2 : ℂ), (1 / 2 : ℂ)], ?_⟩
  norm_num [Matrix.det_fin_two]

theorem spinDilation_dirac_entry :
    spinDiracMatrix spinDilation 0 0 = 2 := by
  rw [show (0 : Fin 4) = Fin.castAdd 2 (0 : Fin 2) by rfl]
  norm_num [spinDiracMatrix, Matrix.reindexRingEquiv,
    Matrix.reindexAddEquiv, Matrix.reindex, Matrix.submatrix,
    finSumFinEquiv, weylDiracBlockMatrix, spinDilation,
    Matrix.fromBlocks, Fin.addCases_left]

theorem spinDiracMatrix_nontrivial : spinDiracMatrix spinDilation ≠ 1 := by
  intro equality
  have entry := congrArg (fun matrix : DiracMatrix => matrix 0 0) equality
  rw [spinDilation_dirac_entry] at entry
  norm_num at entry

/-- S9-A5 positive checkpoint: the same generated total transition glues the
physical Dirac-exterior carrier, and its Spin representation is nontrivial. -/
theorem positiveSource_generates_physicalSpinMatterBundle :
    Nonempty
        (PhysicalDiracMatterAssociatedBundle positiveSmoothUnifiedSource) ∧
      spinDiracMatrix spinDilation ≠ 1 :=
  ⟨⟨associatedLocalPoint totalDiracExteriorMatterRepresentation
      positiveSmoothUnifiedSource 0 0 0⟩,
    spinDiracMatrix_nontrivial⟩

def trivialSpinMatrixAction (_groupElement : SpinPlus13) : DiracMatrix := 1

/-- Negative regression: the generated chiral Spin action cannot be replaced
by a hand-filled identity action. -/
theorem trivialSpinMatrixAction_rejected :
    trivialSpinMatrixAction ≠ spinDiracMatrix := by
  intro actionEquality
  have atDilation := congrFun actionEquality spinDilation
  exact spinDiracMatrix_nontrivial atDilation.symm

end

end SaturationMonoid.PhysicsCore.StageNineSpinMatterBundle
