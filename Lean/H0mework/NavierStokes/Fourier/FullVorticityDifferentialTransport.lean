import H0mework.NavierStokes.Fourier.FullVorticityStretching
import H0mework.NavierStokes.Fourier.LocalEnergyFluxTransport

/-!
# Differential transport of full three-dimensional vorticity

This module proves the differential identities needed to transport the
full right-handed vorticity field through periodic-cell and viscous PDE
readouts.  In particular, curl preserves the actual lattice, is
divergence-free, kills pressure gradients, and commutes with the vector
Laplacian at `C³` regularity.

These are generic PDE transport/readout theorems.  They do not generate a
velocity field, pressure, trajectory, or regularity estimate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicFullVorticityDifferentialTransport

open scoped Laplacian

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseVectorCalculus
open ThreeDimensionalPeriodicFullVorticityStretching
open ThreeDimensionalPeriodicLocalEnergyFluxTransport

noncomputable section

abbrev Velocity := PhysicalSpace

abbrev VelocityField := PhysicalSpace → Velocity

abbrev ScalarField := PhysicalSpace → ℝ

private def coordinateDirection (i : Coordinate) : PhysicalSpace :=
  EuclideanSpace.single i 1

/-! ## Regularity and lattice transport -/

/-- A `C³` velocity has a `C²` full vorticity field. -/
theorem vorticityField_contDiff_two
    (u : VelocityField) (hu : ContDiff ℝ 3 u) :
    ContDiff ℝ 2 (vorticityField u) := by
  have hDerivative :
      ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (m := 2) (by norm_num)
  change ContDiff ℝ 2
    (vorticityReadout ∘ fderiv ℝ u)
  exact vorticityReadout.contDiff.comp hDerivative

/-- Curl preserves the actual unit-lattice translation law. -/
theorem vorticityField_latticePeriodic
    (u : VelocityField) (hu : LatticePeriodic u) :
    LatticePeriodic (vorticityField u) := by
  intro z x
  unfold vorticityField
  rw [fderiv_latticePeriodic u hu z x]

/-! ## Linear differential transport -/

theorem vorticityField_sub
    (u v : VelocityField)
    (hu : Differentiable ℝ u)
    (hv : Differentiable ℝ v) :
    vorticityField (u - v) =
      vorticityField u - vorticityField v := by
  rw [sub_eq_add_neg,
    vorticityField_add u (-v) hu hv.neg,
    vorticityField_neg]
  rfl

theorem vorticityField_const_smul
    (c : ℝ) (u : VelocityField) :
    vorticityField (c • u) = c • vorticityField u := by
  funext x
  simp only [vorticityField, Pi.smul_apply]
  rw [congrFun (fderiv_const_smul_field c) x]
  simp only [Pi.smul_apply, map_smul]

/-! ## Divergence of curl -/

/-- Every `C²` full vorticity field is divergence-free. -/
theorem velocityDivergence_vorticityField_eq_zero
    (u : VelocityField) (hu : ContDiff ℝ 2 u) :
    velocityDivergence (vorticityField u) = 0 := by
  funext x
  have hSymmetric :
      IsSymmSndFDerivAt ℝ u x :=
    hu.contDiffAt.isSymmSndFDerivAt (by norm_num)
  change
    (∑ i : Coordinate,
      fderiv ℝ (vorticityField u) x (coordinateDirection i) i) = 0
  rw [fderiv_vorticityField u hu x]
  simp only [ContinuousLinearMap.comp_apply,
    vorticityReadout_apply, Fin.sum_univ_three,
    coordinateDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  rw [hSymmetric
      (EuclideanSpace.single (0 : Coordinate) 1)
      (EuclideanSpace.single (1 : Coordinate) 1),
    hSymmetric
      (EuclideanSpace.single (1 : Coordinate) 1)
      (EuclideanSpace.single (2 : Coordinate) 1),
    hSymmetric
      (EuclideanSpace.single (2 : Coordinate) 1)
      (EuclideanSpace.single (0 : Coordinate) 1)]
  ring

/-! ## Curl of a pressure gradient -/

private theorem fderiv_scalarGradient
    (p : ScalarField) (hp : ContDiff ℝ 2 p)
    (x : PhysicalSpace) :
    fderiv ℝ (scalarGradient p) x =
      scalarGradientReadout.comp
        (fderiv ℝ (fderiv ℝ p) x) := by
  have hDerivative :
      ContDiff ℝ 1 (fderiv ℝ p) :=
    hp.fderiv_right (m := 1) (by norm_num)
  change fderiv ℝ
      (scalarGradientReadout ∘ fderiv ℝ p) x = _
  rw [fderiv_comp x scalarGradientReadout.differentiableAt
    (hDerivative.differentiable_one x)]
  rw [ContinuousLinearMap.fderiv]

/-- The right-handed curl annihilates every `C²` pressure gradient. -/
theorem vorticityField_scalarGradient_eq_zero
    (p : ScalarField) (hp : ContDiff ℝ 2 p) :
    vorticityField (scalarGradient p) = 0 := by
  funext x
  have hSymmetric :
      IsSymmSndFDerivAt ℝ p x :=
    hp.contDiffAt.isSymmSndFDerivAt (by norm_num)
  rw [vorticityField, fderiv_scalarGradient p hp x]
  ext i
  fin_cases i
  · change
      fderiv ℝ (fderiv ℝ p) x
          (coordinateDirection 1) (coordinateDirection 2) -
        fderiv ℝ (fderiv ℝ p) x
          (coordinateDirection 2) (coordinateDirection 1) = 0
    rw [hSymmetric (coordinateDirection 1) (coordinateDirection 2)]
    ring
  · change
      fderiv ℝ (fderiv ℝ p) x
          (coordinateDirection 2) (coordinateDirection 0) -
        fderiv ℝ (fderiv ℝ p) x
          (coordinateDirection 0) (coordinateDirection 2) = 0
    rw [hSymmetric (coordinateDirection 2) (coordinateDirection 0)]
    ring
  · change
      fderiv ℝ (fderiv ℝ p) x
          (coordinateDirection 0) (coordinateDirection 1) -
        fderiv ℝ (fderiv ℝ p) x
          (coordinateDirection 1) (coordinateDirection 0) = 0
    rw [hSymmetric (coordinateDirection 0) (coordinateDirection 1)]
    ring

/-! ## Curl and the vector Laplacian -/

private noncomputable def secondDerivativeEvaluation
    (a b : PhysicalSpace) :
    SecondVelocityDerivative →L[ℝ] Velocity :=
  (ContinuousLinearMap.apply ℝ Velocity b) ∘L
    (ContinuousLinearMap.apply ℝ
      (PhysicalSpace →L[ℝ] Velocity) a)

@[simp] private theorem secondDerivativeEvaluation_apply
    (a b : PhysicalSpace) (H : SecondVelocityDerivative) :
    secondDerivativeEvaluation a b H = H a b :=
  rfl

private theorem fderiv_secondDerivative_apply
    (u : VelocityField) (hu : ContDiff ℝ 3 u)
    (x d a b : PhysicalSpace) :
    fderiv ℝ
        (fun y => fderiv ℝ (fderiv ℝ u) y a b) x d =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x d a b := by
  have hFirstDerivative :
      ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (m := 2) (by norm_num)
  have hSecondDerivative :
      ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    hFirstDerivative.fderiv_right (m := 1) (by norm_num)
  change fderiv ℝ
      (secondDerivativeEvaluation a b ∘
        fderiv ℝ (fderiv ℝ u)) x d = _
  rw [fderiv_comp x
    (secondDerivativeEvaluation a b).differentiableAt
    (hSecondDerivative.differentiable_one x)]
  rw [ContinuousLinearMap.fderiv]
  rfl

private theorem thirdDerivative_swap_last
    (u : VelocityField) (hu : ContDiff ℝ 3 u)
    (x d a b : PhysicalSpace) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x d a b =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x d b a := by
  have hSecondSymmetry :
      (fun y => fderiv ℝ (fderiv ℝ u) y a b) =
        fun y => fderiv ℝ (fderiv ℝ u) y b a := by
    funext y
    exact
      (hu.contDiffAt.isSymmSndFDerivAt (by norm_num)) a b
  have hDerivative := congrArg
    (fun f : PhysicalSpace → Velocity => fderiv ℝ f x)
    hSecondSymmetry
  have hApply := congrArg
    (fun D : PhysicalSpace →L[ℝ] Velocity => D d)
    hDerivative
  rw [fderiv_secondDerivative_apply u hu x d a b,
    fderiv_secondDerivative_apply u hu x d b a] at hApply
  exact hApply

private theorem thirdDerivative_cyclic
    (u : VelocityField) (hu : ContDiff ℝ 3 u)
    (x v e : PhysicalSpace) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v e e =
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x e e v := by
  have hFirstDerivative :
      ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (m := 2) (by norm_num)
  have hOuterSymmetry :
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v e =
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x e v :=
    hFirstDerivative.contDiffAt.isSymmSndFDerivAt
      (by norm_num) v e
  calc
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v e e =
        fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x e v e := by
      exact congrArg
        (fun D : PhysicalSpace →L[ℝ] Velocity => D e)
        hOuterSymmetry
    _ = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x e e v :=
      thirdDerivative_swap_last u hu x e v e

private theorem fderiv_coordinateVectorLaplacian
    (u : VelocityField) (hu : ContDiff ℝ 3 u)
    (x : PhysicalSpace) :
    fderiv ℝ (coordinateVectorLaplacian u) x =
      vectorLaplacianReadout.comp
        (fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) := by
  have hFirstDerivative :
      ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (m := 2) (by norm_num)
  have hSecondDerivative :
      ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ u)) :=
    hFirstDerivative.fderiv_right (m := 1) (by norm_num)
  change fderiv ℝ
      (vectorLaplacianReadout ∘
        fderiv ℝ (fderiv ℝ u)) x = _
  rw [fderiv_comp x vectorLaplacianReadout.differentiableAt
    (hSecondDerivative.differentiable_one x)]
  rw [ContinuousLinearMap.fderiv]

/-- At `C³` regularity, one spatial derivative commutes with `Δ`. -/
theorem fderiv_vectorLaplacian
    (u : VelocityField) (hu : ContDiff ℝ 3 u) :
    fderiv ℝ (Δ u) = Δ (fderiv ℝ u) := by
  rw [← coordinateVectorLaplacian_eq_mathlib u]
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fderiv ℝ u) (EuclideanSpace.basisFun Coordinate ℝ)]
  funext x
  rw [fderiv_coordinateVectorLaplacian u hu x]
  apply ContinuousLinearMap.ext
  intro v
  ext i
  simp only [vectorLaplacianReadout,
    vectorLaplacianReadoutLinear,
    ContinuousLinearMap.comp_apply,
    EuclideanSpace.basisFun_apply,
    iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change
    (∑ j : Coordinate,
      fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v
        (coordinateDirection j) (coordinateDirection j) i) =
      (EuclideanSpace.proj i)
        ((ContinuousLinearMap.apply ℝ Velocity v)
          (∑ j : Coordinate,
            fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x
              (coordinateDirection j) (coordinateDirection j)))
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun w : Velocity => w i)
    (thirdDerivative_cyclic u hu x v (coordinateDirection j))

/-- At `C³` regularity, full right-handed curl commutes with `Δ`. -/
theorem vorticityField_vectorLaplacian
    (u : VelocityField) (hu : ContDiff ℝ 3 u) :
    vorticityField (Δ u) = Δ (vorticityField u) := by
  have hDerivative :
      ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (m := 2) (by norm_num)
  funext x
  unfold vorticityField
  rw [congrFun (fderiv_vectorLaplacian u hu) x]
  change vorticityReadout (Δ (fderiv ℝ u) x) =
    Δ (vorticityReadout ∘ fderiv ℝ u) x
  exact
    (hDerivative.contDiffAt.laplacian_CLM_comp_left
      (l := vorticityReadout)).symm

end

end ThreeDimensionalPeriodicFullVorticityDifferentialTransport
end NavierStokes
end SaturationMonoid
