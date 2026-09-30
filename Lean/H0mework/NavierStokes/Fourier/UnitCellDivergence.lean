import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import H0mework.NavierStokes.Fourier.CoarseVectorCalculus

/-!
# Divergence cancellation on the periodic unit cell

The lifted three-torus is represented by the physical unit cell, transported
through the canonical Euclidean coordinate equivalence.  The rectangular-box
divergence theorem and the source-owned lattice-periodicity law identify
opposite faces, so every continuously differentiable periodic vector field
has zero cell-integrated divergence.

This module is an analytic readout/transporter.  It does not generate a
Navier--Stokes trajectory, a local-energy identity, or a nonzero flux.
-/

open MeasureTheory Set

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalPeriodicUnitCellDivergence

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicCoarseVectorCalculus

noncomputable section

abbrev CoordinateSpace := Fin 3 → ℝ

/-- The canonical linear isometry from physical `L²` coordinates to raw coordinates. -/
noncomputable def coordinateEquiv :
    PhysicalSpace ≃L[ℝ] CoordinateSpace :=
  EuclideanSpace.equiv (Fin 3) ℝ

/-- The closed unit cube in raw coordinates. -/
def coordinateUnitCube : Set CoordinateSpace :=
  Icc 0 (fun _ => 1)

/-- The lifted physical fundamental cell. -/
def physicalUnitCell : Set PhysicalSpace :=
  coordinateEquiv ⁻¹' coordinateUnitCube

theorem coordinateUnitCube_isCompact :
    IsCompact coordinateUnitCube :=
  isCompact_Icc

theorem physicalUnitCell_isCompact :
    IsCompact physicalUnitCell := by
  exact
    coordinateEquiv.toHomeomorph.isCompact_preimage.mpr
      coordinateUnitCube_isCompact

@[simp]
theorem mem_physicalUnitCell_iff (x : PhysicalSpace) :
    x ∈ physicalUnitCell ↔
      ∀ i : Fin 3, x i ∈ Icc (0 : ℝ) 1 := by
  change
    ((0 : CoordinateSpace) ≤ (fun i => x i) ∧
      (fun i => x i) ≤ fun _ => 1) ↔
      ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1
  constructor
  · rintro ⟨hlower, hupper⟩ i
    exact ⟨hlower i, hupper i⟩
  · intro h
    exact ⟨fun i => (h i).1, fun i => (h i).2⟩

theorem coordinateEquiv_measurePreserving :
    MeasurePreserving coordinateEquiv volume volume := by
  exact PiLp.volume_preserving_ofLp (Fin 3)

noncomputable def coordinatePullbackDerivative
    (J : PhysicalSpace → PhysicalSpace) (y : CoordinateSpace) :
    CoordinateSpace →L[ℝ] CoordinateSpace :=
  (coordinateEquiv : PhysicalSpace →L[ℝ] CoordinateSpace).comp
    ((fderiv ℝ J (coordinateEquiv.symm y)).comp
      (coordinateEquiv.symm :
        CoordinateSpace →L[ℝ] PhysicalSpace))

theorem coordinatePullback_divergence
    (J : PhysicalSpace → PhysicalSpace) (y : CoordinateSpace) :
    (∑ i : Fin 3,
      coordinatePullbackDerivative J y (Pi.single i 1) i) =
      velocityDivergence J (coordinateEquiv.symm y) := by
  simp only [coordinatePullbackDerivative,
    ContinuousLinearMap.comp_apply, coordinateEquiv,
    PiLp.continuousLinearEquiv_symm_apply]
  rfl

def coordinateUnitIntegerShift (i : Fin 3) : IntegerShift :=
  Pi.single i 1

theorem coordinateEquiv_latticeShift_coordinateUnitIntegerShift
    (i : Fin 3) :
    coordinateEquiv
        (latticeShift (coordinateUnitIntegerShift i)) =
      Pi.single i 1 := by
  ext j
  classical
  by_cases hji : j = i
  · subst j
    simp [coordinateEquiv, latticeShift, coordinateUnitIntegerShift]
  · simp [coordinateEquiv, latticeShift, coordinateUnitIntegerShift, hji]

theorem coordinateFace_front_eq_back_add_latticeShift
    (i : Fin 3) (x : Fin 2 → ℝ) :
    coordinateEquiv.symm (i.insertNth 1 x) =
      coordinateEquiv.symm (i.insertNth 0 x) +
        latticeShift (coordinateUnitIntegerShift i) := by
  apply coordinateEquiv.injective
  simp only [map_add, coordinateEquiv.apply_symm_apply,
    coordinateEquiv_latticeShift_coordinateUnitIntegerShift]
  have h :=
    Fin.insertNth_sub_same (α := fun _ => ℝ)
      i (1 : ℝ) 0 x
  simpa only [sub_zero, add_comm] using
    (sub_eq_iff_eq_add.mp h)

/--
The divergence theorem on the raw coordinate cube, with opposite faces
cancelled by the concrete lattice-periodicity law.
-/
theorem coordinateUnitCube_velocityDivergence_integral_eq_zero
    (J : PhysicalSpace → PhysicalSpace)
    (hJ : ContDiff ℝ 1 J)
    (hperiodic : LatticePeriodic J) :
    (∫ y in coordinateUnitCube,
      velocityDivergence J (coordinateEquiv.symm y)) = 0 := by
  let pulled : CoordinateSpace → CoordinateSpace :=
    fun y => coordinateEquiv (J (coordinateEquiv.symm y))
  have pulledContinuous : Continuous pulled :=
    coordinateEquiv.continuous.comp
      (hJ.continuous.comp coordinateEquiv.symm.continuous)
  have pulledHasFDerivAt (y : CoordinateSpace) :
      HasFDerivAt pulled (coordinatePullbackDerivative J y) y := by
    exact coordinateEquiv.hasFDerivAt.comp
      y
      (((hJ.differentiable one_ne_zero
        (coordinateEquiv.symm y)).hasFDerivAt).comp
          y coordinateEquiv.symm.hasFDerivAt)
  have divergenceContinuous :
      Continuous
        (fun y : CoordinateSpace =>
          velocityDivergence J (coordinateEquiv.symm y)) :=
    (velocityDivergence_continuous J hJ).comp
      coordinateEquiv.symm.continuous
  have divergenceIntegrable :
      IntegrableOn
        (fun y : CoordinateSpace =>
          ∑ i : Fin 3,
            coordinatePullbackDerivative J y
              (Pi.single i 1) i)
        (Icc 0 (fun _ => 1)) := by
    simpa only [coordinatePullback_divergence] using
      divergenceContinuous.integrableOn_Icc
  have divergenceFormula :=
    MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable
      (n := 2) (E := ℝ)
      (a := (0 : CoordinateSpace))
      (b := fun _ => 1)
      (by
        intro i
        norm_num)
      pulled
      (coordinatePullbackDerivative J)
      (∅ : Set CoordinateSpace)
      Set.countable_empty
      pulledContinuous.continuousOn
      (by
        intro y hy
        exact pulledHasFDerivAt y)
      divergenceIntegrable
  rw [coordinateUnitCube]
  simp_rw [← coordinatePullback_divergence]
  rw [divergenceFormula]
  simp only [Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i hi
  suffices
      (fun x : Fin 2 → ℝ =>
          pulled (i.insertNth 1 x) i) =
        fun x : Fin 2 → ℝ =>
          pulled (i.insertNth 0 x) i by
    rw [this, sub_self]
  funext x
  dsimp only [pulled]
  rw [coordinateFace_front_eq_back_add_latticeShift]
  exact congrFun
    (congrArg coordinateEquiv
      (hperiodic (coordinateUnitIntegerShift i)
        (coordinateEquiv.symm (i.insertNth 0 x)))) i

/--
Every `C¹` lattice-periodic vector field has zero integrated divergence on
the physical fundamental cell.
-/
theorem physicalUnitCell_velocityDivergence_integral_eq_zero
    (J : PhysicalSpace → PhysicalSpace)
    (hJ : ContDiff ℝ 1 J)
    (hperiodic : LatticePeriodic J) :
    (∫ x in physicalUnitCell, velocityDivergence J x) = 0 := by
  have hembedding : MeasurableEmbedding coordinateEquiv :=
    coordinateEquiv.toHomeomorph.measurableEmbedding
  calc
    (∫ x in physicalUnitCell, velocityDivergence J x) =
        ∫ y in coordinateUnitCube,
          velocityDivergence J (coordinateEquiv.symm y) := by
      rw [← coordinateEquiv_measurePreserving.setIntegral_preimage_emb
        hembedding]
      rfl
    _ = 0 :=
      coordinateUnitCube_velocityDivergence_integral_eq_zero
        J hJ hperiodic

end

end ThreeDimensionalPeriodicUnitCellDivergence
end NavierStokes
end SaturationMonoid
