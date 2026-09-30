import H0mework.NavierStokes.Galerkin.CommonTimeExistence

/-!
# Common-time gluing for actual finite Galerkin sections

Two actual unforced finite Galerkin trajectories on the same Fourier
inventory, with the same initial state and the same time interval, are not
independent payments.  Local compactness generates one closed ball
containing both sections; the finite polynomial vector field is Lipschitz on
that ball, so ODE uniqueness glues the two presentations on the whole
interval.

The radius and Lipschitz constant are generated inside the proof.  They are
not caller-supplied smallness or compatibility certificates.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeGluing

open Set ODE
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open
  ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open
  ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds

noncomputable section

/--
Actual unforced finite Galerkin sections with one support, one initial state,
and one common time interval glue uniquely on that entire interval.
-/
theorem finiteGalerkinTrajectories_eqOn_Icc_of_same_initial
    (modes : Finset IntegerWavevector)
    (ν requestedTime : ℝ)
    (left right : ℝ → ComplexVorticityHilbertState)
    (leftPhysical :
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt left
          (finiteStateVorticityGenerator
            modes ν (left time))
          time)
    (rightPhysical :
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        HasDerivAt right
          (finiteStateVorticityGenerator
            modes ν (right time))
          time)
    (sameInitial : left 0 = right 0) :
    EqOn left right (Icc (0 : ℝ) requestedTime) := by
  have leftContinuous :
      ContinuousOn left (Icc (0 : ℝ) requestedTime) :=
    HasDerivAt.continuousOn leftPhysical
  have rightContinuous :
      ContinuousOn right (Icc (0 : ℝ) requestedTime) :=
    HasDerivAt.continuousOn rightPhysical
  have leftImageCompact :
      IsCompact (left '' Icc (0 : ℝ) requestedTime) :=
    isCompact_Icc.image_of_continuousOn leftContinuous
  have rightImageCompact :
      IsCompact (right '' Icc (0 : ℝ) requestedTime) :=
    isCompact_Icc.image_of_continuousOn rightContinuous
  have bothImagesCompact :
      IsCompact
        ((left '' Icc (0 : ℝ) requestedTime) ∪
          (right '' Icc (0 : ℝ) requestedTime)) :=
    leftImageCompact.union rightImageCompact
  obtain ⟨radius, radiusPos, imageNormLe⟩ :=
    bothImagesCompact.isBounded.exists_pos_norm_le
  obtain
      ⟨_fieldBound, lipschitzBound, _fieldNormLe,
        generatorLipschitz⟩ :=
    exists_finiteStateVorticityGenerator_bounds
      modes ν radius
  have leftBall :
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        left time ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) radius := by
    intro time timeMem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact
      imageNormLe (left time)
        (Or.inl ⟨time, timeMem, rfl⟩)
  have rightBall :
      ∀ time ∈ Icc (0 : ℝ) requestedTime,
        right time ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) radius := by
    intro time timeMem
    rw [Metric.mem_closedBall, dist_zero_right]
    exact
      imageNormLe (right time)
        (Or.inr ⟨time, timeMem, rfl⟩)
  apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ =>
        finiteStateVorticityGenerator modes ν)
      (s := fun _ =>
        Metric.closedBall
          (0 : ComplexVorticityHilbertState) radius)
      (K := lipschitzBound)
  · intro time timeMem
    exact generatorLipschitz
  · exact leftContinuous
  · intro time timeMem
    exact
      (leftPhysical time
        (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
  · intro time timeMem
    exact leftBall time (mem_Icc_of_Ico timeMem)
  · exact rightContinuous
  · intro time timeMem
    exact
      (rightPhysical time
        (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
  · intro time timeMem
    exact rightBall time (mem_Icc_of_Ico timeMem)
  · exact sameInitial

end

end
    ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeGluing
end NavierStokes
end SaturationMonoid
