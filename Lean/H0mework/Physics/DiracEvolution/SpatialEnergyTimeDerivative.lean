import H0mework.Physics.Dirac.DiracMatterSpatialEnergyBalance
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Time derivative of the Stage-9 Dirac spatial energy

The canonical Cauchy chart turns the temporal Dirac flux into a time-dependent
spatial energy density.  Differentiation under the compact box integral then
combines with the spatial flux balance to identify the total-energy derivative
with the mother-action source term.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterSpatialEnergyTimeDerivative

open Filter MeasureTheory Metric Set
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterSymmetricHyperbolicFluxBalance
open StageNineHolonomicField
open StageNineP286ActionCauchySplit
open scoped Topology

noncomputable section

def diracMatterSpatialEnergyTimeDerivative
    (density : ℝ → DiracMatterSpatialCoordinates → ℝ)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  fderiv ℝ (Function.uncurry density) (time, space)
    (1, (0 : DiracMatterSpatialCoordinates))

theorem diracMatterSpatialEnergyTimeDerivative_hasDerivAt
    (density : ℝ → DiracMatterSpatialCoordinates → ℝ)
    (jointC1 : ContDiff ℝ 1 (Function.uncurry density))
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    HasDerivAt (density · space)
      (diracMatterSpatialEnergyTimeDerivative density time space) time := by
  have jointDerivative :
      HasFDerivAt (Function.uncurry density)
        (fderiv ℝ (Function.uncurry density) (time, space))
        (time, space) :=
    (jointC1.differentiable one_ne_zero (time, space)).hasFDerivAt
  have sliced :
      HasFDerivAt
        ((Function.uncurry density) ∘
          fun candidateTime : ℝ => (candidateTime, space))
        ((fderiv ℝ (Function.uncurry density) (time, space)).comp
          (ContinuousLinearMap.inl ℝ ℝ DiracMatterSpatialCoordinates))
        time :=
    jointDerivative.comp time
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) time space)
  simpa [Function.comp_def, diracMatterSpatialEnergyTimeDerivative] using
    sliced.hasDerivAt

theorem diracMatterSpatialEnergyTimeDerivative_continuous
    (density : ℝ → DiracMatterSpatialCoordinates → ℝ)
    (jointC1 : ContDiff ℝ 1 (Function.uncurry density))
    (time : ℝ) :
    Continuous (diracMatterSpatialEnergyTimeDerivative density time) := by
  unfold diracMatterSpatialEnergyTimeDerivative
  exact
    ((jointC1.continuous_fderiv one_ne_zero).comp
      (continuous_const.prodMk continuous_id)).clm_apply continuous_const

theorem diracMatterSpatialEnergyIntegral_hasDerivAt
    (density : ℝ → DiracMatterSpatialCoordinates → ℝ)
    (jointC1 : ContDiff ℝ 1 (Function.uncurry density))
    (time : ℝ)
    (a b : DiracMatterSpatialCoordinates) :
    HasDerivAt
      (fun candidateTime => ∫ space in Icc a b, density candidateTime space)
      (∫ space in Icc a b,
        diracMatterSpatialEnergyTimeDerivative density time space)
      time := by
  let jointDerivative := fderiv ℝ (Function.uncurry density)
  let compactSet :=
    closedBall time 1 ×ˢ Icc a b
  have jointDerivativeContinuous : Continuous jointDerivative := by
    exact jointC1.continuous_fderiv one_ne_zero
  have compactSetCompact : IsCompact compactSet :=
    (isCompact_closedBall time (1 : ℝ)).prod isCompact_Icc
  have imageBounded :
      Bornology.IsBounded (jointDerivative '' compactSet) :=
    (compactSetCompact.image jointDerivativeContinuous).isBounded
  obtain ⟨C, CPositive, imageSubset⟩ :
      ∃ C : ℝ, 0 < C ∧
        jointDerivative '' compactSet ⊆
          closedBall (0 : ℝ × DiracMatterSpatialCoordinates →L[ℝ] ℝ) C :=
    imageBounded.subset_closedBall_lt 0 0
  let timeAxis : ℝ × DiracMatterSpatialCoordinates :=
    (1, (0 : DiracMatterSpatialCoordinates))
  let bound : DiracMatterSpatialCoordinates → ℝ :=
    fun _ => C * ‖timeAxis‖
  have timeNeighborhood : closedBall time 1 ∈ 𝓝 time :=
    mem_of_superset (ball_mem_nhds time zero_lt_one) ball_subset_closedBall
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Icc a b))
      (F := density)
      (F' := fun candidateTime space =>
        diracMatterSpatialEnergyTimeDerivative density candidateTime space)
      (bound := bound)
      timeNeighborhood ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with candidateTime
    exact (jointC1.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact
      (jointC1.continuous.comp
        (continuous_const.prodMk continuous_id)).continuousOn
        |>.integrableOn_compact isCompact_Icc
  · exact
      (diracMatterSpatialEnergyTimeDerivative_continuous
        density jointC1 time).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with space spaceMem
    intro candidateTime candidateTimeMem
    have pairMem : (candidateTime, space) ∈ compactSet :=
      ⟨candidateTimeMem, spaceMem⟩
    have derivativeMem : jointDerivative (candidateTime, space) ∈
        closedBall
          (0 : ℝ × DiracMatterSpatialCoordinates →L[ℝ] ℝ) C :=
      imageSubset (mem_image_of_mem jointDerivative pairMem)
    have derivativeBound :
        ‖jointDerivative (candidateTime, space)‖ ≤ C := by
      simpa only [mem_closedBall_zero_iff] using derivativeMem
    calc
      ‖diracMatterSpatialEnergyTimeDerivative
          density candidateTime space‖ =
          ‖jointDerivative (candidateTime, space) timeAxis‖ := rfl
      _ ≤ ‖jointDerivative (candidateTime, space)‖ * ‖timeAxis‖ :=
        (jointDerivative (candidateTime, space)).le_opNorm timeAxis
      _ ≤ C * ‖timeAxis‖ :=
        mul_le_mul_of_nonneg_right derivativeBound (norm_nonneg _)
      _ = bound space := rfl
  · exact integrableOn_const isCompact_Icc.measure_ne_top
  · filter_upwards with space candidateTime _
    exact diracMatterSpatialEnergyTimeDerivative_hasDerivAt
      density jointC1 candidateTime space

def diracMatterSpatialEnergyDensity
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  let point := diracMatterSpacetimeCoordinatePoint time space
  diracMatterEnergyFlux
    (coefficient canonicalLorentzianTimeDirection point) (field point)

@[simp] theorem diracMatterSpacetimeCoordinatePoint_timeLine
    (time parameter : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpacetimeCoordinatePoint (time + parameter) space =
      diracMatterCoordinateLine
        (diracMatterSpacetimeCoordinatePoint time space)
        canonicalLorentzianTimeDirection parameter := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [diracMatterSpacetimeCoordinatePoint,
      diracMatterCoordinateLine, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, coordinateDirection,
      Fin.sum_univ_three]

theorem diracMatterSpatialEnergyTimeDerivative_eq_temporalEnergyFluxDerivative
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (jointC1 :
      ContDiff ℝ 1
        (Function.uncurry
          (diracMatterSpatialEnergyDensity coefficient field)))
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterSpatialEnergyTimeDerivative
        (diracMatterSpatialEnergyDensity coefficient field) time space =
      diracMatterTemporalEnergyFluxDerivative coefficient field time space := by
  have timeDerivative :=
    diracMatterSpatialEnergyTimeDerivative_hasDerivAt
      (diracMatterSpatialEnergyDensity coefficient field)
      jointC1 time space
  have shifted :
      HasDerivAt
        (fun parameter =>
          diracMatterSpatialEnergyDensity coefficient field
            (time + parameter) space)
        (diracMatterSpatialEnergyTimeDerivative
          (diracMatterSpatialEnergyDensity coefficient field) time space)
        0 := by
    exact HasDerivAt.comp_const_add
      (f := fun candidateTime =>
        diracMatterSpatialEnergyDensity coefficient field candidateTime space)
      time 0 (by simpa using timeDerivative)
  have curveEq :
      (fun parameter =>
        diracMatterSpatialEnergyDensity coefficient field
          (time + parameter) space) =
        (fun parameter =>
          let point :=
            diracMatterCoordinateLine
              (diracMatterSpacetimeCoordinatePoint time space)
              canonicalLorentzianTimeDirection parameter
          diracMatterEnergyFlux
            (coefficient canonicalLorentzianTimeDirection point)
            (field point)) := by
    funext parameter
    simp only [diracMatterSpatialEnergyDensity]
    rw [diracMatterSpacetimeCoordinatePoint_timeLine]
  rw [curveEq] at shifted
  exact shifted.deriv.symm

theorem integral_diracMatterSpatialEnergyDensity_hasDerivAt
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (jointC1 :
      ContDiff ℝ 1
        (Function.uncurry
          (diracMatterSpatialEnergyDensity coefficient field)))
    (time : ℝ)
    (fieldDerivative coefficientDerivative :
      DiracMatterSpatialCoordinates →
        LorentzianIndex → DiracExteriorMatterCarrier)
    (lowerOrder :
      DiracMatterSpatialCoordinates → DiracExteriorMatterCarrier)
    (a b : DiracMatterSpatialCoordinates)
    (hle : a ≤ b)
    (hermitian :
      ∀ (space : DiracMatterSpatialCoordinates)
        (direction : LorentzianIndex),
        Matrix.IsHermitian
          (coefficient direction
            (diracMatterSpacetimeCoordinatePoint time space)))
    (fieldCoordinateDerivative :
      ∀ (space : DiracMatterSpatialCoordinates)
        (direction : LorentzianIndex)
        (internal : InternalMatterCoordinateIndex)
        (spin : DiracSpinorIndex),
        HasDerivAt
          (fun parameter =>
            internalMatterCoordinate internal
              (field
                (diracMatterCoordinateLine
                  (diracMatterSpacetimeCoordinatePoint time space)
                  direction parameter) spin))
          (internalMatterCoordinate internal
            (fieldDerivative space direction spin))
          0)
    (actedFieldCoordinateDerivative :
      ∀ (space : DiracMatterSpatialCoordinates)
        (direction : LorentzianIndex)
        (internal : InternalMatterCoordinateIndex)
        (spin : DiracSpinorIndex),
        HasDerivAt
          (fun parameter =>
            let point :=
              diracMatterCoordinateLine
                (diracMatterSpacetimeCoordinatePoint time space)
                direction parameter
            internalMatterCoordinate internal
              (diracMatrixMatterAction
                (coefficient direction point) (field point) spin))
          (internalMatterCoordinate internal
            ((diracMatrixMatterAction
                (coefficient direction
                  (diracMatterSpacetimeCoordinatePoint time space))
                (fieldDerivative space direction) +
              coefficientDerivative space direction) spin))
          0)
    (equation :
      ∀ space : DiracMatterSpatialCoordinates,
        (∑ direction : LorentzianIndex,
          diracMatrixMatterAction
            (coefficient direction
              (diracMatterSpacetimeCoordinatePoint time space))
            (fieldDerivative space direction)) + lowerOrder space = 0)
    (spatialRegular :
      ∀ direction : Fin 3,
        ContDiff ℝ 1
          (diracMatterSpatialEnergyFlux coefficient field time direction))
    (boundaryZero :
      DiracMatterSpatialFluxZeroOnBoxBoundary
        (diracMatterSpatialEnergyFlux coefficient field time) a b)
    (sourceIntegrable :
      IntegrableOn
        (fun space =>
          diracMatterEnergySourceTerm field
            (diracMatterSpacetimeCoordinatePoint time space)
            (coefficientDerivative space) (lowerOrder space))
        (Icc a b)) :
    HasDerivAt
      (fun candidateTime =>
        ∫ space in Icc a b,
          diracMatterSpatialEnergyDensity
            coefficient field candidateTime space)
      (∫ space in Icc a b,
        diracMatterEnergySourceTerm field
          (diracMatterSpacetimeCoordinatePoint time space)
          (coefficientDerivative space) (lowerOrder space))
      time := by
  have energyDerivative :=
    diracMatterSpatialEnergyIntegral_hasDerivAt
      (diracMatterSpatialEnergyDensity coefficient field)
      jointC1 time a b
  have timeDerivativeIntegralEq :
      (∫ space in Icc a b,
          diracMatterSpatialEnergyTimeDerivative
            (diracMatterSpatialEnergyDensity coefficient field)
            time space) =
        ∫ space in Icc a b,
          diracMatterTemporalEnergyFluxDerivative
            coefficient field time space :=
    setIntegral_congr_fun measurableSet_Icc fun space _ =>
      diracMatterSpatialEnergyTimeDerivative_eq_temporalEnergyFluxDerivative
        coefficient field jointC1 time space
  have integratedBalance :=
    integral_diracMatterEnergyBalance_box
      coefficient field time fieldDerivative coefficientDerivative
      lowerOrder a b hle hermitian fieldCoordinateDerivative
      actedFieldCoordinateDerivative equation spatialRegular
      boundaryZero sourceIntegrable
  exact energyDerivative.congr_deriv
    (timeDerivativeIntegralEq.trans integratedBalance)

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterSpatialEnergyTimeDerivative
