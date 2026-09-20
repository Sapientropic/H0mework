import H0mework.Physics.Dirac.DiracMatterSymmetricHyperbolicFluxBalance
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

/-!
# Spatial energy balance for Stage-9 Dirac matter

The canonical Cauchy chart identifies the three spatial coordinates with
`Fin 3 → ℝ`.  The Bochner divergence theorem then turns the local Hermitian
Dirac flux identity into an exact box-integrated energy balance.  Vanishing
normal flux on the box boundary removes the spatial divergence term.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterSpatialEnergyBalance

open MeasureTheory Set
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSymmetricHyperbolicFluxBalance
open StageNineHolonomicField
open StageNineP286ActionCauchySplit

noncomputable section

abbrev DiracMatterSpatialCoordinates := Fin 3 → ℝ

def diracMatterSpatialFluxDivergence
    (flux : Fin 3 → DiracMatterSpatialCoordinates → ℝ)
    (point : DiracMatterSpatialCoordinates) : ℝ :=
  ∑ direction : Fin 3,
    fderiv ℝ (flux direction) point (Pi.single direction 1)

def diracMatterSpacetimeCoordinatePoint
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : BasePoint :=
  canonicalCauchySlicePoint time
    ((EuclideanSpace.equiv (Fin 3) ℝ).symm space)

@[simp] theorem diracMatterSpacetimeCoordinatePoint_line
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (direction : Fin 3)
    (parameter : ℝ) :
    diracMatterSpacetimeCoordinatePoint time
        (space + parameter • Pi.single direction 1) =
      diracMatterCoordinateLine
        (diracMatterSpacetimeCoordinatePoint time space)
        direction.succ parameter := by
  apply PiLp.ext
  intro coordinate
  fin_cases direction <;> fin_cases coordinate <;>
    simp [diracMatterSpacetimeCoordinatePoint,
      diracMatterCoordinateLine, canonicalCauchySlicePoint,
      canonicalLorentzianTimeDirection, coordinateDirection,
      Fin.sum_univ_three]

def diracMatterSpatialEnergyFlux
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (direction : Fin 3)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  let point := diracMatterSpacetimeCoordinatePoint time space
  diracMatterEnergyFlux (coefficient direction.succ point) (field point)

/-- Spatial slice of the bilinear Hermitian flux between an independent test
and trial field. -/
def diracMatterSpatialBilinearFlux
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (first second : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (direction : Fin 3)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  let point := diracMatterSpacetimeCoordinatePoint time space
  diracMatterBilinearFlux (coefficient direction.succ point)
    (first point) (second point)

theorem diracMatterSpatialBilinearFlux_fderiv_coordinate
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (first second : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (direction : Fin 3)
    (space : DiracMatterSpatialCoordinates)
    (differentiable :
      DifferentiableAt ℝ
        (diracMatterSpatialBilinearFlux coefficient first second time direction)
        space) :
    fderiv ℝ
        (diracMatterSpatialBilinearFlux coefficient first second time direction)
        space (Pi.single direction 1) =
      deriv
        (fun parameter ↦
          let point :=
            diracMatterCoordinateLine
              (diracMatterSpacetimeCoordinatePoint time space)
              direction.succ parameter
          diracMatterBilinearFlux (coefficient direction.succ point)
            (first point) (second point))
        0 := by
  have differentiableLine :
      DifferentiableAt ℝ
        (diracMatterSpatialBilinearFlux coefficient first second time direction)
        (space + (0 : ℝ) • Pi.single direction 1) := by
    simpa using differentiable
  have derivativeEq := differentiableLine.deriv_comp_add_smul
    (𝕜 := ℝ) (x := space) (y := Pi.single direction 1) (t := (0 : ℝ))
  simp only [zero_smul, add_zero] at derivativeEq
  rw [← derivativeEq]
  apply congrArg (fun curve : ℝ → ℝ ↦ deriv curve 0)
  funext parameter
  simp only [diracMatterSpatialBilinearFlux]
  rw [diracMatterSpacetimeCoordinatePoint_line]

theorem diracMatterSpatialEnergyFlux_fderiv_coordinate
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (direction : Fin 3)
    (space : DiracMatterSpatialCoordinates)
    (differentiable :
      DifferentiableAt ℝ
        (diracMatterSpatialEnergyFlux coefficient field time direction)
        space) :
    fderiv ℝ (diracMatterSpatialEnergyFlux coefficient field time direction)
        space (Pi.single direction 1) =
      deriv
        (fun parameter =>
          let point :=
            diracMatterCoordinateLine
              (diracMatterSpacetimeCoordinatePoint time space)
              direction.succ parameter
          diracMatterEnergyFlux
            (coefficient direction.succ point) (field point))
        0 := by
  have differentiableLine :
      DifferentiableAt ℝ
        (diracMatterSpatialEnergyFlux coefficient field time direction)
        (space + (0 : ℝ) • Pi.single direction 1) := by
    simpa using differentiable
  have derivativeEq := differentiableLine.deriv_comp_add_smul
    (𝕜 := ℝ) (x := space) (y := Pi.single direction 1) (t := (0 : ℝ))
  simp only [zero_smul, add_zero] at derivativeEq
  rw [← derivativeEq]
  apply congrArg (fun curve : ℝ → ℝ => deriv curve 0)
  funext parameter
  simp only [diracMatterSpatialEnergyFlux]
  rw [diracMatterSpacetimeCoordinatePoint_line]

theorem diracMatterEnergyFluxDivergence_slice_eq
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (spatialDifferentiable :
      ∀ direction : Fin 3,
        DifferentiableAt ℝ
          (diracMatterSpatialEnergyFlux coefficient field time direction)
          space) :
    diracMatterEnergyFluxDivergence coefficient field
        (diracMatterSpacetimeCoordinatePoint time space) =
      deriv
          (fun parameter =>
            let point :=
              diracMatterCoordinateLine
                (diracMatterSpacetimeCoordinatePoint time space)
                canonicalLorentzianTimeDirection parameter
            diracMatterEnergyFlux
              (coefficient canonicalLorentzianTimeDirection point)
              (field point))
          0 +
        diracMatterSpatialFluxDivergence
          (diracMatterSpatialEnergyFlux coefficient field time) space := by
  unfold diracMatterEnergyFluxDivergence
  unfold diracMatterSpatialFluxDivergence
  rw [Fin.sum_univ_four, Fin.sum_univ_three]
  rw [diracMatterSpatialEnergyFlux_fderiv_coordinate
      coefficient field time 0 space (spatialDifferentiable 0),
    diracMatterSpatialEnergyFlux_fderiv_coordinate
      coefficient field time 1 space (spatialDifferentiable 1),
    diracMatterSpatialEnergyFlux_fderiv_coordinate
      coefficient field time 2 space (spatialDifferentiable 2)]
  simp only [canonicalLorentzianTimeDirection]
  have succZero : (Fin.succ (0 : Fin 3) : Fin 4) = 1 := rfl
  have succOne : (Fin.succ (1 : Fin 3) : Fin 4) = 2 := rfl
  have succTwo : (Fin.succ (2 : Fin 3) : Fin 4) = 3 := rfl
  rw [succZero, succOne, succTwo]
  ring

def diracMatterTemporalEnergyFluxDerivative
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  deriv
    (fun parameter =>
      let point :=
        diracMatterCoordinateLine
          (diracMatterSpacetimeCoordinatePoint time space)
          canonicalLorentzianTimeDirection parameter
      diracMatterEnergyFlux
        (coefficient canonicalLorentzianTimeDirection point) (field point))
    0

def diracMatterEnergySourceTerm
    (field : BasePoint → DiracExteriorMatterCarrier)
    (point : BasePoint)
    (coefficientDerivative :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (lowerOrder : DiracExteriorMatterCarrier) : ℝ :=
  (∑ direction : LorentzianIndex,
    Complex.re
      (diracExteriorMatterCoordinatePairing (field point)
        (coefficientDerivative direction))) -
    2 * Complex.re
      (diracExteriorMatterCoordinatePairing (field point) lowerOrder)

theorem diracMatterEnergyBalance_pointwise
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
    (time : ℝ)
    (space : DiracMatterSpatialCoordinates)
    (fieldDerivative coefficientDerivative :
      LorentzianIndex → DiracExteriorMatterCarrier)
    (lowerOrder : DiracExteriorMatterCarrier)
    (hermitian :
      ∀ direction : LorentzianIndex,
        Matrix.IsHermitian
          (coefficient direction
            (diracMatterSpacetimeCoordinatePoint time space)))
    (fieldCoordinateDerivative :
      ∀ (direction : LorentzianIndex)
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
            (fieldDerivative direction spin))
          0)
    (actedFieldCoordinateDerivative :
      ∀ (direction : LorentzianIndex)
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
                (fieldDerivative direction) +
              coefficientDerivative direction) spin))
          0)
    (equation :
      (∑ direction : LorentzianIndex,
        diracMatrixMatterAction
          (coefficient direction
            (diracMatterSpacetimeCoordinatePoint time space))
          (fieldDerivative direction)) + lowerOrder = 0)
    (spatialDifferentiable :
      ∀ direction : Fin 3,
        DifferentiableAt ℝ
          (diracMatterSpatialEnergyFlux coefficient field time direction)
          space) :
    diracMatterTemporalEnergyFluxDerivative coefficient field time space +
        diracMatterSpatialFluxDivergence
          (diracMatterSpatialEnergyFlux coefficient field time) space =
      diracMatterEnergySourceTerm field
        (diracMatterSpacetimeCoordinatePoint time space)
        coefficientDerivative lowerOrder := by
  unfold diracMatterTemporalEnergyFluxDerivative
  unfold diracMatterEnergySourceTerm
  rw [← diracMatterEnergyFluxDivergence_slice_eq
    coefficient field time space spatialDifferentiable]
  exact diracMatterEnergyFluxDivergence_eq
    coefficient field (diracMatterSpacetimeCoordinatePoint time space)
    fieldDerivative coefficientDerivative lowerOrder hermitian
    fieldCoordinateDerivative actedFieldCoordinateDerivative equation

theorem diracMatterSpatialFluxDivergence_continuous
    (flux : Fin 3 → DiracMatterSpatialCoordinates → ℝ)
    (regular : ∀ direction : Fin 3, ContDiff ℝ 1 (flux direction)) :
    Continuous (diracMatterSpatialFluxDivergence flux) := by
  unfold diracMatterSpatialFluxDivergence
  exact continuous_finsetSum _ fun direction _ =>
    ((regular direction).continuous_fderiv one_ne_zero).clm_apply
      continuous_const

theorem integral_diracMatterSpatialFluxDivergence_box
    (flux : Fin 3 → DiracMatterSpatialCoordinates → ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (hle : a ≤ b)
    (regular : ∀ direction : Fin 3, ContDiff ℝ 1 (flux direction)) :
    (∫ point in Icc a b, diracMatterSpatialFluxDivergence flux point) =
      ∑ direction : Fin 3,
        ((∫ point in Icc (a ∘ direction.succAbove)
              (b ∘ direction.succAbove),
            flux direction
              (direction.insertNth (b direction) point)) -
          ∫ point in Icc (a ∘ direction.succAbove)
              (b ∘ direction.succAbove),
            flux direction
              (direction.insertNth (a direction) point)) := by
  apply MeasureTheory.integral_divergence_of_hasFDerivAt_off_countable'
    a b hle flux
    (fun direction point => fderiv ℝ (flux direction) point)
    ∅ countable_empty
  · intro direction
    exact (regular direction).continuous.continuousOn
  · intro point _ direction
    exact ((regular direction).differentiable one_ne_zero point).hasFDerivAt
  · exact
      (diracMatterSpatialFluxDivergence_continuous flux regular).continuousOn
        |>.integrableOn_compact isCompact_Icc

def DiracMatterSpatialFluxZeroOnBoxBoundary
    (flux : Fin 3 → DiracMatterSpatialCoordinates → ℝ)
    (a b : DiracMatterSpatialCoordinates) : Prop :=
  ∀ (direction : Fin 3) (point : Fin 2 → ℝ),
    point ∈ Icc (a ∘ direction.succAbove) (b ∘ direction.succAbove) →
      flux direction (direction.insertNth (b direction) point) = 0 ∧
      flux direction (direction.insertNth (a direction) point) = 0

theorem integral_diracMatterSpatialFluxDivergence_box_eq_zero
    (flux : Fin 3 → DiracMatterSpatialCoordinates → ℝ)
    (a b : DiracMatterSpatialCoordinates)
    (hle : a ≤ b)
    (regular : ∀ direction : Fin 3, ContDiff ℝ 1 (flux direction))
    (boundaryZero : DiracMatterSpatialFluxZeroOnBoxBoundary flux a b) :
    (∫ point in Icc a b, diracMatterSpatialFluxDivergence flux point) = 0 := by
  rw [integral_diracMatterSpatialFluxDivergence_box flux a b hle regular]
  apply Finset.sum_eq_zero
  intro direction _
  have frontZero :
      (∫ point in Icc (a ∘ direction.succAbove)
            (b ∘ direction.succAbove),
          flux direction (direction.insertNth (b direction) point)) = 0 := by
    calc
      _ = ∫ _point in Icc (a ∘ direction.succAbove)
            (b ∘ direction.succAbove), (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_Icc fun point membership =>
          (boundaryZero direction point membership).1
      _ = 0 := by simp
  have backZero :
      (∫ point in Icc (a ∘ direction.succAbove)
            (b ∘ direction.succAbove),
          flux direction (direction.insertNth (a direction) point)) = 0 := by
    calc
      _ = ∫ _point in Icc (a ∘ direction.succAbove)
            (b ∘ direction.succAbove), (0 : ℝ) :=
        setIntegral_congr_fun measurableSet_Icc fun point membership =>
          (boundaryZero direction point membership).2
      _ = 0 := by simp
  rw [frontZero, backZero, sub_self]

theorem integral_diracMatterEnergyBalance_box
    (coefficient : LorentzianIndex → BasePoint → DiracMatrix)
    (field : BasePoint → DiracExteriorMatterCarrier)
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
    (∫ space in Icc a b,
        diracMatterTemporalEnergyFluxDerivative
          coefficient field time space) =
      ∫ space in Icc a b,
        diracMatterEnergySourceTerm field
          (diracMatterSpacetimeCoordinatePoint time space)
          (coefficientDerivative space) (lowerOrder space) := by
  have balance
      (space : DiracMatterSpatialCoordinates) :
      diracMatterTemporalEnergyFluxDerivative coefficient field time space +
          diracMatterSpatialFluxDivergence
            (diracMatterSpatialEnergyFlux coefficient field time) space =
        diracMatterEnergySourceTerm field
          (diracMatterSpacetimeCoordinatePoint time space)
          (coefficientDerivative space) (lowerOrder space) :=
    diracMatterEnergyBalance_pointwise
      coefficient field time space
      (fieldDerivative space) (coefficientDerivative space)
      (lowerOrder space) (hermitian space)
      (fieldCoordinateDerivative space)
      (actedFieldCoordinateDerivative space) (equation space)
      (fun direction =>
        (spatialRegular direction).differentiable one_ne_zero space)
  have temporalEq
      (space : DiracMatterSpatialCoordinates) :
      diracMatterTemporalEnergyFluxDerivative coefficient field time space =
        diracMatterEnergySourceTerm field
            (diracMatterSpacetimeCoordinatePoint time space)
            (coefficientDerivative space) (lowerOrder space) -
          diracMatterSpatialFluxDivergence
            (diracMatterSpatialEnergyFlux coefficient field time) space := by
    rw [← balance space]
    ring
  have spatialIntegrable :
      IntegrableOn
        (diracMatterSpatialFluxDivergence
          (diracMatterSpatialEnergyFlux coefficient field time))
        (Icc a b) :=
    (diracMatterSpatialFluxDivergence_continuous
      (diracMatterSpatialEnergyFlux coefficient field time) spatialRegular)
      |>.continuousOn.integrableOn_compact isCompact_Icc
  calc
    (∫ space in Icc a b,
        diracMatterTemporalEnergyFluxDerivative
          coefficient field time space) =
      ∫ space in Icc a b,
        (diracMatterEnergySourceTerm field
            (diracMatterSpacetimeCoordinatePoint time space)
            (coefficientDerivative space) (lowerOrder space) -
          diracMatterSpatialFluxDivergence
            (diracMatterSpatialEnergyFlux coefficient field time) space) :=
      setIntegral_congr_fun measurableSet_Icc fun space _ => temporalEq space
    _ = (∫ space in Icc a b,
          diracMatterEnergySourceTerm field
            (diracMatterSpacetimeCoordinatePoint time space)
            (coefficientDerivative space) (lowerOrder space)) -
        ∫ space in Icc a b,
          diracMatterSpatialFluxDivergence
            (diracMatterSpatialEnergyFlux coefficient field time) space := by
      rw [integral_sub sourceIntegrable spatialIntegrable]
    _ = ∫ space in Icc a b,
          diracMatterEnergySourceTerm field
            (diracMatterSpacetimeCoordinatePoint time space)
            (coefficientDerivative space) (lowerOrder space) := by
      rw [integral_diracMatterSpatialFluxDivergence_box_eq_zero
        (diracMatterSpatialEnergyFlux coefficient field time)
        a b hle spatialRegular boundaryZero, sub_zero]

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterSpatialEnergyBalance
