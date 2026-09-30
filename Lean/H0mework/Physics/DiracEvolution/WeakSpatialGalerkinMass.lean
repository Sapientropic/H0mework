import H0mework.Physics.Dirac.DiracMatterHermitianEnergy
import H0mework.Physics.DiracEvolution.WeakGalerkinEvolution
import H0mework.Physics.Dirac.DiracMatterSpatialEnergyBalance
import H0mework.Physics.DiracEvolution.SpatialEnergyTimeDerivative
import H0mework.Physics.DiracEvolution.SafeGalerkinOperator

/-!
# Stage-nine weak spatial Galerkin mass

This module synthesizes finite matter coefficients into compactly supported
spatial Cauchy fields and integrates the Hermitian Dirac time coefficient into
the real weak mass form. Pointwise positivity and faithful synthesis generate
the mass inverse through Fréchet--Riesz; no inverse, residual, or target field
is accepted as constructor input.
-/

namespace SaturationMonoid.PhysicsCore.StageNineDiracMatterWeakSpatialGalerkinMass

open Filter MeasureTheory Metric Set
open DiracCliffordRepresentation
open DiracExteriorMatterAction
open StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
open StageNineDiracMatterHermitianEnergy
open StageNineDiracMatterSpatialEnergyBalance
open StageNineDiracMatterSpatialEnergyTimeDerivative
open StageNineDiracMatterWeakGalerkinEvolution
open StageNineHolonomicField
open StageNineMatterActionTemporalFirstGermResponse
open StageNineP286ActionCauchySplit
open StageNineP286ActionConnectionVelocity
open scoped ComplexOrder ContDiff Matrix

noncomputable section

set_option autoImplicit false

/-- The real Hermitian weak pairing induced by one Dirac coefficient. -/
def diracExteriorMatterEnergyPairing
    (matrix : DiracMatrix)
    (first second : DiracExteriorMatterCarrier) : ℝ :=
  (diracExteriorMatterCoordinatePairing first
  (diracMatrixMatterAction matrix second)).re

private theorem coordinatePairing_add_left
    (first second third : DiracExteriorMatterCarrier) :
    diracExteriorMatterCoordinatePairing (first + second) third =
      diracExteriorMatterCoordinatePairing first third +
        diracExteriorMatterCoordinatePairing second third := by
  unfold diracExteriorMatterCoordinatePairing
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro internal _
  unfold dotProduct
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro spin _
  simp
  ring

private theorem coordinatePairing_real_smul_left
    (parameter : ℝ)
    (first second : DiracExteriorMatterCarrier) :
    diracExteriorMatterCoordinatePairing (parameter • first) second =
      (parameter : ℂ) *
        diracExteriorMatterCoordinatePairing first second := by
  unfold diracExteriorMatterCoordinatePairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro internal _
  unfold dotProduct
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro spin _
  simp
  ring

theorem diracExteriorMatterEnergyPairing_add_right
    (matrix : DiracMatrix)
    (first second third : DiracExteriorMatterCarrier) :
    diracExteriorMatterEnergyPairing matrix first (second + third) =
      diracExteriorMatterEnergyPairing matrix first second +
        diracExteriorMatterEnergyPairing matrix first third := by
  unfold diracExteriorMatterEnergyPairing
  rw [map_add]
  change
    ((diracExteriorMatterCoordinatePairingRight first)
      ((diracMatrixMatterAction matrix) second +
        (diracMatrixMatterAction matrix) third)).re = _
  rw [map_add, Complex.add_re]
  simp only [diracExteriorMatterCoordinatePairingRight_apply]

theorem diracExteriorMatterEnergyPairing_real_smul_right
    (matrix : DiracMatrix)
    (parameter : ℝ)
    (first second : DiracExteriorMatterCarrier) :
    diracExteriorMatterEnergyPairing matrix first (parameter • second) =
      parameter • diracExteriorMatterEnergyPairing matrix first second := by
  unfold diracExteriorMatterEnergyPairing
  change
    (diracExteriorMatterCoordinatePairing first
      ((diracMatrixMatterAction matrix) ((parameter : ℂ) • second))).re = _
  rw [map_smul]
  change
    ((diracExteriorMatterCoordinatePairingRight first)
      ((parameter : ℂ) •
        (diracMatrixMatterAction matrix) second)).re = _
  rw [map_smul]
  simp

theorem diracExteriorMatterEnergyPairing_add_left
    (matrix : DiracMatrix)
    (first second third : DiracExteriorMatterCarrier) :
    diracExteriorMatterEnergyPairing matrix (first + second) third =
      diracExteriorMatterEnergyPairing matrix first third +
        diracExteriorMatterEnergyPairing matrix second third := by
  unfold diracExteriorMatterEnergyPairing
  rw [coordinatePairing_add_left, Complex.add_re]

theorem diracExteriorMatterEnergyPairing_real_smul_left
    (matrix : DiracMatrix)
    (parameter : ℝ)
    (first second : DiracExteriorMatterCarrier) :
    diracExteriorMatterEnergyPairing matrix (parameter • first) second =
      parameter • diracExteriorMatterEnergyPairing matrix first second := by
  unfold diracExteriorMatterEnergyPairing
  rw [coordinatePairing_real_smul_left]
  simp

@[simp] theorem diracExteriorMatterEnergyPairing_self
    (matrix : DiracMatrix)
    (field : DiracExteriorMatterCarrier) :
    diracExteriorMatterEnergyPairing matrix field field =
      diracExteriorMatterCoordinateEnergy matrix field :=
  rfl

section SpatialSynthesis

variable {modeCount : ℕ}

/-- The canonical spacetime point determined by time and spatial coordinates
is a smooth joint parameter. -/
theorem diracMatterSpacetimeCoordinatePoint_joint_contDiff :
    ContDiff ℝ ∞ (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      diracMatterSpacetimeCoordinatePoint input.1 input.2) := by
  rw [show (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      diracMatterSpacetimeCoordinatePoint input.1 input.2) =
      (fun input ↦
        input.1 • coordinateDirection canonicalLorentzianTimeDirection +
          canonicalSpatialInclusion
            ((EuclideanSpace.equiv (Fin 3) ℝ).symm input.2)) by
    funext input
    unfold diracMatterSpacetimeCoordinatePoint
    rw [canonicalCauchySlicePoint_eq_const_add_inclusion]
    congr 1
    ext coordinate
    fin_cases coordinate <;>
      simp [coordinateDirection, canonicalLorentzianTimeDirection]]
  exact (contDiff_fst.smul contDiff_const).add
    (canonicalSpatialInclusion.contDiff.comp
      ((EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousLinearEquiv.contDiff.comp
        contDiff_snd))

/-- Synthesis of a finite matter coefficient into a spatial Cauchy field. -/
def diracMatterSpatialGalerkinCoordinates
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (space : DiracMatterSpatialCoordinates) : MatterCoordinateCarrier :=
  ∑ mode, basis mode space •
    diracMatterGalerkinCoefficientMode coefficient mode

def diracMatterSpatialGalerkinSynthesis
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (space : DiracMatterSpatialCoordinates) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (diracMatterSpatialGalerkinCoordinates basis coefficient space)

@[simp] theorem diracMatterSpatialGalerkinSynthesis_coordinates
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (space : DiracMatterSpatialCoordinates) :
    matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis coefficient space) =
      ∑ mode, basis mode space •
        diracMatterGalerkinCoefficientMode coefficient mode := by
  simp [diracMatterSpatialGalerkinSynthesis,
    diracMatterSpatialGalerkinCoordinates]

theorem diracMatterSpatialGalerkinSynthesis_add
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterSpatialGalerkinSynthesis basis (first + second) =
      diracMatterSpatialGalerkinSynthesis basis first +
        diracMatterSpatialGalerkinSynthesis basis second := by
  funext space
  apply matterCoordinateEquiv.injective
  simp only [diracMatterSpatialGalerkinSynthesis_coordinates,
    diracMatterGalerkinCoefficientMode_add, smul_add,
    Finset.sum_add_distrib, Pi.add_apply, map_add]

theorem diracMatterSpatialGalerkinSynthesis_real_smul
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterSpatialGalerkinSynthesis basis (parameter • coefficient) =
      parameter •
        diracMatterSpatialGalerkinSynthesis basis coefficient := by
  funext space
  apply matterCoordinateEquiv.injective
  simp only [diracMatterSpatialGalerkinSynthesis_coordinates,
    diracMatterGalerkinCoefficientMode_real_smul, Pi.smul_apply,
    matterCoordinateEquiv_real_smul]
  change
    (∑ mode, (basis mode space : ℂ) •
      ((parameter : ℂ) •
        diracMatterGalerkinCoefficientMode coefficient mode)) =
      (parameter : ℂ) •
        (∑ mode, (basis mode space : ℂ) •
          diracMatterGalerkinCoefficientMode coefficient mode)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro mode _
  rw [smul_smul, smul_smul, mul_comm]

theorem diracMatterSpatialGalerkinSynthesis_coordinates_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    Continuous (fun space ↦ matterCoordinateEquiv
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)) := by
  simp only [diracMatterSpatialGalerkinSynthesis_coordinates]
  apply continuous_finsetSum Finset.univ
  intro mode _
  exact (basisContinuous mode).smul continuous_const

theorem diracMatterSpatialGalerkinSynthesis_coordinates_contDiff_one
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    ContDiff ℝ 1 (fun space ↦ matterCoordinateEquiv
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)) := by
  simp only [diracMatterSpatialGalerkinSynthesis_coordinates]
  apply ContDiff.sum
  intro mode _
  exact (basisRegular mode).smul contDiff_const

theorem diracMatterSpatialGalerkinSynthesis_coordinates_hasCompactSupport
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    HasCompactSupport (fun space ↦ matterCoordinateEquiv
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)) := by
  have functionEq :
      (fun space ↦ matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis coefficient space)) =
      diracMatterSpatialGalerkinCoordinates basis coefficient := by
    funext space
    exact diracMatterSpatialGalerkinSynthesis_coordinates basis coefficient space
  rw [functionEq]
  rw [hasCompactSupport_iff_eventuallyEq]
  have eachMode (mode : Fin modeCount) :
      ∀ᶠ space in coclosedCompact _, basis mode space = 0 := by
    simpa only [hasCompactSupport_iff_eventuallyEq, Filter.EventuallyEq,
      Pi.zero_apply] using
      basisCompact mode
  have allModes :
      ∀ᶠ space in coclosedCompact _, ∀ mode ∈ Finset.univ,
        basis mode space = 0 :=
    (eventually_all_finset Finset.univ).2 fun mode _ ↦ eachMode mode
  filter_upwards [allModes] with space equality
  simp [diracMatterSpatialGalerkinCoordinates, equality]

end SpatialSynthesis

section WeakMassDensity

variable {modeCount : ℕ}

/-- One faithful internal/spin read after returning from the finite matter
coordinate carrier. -/
def matterCoordinateInternalSpinLinear
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) : MatterCoordinateCarrier →ₗ[ℂ] ℂ where
  toFun coordinate :=
    internalMatterCoordinate internal (matterCoordinateEquiv.symm coordinate spin)
  map_add' first second := by simp
  map_smul' parameter coordinate := by simp

/-- The faithful internal/spin read is continuous because its domain is the
finite matter coordinate carrier. -/
def matterCoordinateInternalSpinCLM
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) : MatterCoordinateCarrier →L[ℂ] ℂ :=
  (matterCoordinateInternalSpinLinear internal spin).toContinuousLinearMap

@[simp] theorem matterCoordinateInternalSpinCLM_apply
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex)
    (coordinate : MatterCoordinateCarrier) :
    matterCoordinateInternalSpinCLM internal spin coordinate =
      internalMatterCoordinate internal
        (matterCoordinateEquiv.symm coordinate spin) :=
  rfl

theorem diracMatterSpatialGalerkinSynthesis_internalCoordinate_continuous
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) :
    Continuous fun space ↦ internalMatterCoordinate internal
      (diracMatterSpatialGalerkinSynthesis basis coefficient space spin) := by
  let coordinatePath : DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
    fun space ↦ matterCoordinateEquiv
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)
  have coordinatePathContinuous : Continuous coordinatePath :=
    diracMatterSpatialGalerkinSynthesis_coordinates_continuous
      basis basisContinuous coefficient
  have readEq :
      (fun space ↦ matterCoordinateInternalSpinCLM internal spin
        (coordinatePath space)) =
      (fun space ↦ internalMatterCoordinate internal
        (diracMatterSpatialGalerkinSynthesis basis coefficient space spin)) := by
    funext space
    unfold coordinatePath
    rw [matterCoordinateInternalSpinCLM_apply,
      matterCoordinateEquiv.symm_apply_apply]
  rw [← readEq]
  exact (matterCoordinateInternalSpinCLM internal spin).continuous.comp
    coordinatePathContinuous

theorem diracMatterSpatialGalerkinSynthesis_internalCoordinate_contDiff_one
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (internal : InternalMatterCoordinateIndex)
    (spin : DiracSpinorIndex) :
    ContDiff ℝ 1 fun space ↦ internalMatterCoordinate internal
      (diracMatterSpatialGalerkinSynthesis basis coefficient space spin) := by
  let coordinatePath : DiracMatterSpatialCoordinates → MatterCoordinateCarrier :=
    fun space ↦ matterCoordinateEquiv
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)
  let readCLM : MatterCoordinateCarrier →L[ℝ] ℂ :=
    (matterCoordinateInternalSpinCLM internal spin).restrictScalars ℝ
  have coordinatePathRegular : ContDiff ℝ 1 coordinatePath :=
    diracMatterSpatialGalerkinSynthesis_coordinates_contDiff_one
      basis basisRegular coefficient
  have readEq :
      (fun space ↦ readCLM (coordinatePath space)) =
      (fun space ↦ internalMatterCoordinate internal
        (diracMatterSpatialGalerkinSynthesis basis coefficient space spin)) := by
    funext space
    unfold readCLM coordinatePath
    change matterCoordinateInternalSpinCLM internal spin
      (matterCoordinateEquiv
        (diracMatterSpatialGalerkinSynthesis basis coefficient space)) = _
    rw [matterCoordinateInternalSpinCLM_apply,
      matterCoordinateEquiv.symm_apply_apply]
  rw [← readEq]
  exact readCLM.contDiff.comp coordinatePathRegular

/-- Pointwise weak mass density before spatial integration. -/
def diracMatterWeakMassDensity
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (space : DiracMatterSpatialCoordinates) : ℝ :=
  diracExteriorMatterEnergyPairing (matrix space)
    (diracMatterSpatialGalerkinSynthesis basis first space)
    (diracMatterSpatialGalerkinSynthesis basis second space)

/-- Joint time-space continuity of the action-owned weak mass density. -/
theorem diracMatterWeakMassDensity_joint_continuous
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    Continuous fun input : ℝ × DiracMatterSpatialCoordinates ↦
      diracMatterWeakMassDensity (matrix input.1) basis first second input.2 := by
  unfold diracMatterWeakMassDensity diracExteriorMatterEnergyPairing
  rw [show (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      (diracExteriorMatterCoordinatePairing
        (diracMatterSpatialGalerkinSynthesis basis first input.2)
        ((diracMatrixMatterAction (matrix input.1 input.2))
          (diracMatterSpatialGalerkinSynthesis basis second input.2))).re) =
      (fun input ↦ Complex.re
        (∑ internal : InternalMatterCoordinateIndex,
          (star (fun spin ↦ internalMatterCoordinate internal
              (diracMatterSpatialGalerkinSynthesis basis first input.2 spin))) ⬝ᵥ
            (fun spin ↦ ∑ column : DiracSpinorIndex,
              matrix input.1 input.2 spin column *
                internalMatterCoordinate internal
                  (diracMatterSpatialGalerkinSynthesis basis second input.2
                    column)))) by
    funext input
    unfold diracExteriorMatterCoordinatePairing
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro internal _
    congr 1
    funext spin
    exact internalMatterCoordinate_diracMatrixMatterAction
      (matrix input.1 input.2)
      (diracMatterSpatialGalerkinSynthesis basis second input.2)
      spin internal]
  apply Complex.continuous_re.comp
  apply continuous_finsetSum Finset.univ
  intro internal _
  unfold dotProduct
  apply continuous_finsetSum Finset.univ
  intro spin _
  apply Continuous.mul
  · exact Continuous.star
      ((diracMatterSpatialGalerkinSynthesis_internalCoordinate_continuous
        basis basisContinuous first internal spin).comp continuous_snd)
  · apply continuous_finsetSum Finset.univ
    intro column _
    exact (matrixContinuous spin column).mul
      ((diracMatterSpatialGalerkinSynthesis_internalCoordinate_continuous
        basis basisContinuous second internal column).comp continuous_snd)

theorem diracMatterWeakMassDensity_joint_contDiff_one
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixRegular : ∀ row column, ContDiff ℝ 1 fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    ContDiff ℝ 1 fun input : ℝ × DiracMatterSpatialCoordinates ↦
      diracMatterWeakMassDensity (matrix input.1) basis first second input.2 := by
  unfold diracMatterWeakMassDensity diracExteriorMatterEnergyPairing
  rw [show (fun input : ℝ × DiracMatterSpatialCoordinates ↦
      (diracExteriorMatterCoordinatePairing
        (diracMatterSpatialGalerkinSynthesis basis first input.2)
        ((diracMatrixMatterAction (matrix input.1 input.2))
          (diracMatterSpatialGalerkinSynthesis basis second input.2))).re) =
      (fun input ↦ Complex.re
        (∑ internal : InternalMatterCoordinateIndex,
          (star (fun spin ↦ internalMatterCoordinate internal
              (diracMatterSpatialGalerkinSynthesis basis first input.2 spin))) ⬝ᵥ
            (fun spin ↦ ∑ column : DiracSpinorIndex,
              matrix input.1 input.2 spin column *
                internalMatterCoordinate internal
                  (diracMatterSpatialGalerkinSynthesis basis second input.2
                    column)))) by
    funext input
    unfold diracExteriorMatterCoordinatePairing
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro internal _
    congr 1
    funext spin
    exact internalMatterCoordinate_diracMatrixMatterAction
      (matrix input.1 input.2)
      (diracMatterSpatialGalerkinSynthesis basis second input.2)
      spin internal]
  apply Complex.reCLM.contDiff.comp
  apply ContDiff.sum
  intro internal _
  unfold dotProduct
  apply ContDiff.sum
  intro spin _
  apply ContDiff.mul
  · exact Complex.conjCLE.contDiff.comp
      ((diracMatterSpatialGalerkinSynthesis_internalCoordinate_contDiff_one
        basis basisRegular first internal spin).comp contDiff_snd)
  · apply ContDiff.sum
    intro column _
    exact (matrixRegular spin column).mul
      ((diracMatterSpatialGalerkinSynthesis_internalCoordinate_contDiff_one
        basis basisRegular second internal column).comp contDiff_snd)

theorem diracMatterWeakMassDensity_continuous
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    Continuous (diracMatterWeakMassDensity matrix basis first second) := by
  unfold diracMatterWeakMassDensity diracExteriorMatterEnergyPairing
  rw [show (fun space ↦
      (diracExteriorMatterCoordinatePairing
        (diracMatterSpatialGalerkinSynthesis basis first space)
        ((diracMatrixMatterAction (matrix space))
          (diracMatterSpatialGalerkinSynthesis basis second space))).re) =
      (fun space ↦ Complex.re
        (∑ internal : InternalMatterCoordinateIndex,
          (star (fun spin ↦ internalMatterCoordinate internal
              (diracMatterSpatialGalerkinSynthesis basis first space spin))) ⬝ᵥ
            (fun spin ↦ ∑ column : DiracSpinorIndex,
              matrix space spin column *
                internalMatterCoordinate internal
                  (diracMatterSpatialGalerkinSynthesis basis second space
                    column)))) by
    funext space
    unfold diracExteriorMatterCoordinatePairing
    apply congrArg Complex.re
    apply Finset.sum_congr rfl
    intro internal _
    congr 1
    funext spin
    exact internalMatterCoordinate_diracMatrixMatterAction
      (matrix space) (diracMatterSpatialGalerkinSynthesis basis second space)
        spin internal]
  apply Complex.continuous_re.comp
  apply continuous_finsetSum Finset.univ
  intro internal _
  unfold dotProduct
  apply continuous_finsetSum Finset.univ
  intro spin _
  apply Continuous.mul
  · exact Continuous.star
      (diracMatterSpatialGalerkinSynthesis_internalCoordinate_continuous
        basis basisContinuous first internal spin)
  · apply continuous_finsetSum Finset.univ
    intro column _
    exact (matrixContinuous spin column).mul
      (diracMatterSpatialGalerkinSynthesis_internalCoordinate_continuous
        basis basisContinuous second internal column)

theorem diracMatterWeakMassDensity_add_right
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second third : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassDensity matrix basis first (second + third) =
      diracMatterWeakMassDensity matrix basis first second +
        diracMatterWeakMassDensity matrix basis first third := by
  funext space
  unfold diracMatterWeakMassDensity
  rw [diracMatterSpatialGalerkinSynthesis_add]
  simp only [Pi.add_apply]
  rw [diracExteriorMatterEnergyPairing_add_right]

theorem diracMatterWeakMassDensity_real_smul_right
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassDensity matrix basis first (parameter • second) =
      parameter • diracMatterWeakMassDensity matrix basis first second := by
  funext space
  unfold diracMatterWeakMassDensity
  rw [diracMatterSpatialGalerkinSynthesis_real_smul]
  simp only [Pi.smul_apply]
  rw [diracExteriorMatterEnergyPairing_real_smul_right]

theorem diracMatterWeakMassDensity_add_left
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second third : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassDensity matrix basis (first + second) third =
      diracMatterWeakMassDensity matrix basis first third +
        diracMatterWeakMassDensity matrix basis second third := by
  funext space
  unfold diracMatterWeakMassDensity
  rw [diracMatterSpatialGalerkinSynthesis_add]
  simp only [Pi.add_apply]
  rw [diracExteriorMatterEnergyPairing_add_left]

theorem diracMatterWeakMassDensity_real_smul_left
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassDensity matrix basis (parameter • first) second =
      parameter • diracMatterWeakMassDensity matrix basis first second := by
  funext space
  unfold diracMatterWeakMassDensity
  rw [diracMatterSpatialGalerkinSynthesis_real_smul]
  simp only [Pi.smul_apply]
  rw [diracExteriorMatterEnergyPairing_real_smul_left]

theorem diracMatterWeakMassDensity_hasCompactSupport
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    HasCompactSupport (diracMatterWeakMassDensity matrix basis first second) := by
  have firstCoordinatesCompact :=
    diracMatterSpatialGalerkinSynthesis_coordinates_hasCompactSupport
      basis basisCompact first
  rw [hasCompactSupport_iff_eventuallyEq] at firstCoordinatesCompact ⊢
  filter_upwards [firstCoordinatesCompact] with space coordinatesZero
  have firstZero :
      diracMatterSpatialGalerkinSynthesis basis first space = 0 := by
    apply matterCoordinateEquiv.injective
    simpa only [Pi.zero_apply, map_zero] using coordinatesZero
  simp [diracMatterWeakMassDensity, firstZero,
    diracExteriorMatterEnergyPairing,
    diracExteriorMatterCoordinatePairing, dotProduct]

theorem diracMatterWeakMassDensity_integrable
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    MeasureTheory.Integrable
      (diracMatterWeakMassDensity matrix basis first second) :=
  (diracMatterWeakMassDensity_continuous matrix basis matrixContinuous
    basisContinuous first second).integrable_of_hasCompactSupport
      (diracMatterWeakMassDensity_hasCompactSupport matrix basis basisCompact
        first second)

/-- The spatially integrated Hermitian weak mass pairing. -/
def diracMatterWeakMassFormValue
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) : ℝ :=
  ∫ space, diracMatterWeakMassDensity matrix basis first second space

/-- The integrated weak mass pairing varies continuously with a jointly
continuous time-dependent Dirac coefficient. -/
theorem diracMatterWeakMassFormValue_time_continuous
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    Continuous fun time ↦
      diracMatterWeakMassFormValue (matrix time) basis first second := by
  let carrier : Set DiracMatterSpatialCoordinates :=
    ⋃ mode : Fin modeCount, tsupport (basis mode)
  have carrierCompact : IsCompact carrier := by
    exact isCompact_iUnion basisCompact
  have densityContinuous : Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        diracMatterWeakMassDensity (matrix input.1) basis first second input.2 :=
    diracMatterWeakMassDensity_joint_continuous matrix basis matrixContinuous
      basisContinuous first second
  have densityZeroOutside :
      ∀ time space, time ∈ Set.univ → space ∉ carrier →
        diracMatterWeakMassDensity (matrix time) basis first second space = 0 := by
    intro time space _ spaceOutside
    have basisZero (mode : Fin modeCount) : basis mode space = 0 := by
      by_contra nonzero
      apply spaceOutside
      apply Set.mem_iUnion.2
      exact ⟨mode, subset_closure (by simpa [Function.mem_support] using nonzero)⟩
    have firstZero :
        diracMatterSpatialGalerkinSynthesis basis first space = 0 := by
      apply matterCoordinateEquiv.injective
      simp [diracMatterSpatialGalerkinSynthesis_coordinates, basisZero]
    simp [diracMatterWeakMassDensity, firstZero,
      diracExteriorMatterEnergyPairing,
      diracExteriorMatterCoordinatePairing, dotProduct]
  have integralContinuous :=
    continuousOn_integral_of_compact_support
      (X := ℝ) (Y := DiracMatterSpatialCoordinates) (E := ℝ)
      (μ := volume) (s := Set.univ) (k := carrier)
      (f := fun time space ↦
        diracMatterWeakMassDensity (matrix time) basis first second space)
      carrierCompact densityContinuous.continuousOn densityZeroOutside
  simpa [diracMatterWeakMassFormValue] using integralContinuous

/-- Time derivative of the integrated weak mass pairing, generated by the
joint derivative of its action coefficient. -/
def diracMatterWeakMassFormValueTimeDerivative
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ) : ℝ :=
  ∫ space, diracMatterSpatialEnergyTimeDerivative
    (fun candidateTime ↦
      diracMatterWeakMassDensity (matrix candidateTime) basis first second)
    time space

theorem diracMatterWeakMassFormValue_time_hasDerivAt
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixRegular : ∀ row column, ContDiff ℝ 1 fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (time : ℝ) :
    HasDerivAt
      (fun candidateTime ↦
        diracMatterWeakMassFormValue (matrix candidateTime) basis first second)
      (diracMatterWeakMassFormValueTimeDerivative matrix basis first second time)
      time := by
  let density : ℝ → DiracMatterSpatialCoordinates → ℝ :=
    fun candidateTime space ↦
      diracMatterWeakMassDensity (matrix candidateTime) basis first second space
  let carrier : Set DiracMatterSpatialCoordinates :=
    ⋃ mode : Fin modeCount, tsupport (basis mode)
  have carrierCompact : IsCompact carrier := isCompact_iUnion basisCompact
  have densityJointC1 : ContDiff ℝ 1 (Function.uncurry density) :=
    diracMatterWeakMassDensity_joint_contDiff_one matrix basis matrixRegular
      basisRegular first second
  have densityZeroOutside :
      ∀ candidateTime space, space ∉ carrier → density candidateTime space = 0 := by
    intro candidateTime space spaceOutside
    have basisZero (mode : Fin modeCount) : basis mode space = 0 := by
      by_contra nonzero
      apply spaceOutside
      apply Set.mem_iUnion.2
      exact ⟨mode, subset_closure (by simpa [Function.mem_support] using nonzero)⟩
    have firstZero :
        diracMatterSpatialGalerkinSynthesis basis first space = 0 := by
      apply matterCoordinateEquiv.injective
      simp [diracMatterSpatialGalerkinSynthesis_coordinates, basisZero]
    simp [density, diracMatterWeakMassDensity, firstZero,
      diracExteriorMatterEnergyPairing,
      diracExteriorMatterCoordinatePairing, dotProduct]
  have derivativeZeroOutside :
      ∀ candidateTime space, space ∉ carrier →
        diracMatterSpatialEnergyTimeDerivative density candidateTime space = 0 := by
    intro candidateTime space spaceOutside
    have actual := diracMatterSpatialEnergyTimeDerivative_hasDerivAt
      density densityJointC1 candidateTime space
    apply actual.unique
    convert hasDerivAt_const (x := candidateTime) (c := (0 : ℝ)) using 1
    funext varyingTime
    exact densityZeroOutside varyingTime space spaceOutside
  let jointDerivative := fderiv ℝ (Function.uncurry density)
  let compactSet := closedBall time 1 ×ˢ carrier
  have jointDerivativeContinuous : Continuous jointDerivative :=
    densityJointC1.continuous_fderiv one_ne_zero
  have compactSetCompact : IsCompact compactSet :=
    (isCompact_closedBall time (1 : ℝ)).prod carrierCompact
  have imageBounded : Bornology.IsBounded (jointDerivative '' compactSet) :=
    (compactSetCompact.image jointDerivativeContinuous).isBounded
  obtain ⟨C, _, imageSubset⟩ :
      ∃ C : ℝ, 0 < C ∧
        jointDerivative '' compactSet ⊆
          closedBall
            (0 : ℝ × DiracMatterSpatialCoordinates →L[ℝ] ℝ) C :=
    imageBounded.subset_closedBall_lt 0 0
  let timeAxis : ℝ × DiracMatterSpatialCoordinates :=
    (1, (0 : DiracMatterSpatialCoordinates))
  let bound : DiracMatterSpatialCoordinates → ℝ :=
    carrier.indicator (fun _ ↦ C * ‖timeAxis‖)
  have timeNeighborhood : closedBall time 1 ∈ nhds time :=
    mem_of_superset (ball_mem_nhds time zero_lt_one) ball_subset_closedBall
  have matrixSpatialContinuous (candidateTime : ℝ) (row column) :
      Continuous fun space ↦ matrix candidateTime space row column :=
    (matrixRegular row column).continuous.comp
      (continuous_const.prodMk continuous_id)
  have densityIntegrable : Integrable (density time) :=
    diracMatterWeakMassDensity_integrable (matrix time) basis
      (matrixSpatialContinuous time) (fun mode ↦ (basisRegular mode).continuous)
      basisCompact first second
  have derivativeMeasurable : AEStronglyMeasurable
      (diracMatterSpatialEnergyTimeDerivative density time) :=
    (diracMatterSpatialEnergyTimeDerivative_continuous density densityJointC1
      time).aestronglyMeasurable
  have derivativeBound : ∀ᵐ space ∂volume, ∀ candidateTime ∈ closedBall time 1,
      ‖diracMatterSpatialEnergyTimeDerivative density candidateTime space‖ ≤
        bound space := by
    filter_upwards with space
    intro candidateTime candidateTimeMem
    by_cases spaceMem : space ∈ carrier
    · have pairMem : (candidateTime, space) ∈ compactSet :=
        ⟨candidateTimeMem, spaceMem⟩
      have derivativeMem : jointDerivative (candidateTime, space) ∈
          closedBall
            (0 : ℝ × DiracMatterSpatialCoordinates →L[ℝ] ℝ) C :=
        imageSubset (mem_image_of_mem jointDerivative pairMem)
      have operatorBound : ‖jointDerivative (candidateTime, space)‖ ≤ C := by
        simpa only [mem_closedBall_zero_iff] using derivativeMem
      calc
        ‖diracMatterSpatialEnergyTimeDerivative density candidateTime space‖ =
            ‖jointDerivative (candidateTime, space) timeAxis‖ := rfl
        _ ≤ ‖jointDerivative (candidateTime, space)‖ * ‖timeAxis‖ :=
          (jointDerivative (candidateTime, space)).le_opNorm timeAxis
        _ ≤ C * ‖timeAxis‖ :=
          mul_le_mul_of_nonneg_right operatorBound (norm_nonneg _)
        _ = bound space := by simp [bound, spaceMem]
    · rw [derivativeZeroOutside candidateTime space spaceMem]
      simp [bound, spaceMem]
  have boundIntegrable : Integrable bound :=
    (integrableOn_const carrierCompact.measure_ne_top).integrable_indicator
      carrierCompact.measurableSet
  have result := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := density)
      (F' := fun candidateTime space ↦
        diracMatterSpatialEnergyTimeDerivative density candidateTime space)
      (bound := bound)
      timeNeighborhood
      (by
        filter_upwards with candidateTime
        exact (densityJointC1.continuous.comp
          (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      densityIntegrable derivativeMeasurable derivativeBound boundIntegrable
      (by
        filter_upwards with space candidateTime _
        exact diracMatterSpatialEnergyTimeDerivative_hasDerivAt
          density densityJointC1 candidateTime space)).2
  simpa [density, diracMatterWeakMassFormValue,
    diracMatterWeakMassFormValueTimeDerivative] using result

theorem diracMatterWeakMassFormValueTimeDerivative_continuous
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixRegular : ∀ row column, ContDiff ℝ 1 fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    Continuous
      (diracMatterWeakMassFormValueTimeDerivative matrix basis first second) := by
  let density : ℝ → DiracMatterSpatialCoordinates → ℝ :=
    fun candidateTime space ↦
      diracMatterWeakMassDensity (matrix candidateTime) basis first second space
  let carrier : Set DiracMatterSpatialCoordinates :=
    ⋃ mode : Fin modeCount, tsupport (basis mode)
  have carrierCompact : IsCompact carrier := isCompact_iUnion basisCompact
  have densityJointC1 : ContDiff ℝ 1 (Function.uncurry density) :=
    diracMatterWeakMassDensity_joint_contDiff_one matrix basis matrixRegular
      basisRegular first second
  have derivativeJointContinuous : Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        diracMatterSpatialEnergyTimeDerivative density input.1 input.2 := by
    unfold diracMatterSpatialEnergyTimeDerivative
    exact (densityJointC1.continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have derivativeZeroOutside :
      ∀ candidateTime space, candidateTime ∈ Set.univ → space ∉ carrier →
        diracMatterSpatialEnergyTimeDerivative density candidateTime space = 0 := by
    intro candidateTime space _ spaceOutside
    have basisZero (mode : Fin modeCount) : basis mode space = 0 := by
      by_contra nonzero
      apply spaceOutside
      apply Set.mem_iUnion.2
      exact ⟨mode, subset_closure (by simpa [Function.mem_support] using nonzero)⟩
    have densityZero (varyingTime : ℝ) : density varyingTime space = 0 := by
      have firstZero :
          diracMatterSpatialGalerkinSynthesis basis first space = 0 := by
        apply matterCoordinateEquiv.injective
        simp [diracMatterSpatialGalerkinSynthesis_coordinates, basisZero]
      simp [density, diracMatterWeakMassDensity, firstZero,
        diracExteriorMatterEnergyPairing,
        diracExteriorMatterCoordinatePairing, dotProduct]
    have actual := diracMatterSpatialEnergyTimeDerivative_hasDerivAt
      density densityJointC1 candidateTime space
    apply actual.unique
    convert hasDerivAt_const (x := candidateTime) (c := (0 : ℝ)) using 1
    funext varyingTime
    exact densityZero varyingTime
  have integralContinuous :=
    continuousOn_integral_of_compact_support
      (X := ℝ) (Y := DiracMatterSpatialCoordinates) (E := ℝ)
      (μ := volume) (s := Set.univ) (k := carrier)
      (f := fun candidateTime space ↦
        diracMatterSpatialEnergyTimeDerivative density candidateTime space)
      carrierCompact derivativeJointContinuous.continuousOn
      derivativeZeroOutside
  change Continuous fun candidateTime ↦
    ∫ space, diracMatterSpatialEnergyTimeDerivative density candidateTime space
  exact continuousOn_univ.mp integralContinuous

theorem diracMatterWeakMassFormValue_time_contDiff_one
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixRegular : ∀ row column, ContDiff ℝ 1 fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    ContDiff ℝ 1 fun time ↦
      diracMatterWeakMassFormValue (matrix time) basis first second := by
  rw [contDiff_one_iff_deriv]
  constructor
  · intro time
    exact (diracMatterWeakMassFormValue_time_hasDerivAt matrix basis
      matrixRegular basisRegular basisCompact first second time).differentiableAt
  · have derivEq :
        deriv (fun time ↦
          diracMatterWeakMassFormValue (matrix time) basis first second) =
        diracMatterWeakMassFormValueTimeDerivative matrix basis first second := by
      funext time
      exact (diracMatterWeakMassFormValue_time_hasDerivAt matrix basis
        matrixRegular basisRegular basisCompact first second time).deriv
    rw [derivEq]
    exact diracMatterWeakMassFormValueTimeDerivative_continuous matrix basis
      matrixRegular basisRegular basisCompact first second

theorem diracMatterWeakMassFormValue_add_right
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second third : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassFormValue matrix basis first (second + third) =
      diracMatterWeakMassFormValue matrix basis first second +
        diracMatterWeakMassFormValue matrix basis first third := by
  unfold diracMatterWeakMassFormValue
  rw [diracMatterWeakMassDensity_add_right]
  simp only [Pi.add_apply]
  rw [integral_add
      (diracMatterWeakMassDensity_integrable matrix basis matrixContinuous
        basisContinuous basisCompact first second)
      (diracMatterWeakMassDensity_integrable matrix basis matrixContinuous
        basisContinuous basisCompact first third)]

theorem diracMatterWeakMassFormValue_real_smul_right
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassFormValue matrix basis first (parameter • second) =
      parameter • diracMatterWeakMassFormValue matrix basis first second := by
  unfold diracMatterWeakMassFormValue
  rw [diracMatterWeakMassDensity_real_smul_right]
  simp only [Pi.smul_apply]
  rw [integral_smul]

theorem diracMatterWeakMassFormValue_add_left
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second third : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassFormValue matrix basis (first + second) third =
      diracMatterWeakMassFormValue matrix basis first third +
        diracMatterWeakMassFormValue matrix basis second third := by
  unfold diracMatterWeakMassFormValue
  rw [diracMatterWeakMassDensity_add_left]
  simp only [Pi.add_apply]
  rw [integral_add
      (diracMatterWeakMassDensity_integrable matrix basis matrixContinuous
        basisContinuous basisCompact first third)
      (diracMatterWeakMassDensity_integrable matrix basis matrixContinuous
        basisContinuous basisCompact second third)]

theorem diracMatterWeakMassFormValue_real_smul_left
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (parameter : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassFormValue matrix basis (parameter • first) second =
      parameter • diracMatterWeakMassFormValue matrix basis first second := by
  unfold diracMatterWeakMassFormValue
  rw [diracMatterWeakMassDensity_real_smul_left]
  simp only [Pi.smul_apply]
  rw [integral_smul]

/-- The second coefficient leg of the spatial weak mass form. -/
def diracMatterWeakMassInnerLinear
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first : DiracMatterGalerkinCoefficient modeCount) :
    DiracMatterGalerkinCoefficient modeCount →ₗ[ℝ] ℝ where
  toFun second := diracMatterWeakMassFormValue matrix basis first second
  map_add' := diracMatterWeakMassFormValue_add_right matrix basis
    matrixContinuous basisContinuous basisCompact first
  map_smul' := by
    intro parameter second
    simpa using diracMatterWeakMassFormValue_real_smul_right matrix basis
      parameter first second

/-- The inner weak mass leg is automatically continuous in finite
coefficient dimension. -/
def diracMatterWeakMassInnerCLM
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first : DiracMatterGalerkinCoefficient modeCount) :
    DiracMatterGalerkinCoefficient modeCount →L[ℝ] ℝ :=
  (diracMatterWeakMassInnerLinear matrix basis matrixContinuous
    basisContinuous basisCompact first).toContinuousLinearMap

/-- The complete real-bilinear weak mass form before Riesz realization. -/
def diracMatterWeakMassFormLinear
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    DiracMatterGalerkinCoefficient modeCount →ₗ[ℝ]
      (DiracMatterGalerkinCoefficient modeCount →L[ℝ] ℝ) where
  toFun first := diracMatterWeakMassInnerCLM matrix basis matrixContinuous
    basisContinuous basisCompact first
  map_add' first second := by
    ext third
    exact diracMatterWeakMassFormValue_add_left matrix basis matrixContinuous
      basisContinuous basisCompact first second third
  map_smul' parameter first := by
    ext second
    change diracMatterWeakMassFormValue matrix basis (parameter • first) second =
      parameter • diracMatterWeakMassFormValue matrix basis first second
    simpa using diracMatterWeakMassFormValue_real_smul_left matrix basis
      parameter first second

/-- The integrated Hermitian weak mass form as the bounded bilinear input to
the Riesz mass producer. -/
def diracMatterWeakMassForm
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    DiracMatterGalerkinCoefficient modeCount →L[ℝ]
      (DiracMatterGalerkinCoefficient modeCount →L[ℝ] ℝ) :=
  (diracMatterWeakMassFormLinear matrix basis matrixContinuous
    basisContinuous basisCompact).toContinuousLinearMap

@[simp] theorem diracMatterWeakMassForm_apply
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    diracMatterWeakMassForm matrix basis matrixContinuous basisContinuous
        basisCompact first second =
      diracMatterWeakMassFormValue matrix basis first second :=
  rfl

/-- Joint time-space continuity restricts to a continuous spatial coefficient
at each time. -/
theorem diracMatterWeakMassMatrix_spatial_continuous
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (matrixContinuous : ∀ row column, Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (time : ℝ)
    (row column : DiracSpinorIndex) :
    Continuous fun space ↦ matrix time space row column :=
  (matrixContinuous row column).comp (continuous_const.prodMk continuous_id)

/-- The complete integrated weak mass form is continuous in time. -/
theorem diracMatterWeakMassForm_time_continuous
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    Continuous fun time ↦
      diracMatterWeakMassForm (matrix time) basis
        (diracMatterWeakMassMatrix_spatial_continuous matrix matrixContinuous time)
        basisContinuous basisCompact := by
  rw [continuous_clm_apply]
  intro first
  rw [continuous_clm_apply]
  intro second
  change Continuous fun time ↦
    diracMatterWeakMassFormValue (matrix time) basis first second
  exact diracMatterWeakMassFormValue_time_continuous matrix basis
    matrixContinuous basisContinuous basisCompact first second

/-- A jointly `C¹` action coefficient and `C¹` compactly supported basis
generate a `C¹` weak mass form. -/
theorem diracMatterWeakMassForm_time_contDiff_one
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixRegular : ∀ row column, ContDiff ℝ 1 fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisRegular : ∀ mode, ContDiff ℝ 1 (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode)) :
    ContDiff ℝ 1 fun time ↦
      diracMatterWeakMassForm (matrix time) basis
        (diracMatterWeakMassMatrix_spatial_continuous matrix
          (fun row column ↦ (matrixRegular row column).continuous) time)
        (fun mode ↦ (basisRegular mode).continuous) basisCompact := by
  rw [contDiff_clm_apply_iff]
  intro first
  rw [contDiff_clm_apply_iff]
  intro second
  change ContDiff ℝ 1 fun time ↦
    diracMatterWeakMassFormValue (matrix time) basis first second
  exact diracMatterWeakMassFormValue_time_contDiff_one matrix basis
    matrixRegular basisRegular basisCompact first second

@[simp] theorem diracMatterWeakMassDensity_self
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (space : DiracMatterSpatialCoordinates) :
    diracMatterWeakMassDensity matrix basis coefficient coefficient space =
      diracExteriorMatterCoordinateEnergy (matrix space)
        (diracMatterSpatialGalerkinSynthesis basis coefficient space) :=
  rfl

/-- A pointwise positive-semidefinite time coefficient makes the integrated
weak mass energy nonnegative, without any faithfulness assumption on the
finite synthesis. -/
theorem diracMatterWeakMassForm_nonnegative
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (matrixNonnegative : ∀ space, Matrix.PosSemidef (matrix space))
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    0 ≤ diracMatterWeakMassForm matrix basis matrixContinuous basisContinuous
      basisCompact coefficient coefficient := by
  rw [diracMatterWeakMassForm_apply]
  unfold diracMatterWeakMassFormValue
  apply integral_nonneg_of_ae
  filter_upwards with space
  rw [diracMatterWeakMassDensity_self]
  exact diracExteriorMatterCoordinateEnergy_nonneg (matrix space)
    (matrixNonnegative space)
    (diracMatterSpatialGalerkinSynthesis basis coefficient space)

/-- Pointwise positive Dirac time coefficients make the integrated weak mass
form strictly positive whenever the finite synthesis is faithful. -/
theorem diracMatterWeakMassForm_positive
    (matrix : DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun space ↦
      matrix space row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (matrixPositive : ∀ space, Matrix.PosDef (matrix space))
    (synthesisFaithful : ∀ coefficient : DiracMatterGalerkinCoefficient modeCount,
      coefficient ≠ 0 → ∃ space,
        diracMatterSpatialGalerkinSynthesis basis coefficient space ≠ 0)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (coefficientNonzero : coefficient ≠ 0) :
    0 < diracMatterWeakMassForm matrix basis matrixContinuous basisContinuous
      basisCompact coefficient coefficient := by
  rw [diracMatterWeakMassForm_apply]
  unfold diracMatterWeakMassFormValue
  have densityContinuous :=
    diracMatterWeakMassDensity_continuous matrix basis matrixContinuous
      basisContinuous coefficient coefficient
  have densityIntegrable :=
    diracMatterWeakMassDensity_integrable matrix basis matrixContinuous
      basisContinuous basisCompact coefficient coefficient
  have densityNonnegative :
      0 ≤ diracMatterWeakMassDensity matrix basis coefficient coefficient := by
    intro space
    rw [diracMatterWeakMassDensity_self]
    exact diracExteriorMatterCoordinateEnergy_nonneg (matrix space)
      (matrixPositive space).posSemidef
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)
  obtain ⟨space, fieldNonzero⟩ :=
    synthesisFaithful coefficient coefficientNonzero
  have densityNonzero :
      diracMatterWeakMassDensity matrix basis coefficient coefficient space ≠ 0 := by
    rw [diracMatterWeakMassDensity_self]
    exact (diracExteriorMatterCoordinateEnergy_pos (matrix space)
      (matrixPositive space)
      (diracMatterSpatialGalerkinSynthesis basis coefficient space)
      fieldNonzero).ne'
  exact MeasureTheory.integral_pos_of_integrable_nonneg_nonzero
    densityContinuous densityIntegrable densityNonnegative densityNonzero

/-- Pointwise positivity makes the complete time-dependent weak mass form
strictly positive. -/
theorem diracMatterWeakMassForm_time_positive
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (matrixPositive : ∀ time space, Matrix.PosDef (matrix time space))
    (synthesisFaithful : ∀ coefficient : DiracMatterGalerkinCoefficient modeCount,
      coefficient ≠ 0 → ∃ space,
        diracMatterSpatialGalerkinSynthesis basis coefficient space ≠ 0)
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (coefficientNonzero : coefficient ≠ 0) :
    0 < diracMatterWeakMassForm (matrix time) basis
      (diracMatterWeakMassMatrix_spatial_continuous matrix matrixContinuous time)
      basisContinuous basisCompact coefficient coefficient := by
  exact diracMatterWeakMassForm_positive (matrix time) basis
    (diracMatterWeakMassMatrix_spatial_continuous matrix matrixContinuous time)
    basisContinuous basisCompact (matrixPositive time) synthesisFaithful
    coefficient coefficientNonzero

/-- The action-owned time-dependent weak mass operator is invertible without
accepting an inverse as input. -/
theorem diracMatterWeakMassOperator_isInvertible
    (matrix : ℝ → DiracMatterSpatialCoordinates → DiracMatrix)
    (basis : Fin modeCount → DiracMatterSpatialCoordinates → ℝ)
    (matrixContinuous : ∀ row column, Continuous fun input :
      ℝ × DiracMatterSpatialCoordinates ↦
        matrix input.1 input.2 row column)
    (basisContinuous : ∀ mode, Continuous (basis mode))
    (basisCompact : ∀ mode, HasCompactSupport (basis mode))
    (matrixPositive : ∀ time space, Matrix.PosDef (matrix time space))
    (synthesisFaithful : ∀ coefficient : DiracMatterGalerkinCoefficient modeCount,
      coefficient ≠ 0 → ∃ space,
        diracMatterSpatialGalerkinSynthesis basis coefficient space ≠ 0)
    (time : ℝ) :
    (galerkinWeakMassOperator (fun time ↦
      diracMatterWeakMassForm (matrix time) basis
        (diracMatterWeakMassMatrix_spatial_continuous matrix matrixContinuous time)
        basisContinuous basisCompact) time).IsInvertible := by
  exact galerkinWeakMassOperator_isInvertible _ time
    (diracMatterWeakMassForm_time_positive matrix basis matrixContinuous
      basisContinuous basisCompact matrixPositive synthesisFaithful time)

end WeakMassDensity

end

end SaturationMonoid.PhysicsCore.StageNineDiracMatterWeakSpatialGalerkinMass
