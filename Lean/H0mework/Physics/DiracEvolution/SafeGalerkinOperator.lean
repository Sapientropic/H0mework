import H0mework.Physics.DiracEvolution.GalerkinEvolution
import H0mework.Physics.DiracEvolution.SafeVolterraOperator

/-!
# Cauchy-safe Dirac Galerkin operator

A finite real spatial basis synthesizes candidate matter sections.  The fixed
current's mother-action velocity is then sampled into one real-linear,
finite-dimensional coefficient operator whose continuous time paths generate
local Galerkin evolution.
-/

namespace
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator

open DiracExteriorMatterAction
open ProofFreeRicherAnholonomicSource
open StageNineCanonicalCauchyState
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracMatterGalerkinEvolution
open StageNineHolonomicField
open StageNineMatterActionTemporalFirstGermResponse
open scoped NNReal

noncomputable section

set_option autoImplicit false

variable {modeCount : ℕ}

abbrev DiracMatterGalerkinCoefficient (modeCount : ℕ) :=
  EuclideanSpace ℂ (Fin modeCount × MatterCoordinateIndex)

def diracMatterGalerkinCoefficientMode
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (mode : Fin modeCount) : MatterCoordinateCarrier :=
  WithLp.toLp 2 fun index ↦ coefficient (mode, index)

@[simp] theorem diracMatterGalerkinCoefficientMode_add
    (first second : DiracMatterGalerkinCoefficient modeCount)
    (mode : Fin modeCount) :
    diracMatterGalerkinCoefficientMode (first + second) mode =
      diracMatterGalerkinCoefficientMode first mode +
        diracMatterGalerkinCoefficientMode second mode := by
  ext index
  rfl

@[simp] theorem diracMatterGalerkinCoefficientMode_real_smul
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (mode : Fin modeCount) :
    diracMatterGalerkinCoefficientMode (parameter • coefficient) mode =
      parameter • diracMatterGalerkinCoefficientMode coefficient mode := by
  ext index
  rfl

/-- A finite real spatial basis synthesizes a genuine matter section. -/
def cauchySafeMatterGalerkinSynthesis
    (basis : Fin modeCount → BasePoint → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (point : BasePoint) : DiracExteriorMatterCarrier :=
  matterCoordinateEquiv.symm
    (∑ mode, basis mode point •
      diracMatterGalerkinCoefficientMode coefficient mode)

@[simp] theorem cauchySafeMatterGalerkinSynthesis_coordinates
    (basis : Fin modeCount → BasePoint → ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (point : BasePoint) :
    matterCoordinateEquiv
        (cauchySafeMatterGalerkinSynthesis basis coefficient point) =
      ∑ mode, basis mode point •
        diracMatterGalerkinCoefficientMode coefficient mode := by
  simp [cauchySafeMatterGalerkinSynthesis]

theorem cauchySafeMatterGalerkinSynthesis_add
    (basis : Fin modeCount → BasePoint → ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    cauchySafeMatterGalerkinSynthesis basis (first + second) =
      cauchySafeMatterGalerkinSynthesis basis first +
        cauchySafeMatterGalerkinSynthesis basis second := by
  funext point
  apply matterCoordinateEquiv.injective
  simp only [cauchySafeMatterGalerkinSynthesis_coordinates,
    diracMatterGalerkinCoefficientMode_add, smul_add,
    Finset.sum_add_distrib, Pi.add_apply, map_add]

theorem cauchySafeMatterGalerkinSynthesis_real_smul
    (basis : Fin modeCount → BasePoint → ℝ)
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    cauchySafeMatterGalerkinSynthesis basis (parameter • coefficient) =
      parameter • cauchySafeMatterGalerkinSynthesis basis coefficient := by
  funext point
  apply matterCoordinateEquiv.injective
  simp only [cauchySafeMatterGalerkinSynthesis_coordinates,
    diracMatterGalerkinCoefficientMode_real_smul, Pi.smul_apply,
    matterCoordinateEquiv_real_smul]
  change
    (∑ mode, (basis mode point : ℂ) •
      ((parameter : ℂ) •
        diracMatterGalerkinCoefficientMode coefficient mode)) =
      (parameter : ℂ) •
        (∑ mode, (basis mode point : ℂ) •
          diracMatterGalerkinCoefficientMode coefficient mode)
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro mode _
  rw [smul_smul, smul_smul, mul_comm]

theorem cauchySafeMatterGalerkinSynthesis_differentiableAt
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode))
    (coefficient : DiracMatterGalerkinCoefficient modeCount)
    (point : BasePoint) :
    DifferentiableAt ℝ
      (fun position ↦ matterCoordinateEquiv
        (cauchySafeMatterGalerkinSynthesis basis coefficient position))
      point := by
  simp only [cauchySafeMatterGalerkinSynthesis_coordinates]
  exact DifferentiableAt.fun_sum fun mode _ ↦
    (basisDifferentiable mode point).smul_const
      (diracMatterGalerkinCoefficientMode coefficient mode)

/-- Collocation of the action-native velocity at the selected spatial
points. -/
def cauchySafeMatterGalerkinAction
    (current : StageNineHolonomicConfiguration)
    (basis : Fin modeCount → BasePoint → ℝ)
    (sample : Fin modeCount → StageNineSpatialPoint)
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    DiracMatterGalerkinCoefficient modeCount :=
  WithLp.toLp 2 fun index ↦
    cauchySafeMatterVolterraVelocity current
      (cauchySafeMatterGalerkinSynthesis basis coefficient)
      (canonicalCauchySlicePoint time (sample index.1)) index.2

theorem cauchySafeMatterGalerkinAction_add
    (current : StageNineHolonomicConfiguration)
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode))
    (sample : Fin modeCount → StageNineSpatialPoint)
    (time : ℝ)
    (first second : DiracMatterGalerkinCoefficient modeCount) :
    cauchySafeMatterGalerkinAction current basis sample time
        (first + second) =
      cauchySafeMatterGalerkinAction current basis sample time first +
        cauchySafeMatterGalerkinAction current basis sample time second := by
  ext index
  unfold cauchySafeMatterGalerkinAction
  rw [cauchySafeMatterGalerkinSynthesis_add]
  exact congrArg (fun coordinates : MatterCoordinateCarrier ↦
    coordinates index.2)
    (cauchySafeMatterVolterraVelocity_add current _ _ _
      (cauchySafeMatterGalerkinSynthesis_differentiableAt basis
        basisDifferentiable first _)
      (cauchySafeMatterGalerkinSynthesis_differentiableAt basis
        basisDifferentiable second _))

theorem cauchySafeMatterGalerkinAction_real_smul
    (current : StageNineHolonomicConfiguration)
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode))
    (sample : Fin modeCount → StageNineSpatialPoint)
    (time : ℝ)
    (parameter : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    cauchySafeMatterGalerkinAction current basis sample time
        (parameter • coefficient) =
      parameter •
        cauchySafeMatterGalerkinAction current basis sample time coefficient := by
  ext index
  unfold cauchySafeMatterGalerkinAction
  rw [cauchySafeMatterGalerkinSynthesis_real_smul]
  exact congrArg (fun coordinates : MatterCoordinateCarrier ↦
    coordinates index.2)
    (cauchySafeMatterVolterraVelocity_real_smul current _ parameter _
      (cauchySafeMatterGalerkinSynthesis_differentiableAt basis
        basisDifferentiable coefficient _))

/-- The sampled mother-action velocity as a real-linear coefficient map. -/
def cauchySafeMatterGalerkinActionLinear
    (current : StageNineHolonomicConfiguration)
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode))
    (sample : Fin modeCount → StageNineSpatialPoint)
    (time : ℝ) :
    DiracMatterGalerkinCoefficient modeCount →ₗ[ℝ]
      DiracMatterGalerkinCoefficient modeCount where
  toFun := cauchySafeMatterGalerkinAction current basis sample time
  map_add' := cauchySafeMatterGalerkinAction_add current basis
    basisDifferentiable sample time
  map_smul' := cauchySafeMatterGalerkinAction_real_smul current basis
    basisDifferentiable sample time

/-- The finite coefficient action is automatically continuous. -/
def cauchySafeMatterGalerkinActionCLM
    (current : StageNineHolonomicConfiguration)
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode))
    (sample : Fin modeCount → StageNineSpatialPoint)
    (time : ℝ) :
    DiracMatterGalerkinCoefficient modeCount →L[ℝ]
      DiracMatterGalerkinCoefficient modeCount :=
  ⟨cauchySafeMatterGalerkinActionLinear current basis basisDifferentiable
      sample time,
    (cauchySafeMatterGalerkinActionLinear current basis basisDifferentiable
      sample time).continuous_of_finiteDimensional⟩

@[simp] theorem cauchySafeMatterGalerkinActionCLM_apply
    (current : StageNineHolonomicConfiguration)
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode))
    (sample : Fin modeCount → StageNineSpatialPoint)
    (time : ℝ)
    (coefficient : DiracMatterGalerkinCoefficient modeCount) :
    cauchySafeMatterGalerkinActionCLM current basis basisDifferentiable sample
        time coefficient =
      cauchySafeMatterGalerkinAction current basis sample time coefficient :=
  rfl

/-- A continuous action-generated coefficient operator produces a local
Galerkin curve through the supplied coefficient data. -/
theorem exists_cauchySafeMatterGalerkinCoefficientCurve
    (current : StageNineHolonomicConfiguration)
    (basis : Fin modeCount → BasePoint → ℝ)
    (basisDifferentiable : ∀ mode, Differentiable ℝ (basis mode))
    (sample : Fin modeCount → StageNineSpatialPoint)
    (operatorContinuous : Continuous fun time ↦
      cauchySafeMatterGalerkinActionCLM current basis basisDifferentiable
        sample time)
    (initial : DiracMatterGalerkinCoefficient modeCount)
    (initialTime : ℝ) :
    ∃ bound : ℝ≥0,
      ∃ coefficient : ℝ → DiracMatterGalerkinCoefficient modeCount,
        coefficient initialTime = initial ∧
          ∀ time ∈
            Set.Icc
              (initialTime - galerkinLinearLocalTimeRadius bound initial)
              (initialTime + galerkinLinearLocalTimeRadius bound initial),
            HasDerivWithinAt coefficient
              (cauchySafeMatterGalerkinActionCLM current basis
                basisDifferentiable sample time (coefficient time))
              (Set.Icc
                (initialTime - galerkinLinearLocalTimeRadius bound initial)
                (initialTime + galerkinLinearLocalTimeRadius bound initial))
              time := by
  obtain ⟨bound, coefficient, generated⟩ :=
    exists_galerkinLinearCoefficientCurve_of_continuous
      (cauchySafeMatterGalerkinActionCLM current basis basisDifferentiable sample)
      operatorContinuous initial initialTime
  exact ⟨bound, coefficient, generated.1, generated.2.2⟩

end

end
  SaturationMonoid.PhysicsCore.StageNineDiracDualFormNativeCauchySafeMatterGalerkinOperator
