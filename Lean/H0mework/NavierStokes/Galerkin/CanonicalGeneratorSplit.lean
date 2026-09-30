import H0mework.NavierStokes.Galerkin.CommonTimeExistence
import H0mework.NavierStokes.Galerkin.ViscousRestartDerivativeLoss

/-!
# Canonical nonlinear/viscous split of the local generator bound

The quantified local Picard producer uses the canonical supremum norm of the
actual transverse-support projected Galerkin generator on one carrier ball.
This module splits that canonical bound into two independently generated
pieces:

```text
Fν ≤ F₀ + |ν| V₁.
```

Here `F₀` is the canonical projected nonlinear field bound and `V₁` is the
canonical projected unit-viscosity two-derivative field bound on the same
ball.  Thus viscosity is no longer hidden only in an existential local ODE
constant.  The split is a readout of the actual generator and its exact
viscous tangent, not a new PDE continuation premise.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCanonicalGeneratorSplit

open scoped BigOperators ENNReal

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
open ThreeDimensionalVorticityCoefficientFiniteGalerkinViscousRestartDerivativeLoss

noncomputable section

/-! ## Exact projected viscous tangent -/

/-- Transverse-support projection of the actual positive viscous tangent. -/
def projectedViscousTangent
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    ComplexVorticityHilbertState :=
  finiteTransverseSupportProjection modes
    (finiteStateVorticityViscousTangent modes ν state)

/-- The complete generator is its zero-viscosity nonlinear field minus the
actual viscous tangent. -/
theorem finiteStateVorticityGenerator_eq_nonlinear_sub_viscous
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityGenerator modes ν state =
      finiteStateVorticityGenerator modes 0 state -
        finiteStateVorticityViscousTangent modes ν state := by
  apply lp.ext
  funext wave
  change
    finiteStateVorticityGenerator modes ν state wave =
      finiteStateVorticityGenerator modes 0 state wave -
        finiteStateVorticityViscousTangent modes ν state wave
  rw [finiteStateVorticityGenerator_apply,
    finiteStateVorticityGenerator_apply]
  by_cases waveMem : wave ∈ modes
  · rw [if_pos waveMem, if_pos waveMem]
    simp [finiteStateVorticityViscousTangent, waveMem]
  · rw [if_neg waveMem, if_neg waveMem]
    simp [finiteStateVorticityViscousTangent, waveMem]

/-- Exact split after the same transverse-support observation used by the
quantified Picard producer. -/
theorem projectedGenerator_eq_nonlinear_sub_viscous
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    finiteStateTransverseProjectedGenerator modes ν state =
      finiteStateTransverseProjectedGenerator modes 0 state -
        projectedViscousTangent modes ν state := by
  unfold finiteStateTransverseProjectedGenerator
    projectedViscousTangent
  rw [finiteStateVorticityGenerator_eq_nonlinear_sub_viscous,
    map_sub]

/-- Viscosity scales the projected viscous tangent exactly. -/
theorem projectedViscousTangent_eq_smul_unit
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    projectedViscousTangent modes ν state =
      ν • projectedViscousTangent modes 1 state := by
  unfold projectedViscousTangent
  rw [← map_smul]
  congr 1
  apply lp.ext
  funext wave
  simp [finiteStateVorticityViscousTangent,
    mul_smul]

/-! ## Canonical projected viscous bound -/

def projectedViscousNormRange
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) : Set ℝ :=
  (fun state : ComplexVorticityHilbertState =>
    ‖projectedViscousTangent modes ν state‖) ''
      Metric.closedBall
        (0 : ComplexVorticityHilbertState) radius

theorem projectedViscousNormRange_nonempty
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    (projectedViscousNormRange modes ν radius).Nonempty := by
  refine
    ⟨‖projectedViscousTangent modes ν 0‖,
      0, ?_, rfl⟩
  simp

theorem projectedViscousNormRange_bddAbove
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    BddAbove (projectedViscousNormRange modes ν radius) := by
  let nonlinearBound :=
    canonicalProjectedGeneratorFieldBound modes 0 radius
  let completeBound :=
    canonicalProjectedGeneratorFieldBound modes ν radius
  refine
    ⟨(nonlinearBound : ℝ) + (completeBound : ℝ), ?_⟩
  rintro value ⟨state, stateMem, rfl⟩
  have viscousEq :
      projectedViscousTangent modes ν state =
        finiteStateTransverseProjectedGenerator modes 0 state -
          finiteStateTransverseProjectedGenerator modes ν state := by
    calc
      projectedViscousTangent modes ν state =
          finiteStateTransverseProjectedGenerator modes 0 state -
            (finiteStateTransverseProjectedGenerator modes 0 state -
              projectedViscousTangent modes ν state) := by
        abel
      _ =
          finiteStateTransverseProjectedGenerator modes 0 state -
            finiteStateTransverseProjectedGenerator modes ν state := by
        rw [←
          projectedGenerator_eq_nonlinear_sub_viscous
            modes ν state]
  change
    ‖projectedViscousTangent modes ν state‖ ≤
      (nonlinearBound : ℝ) + (completeBound : ℝ)
  rw [viscousEq]
  have nonlinearLe :=
    projectedGenerator_norm_le_canonicalFieldBound
      modes 0 radius state stateMem
  have completeLe :=
    projectedGenerator_norm_le_canonicalFieldBound
      modes ν radius state stateMem
  exact
    (norm_sub_le _ _).trans
      (add_le_add nonlinearLe completeLe)

def projectedViscousFieldNormSup
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) : ℝ :=
  sSup (projectedViscousNormRange modes ν radius)

theorem projectedViscousFieldNormSup_nonneg
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    0 ≤ projectedViscousFieldNormSup modes ν radius := by
  let zeroValue :=
    ‖projectedViscousTangent modes ν 0‖
  have zeroValueMem :
      zeroValue ∈ projectedViscousNormRange modes ν radius := by
    refine ⟨0, ?_, rfl⟩
    simp
  exact
    (norm_nonneg _).trans
      (le_csSup
        (projectedViscousNormRange_bddAbove
          modes ν radius)
        zeroValueMem)

def canonicalProjectedViscousFieldBound
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) : NNReal :=
  ⟨projectedViscousFieldNormSup modes ν radius,
    projectedViscousFieldNormSup_nonneg modes ν radius⟩

@[simp] theorem coe_canonicalProjectedViscousFieldBound
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    (canonicalProjectedViscousFieldBound
      modes ν radius : ℝ) =
        projectedViscousFieldNormSup modes ν radius :=
  rfl

theorem projectedViscous_norm_le_canonicalFieldBound
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal)
    (state : ComplexVorticityHilbertState)
    (stateMem :
      state ∈
        Metric.closedBall
          (0 : ComplexVorticityHilbertState) radius) :
    ‖projectedViscousTangent modes ν state‖ ≤
      canonicalProjectedViscousFieldBound modes ν radius := by
  exact
    le_csSup
      (projectedViscousNormRange_bddAbove modes ν radius)
      ⟨state, stateMem, rfl⟩

theorem canonicalProjectedViscousFieldBound_le
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal)
    (bound : ℝ)
    (bounds :
      ∀ state ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) radius,
        ‖projectedViscousTangent modes ν state‖ ≤
          bound) :
    (canonicalProjectedViscousFieldBound
        modes ν radius : ℝ) ≤
      bound := by
  apply csSup_le
    (projectedViscousNormRange_nonempty modes ν radius)
  intro value valueMem
  rcases valueMem with ⟨state, stateMem, rfl⟩
  exact bounds state stateMem

/-! ## Canonical viscosity split -/

/-- The canonical complete field bound is controlled by the independently
generated nonlinear and viscous canonical bounds on the same carrier. -/
theorem canonicalProjectedGeneratorFieldBound_le_nonlinear_add_viscous
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    (canonicalProjectedGeneratorFieldBound
        modes ν radius : ℝ) ≤
      canonicalProjectedGeneratorFieldBound modes 0 radius +
        canonicalProjectedViscousFieldBound modes ν radius := by
  apply canonicalProjectedGeneratorFieldBound_le
  intro state stateMem
  rw [projectedGenerator_eq_nonlinear_sub_viscous]
  exact
    (norm_sub_le _ _).trans
      (add_le_add
        (projectedGenerator_norm_le_canonicalFieldBound
          modes 0 radius state stateMem)
        (projectedViscous_norm_le_canonicalFieldBound
          modes ν radius state stateMem))

/-- The canonical viscous field bound is at most `|ν|` times the canonical
unit-viscosity two-derivative bound. -/
theorem canonicalProjectedViscousFieldBound_le_abs_mul_unit
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    (canonicalProjectedViscousFieldBound
        modes ν radius : ℝ) ≤
      |ν| *
        canonicalProjectedViscousFieldBound modes 1 radius := by
  apply canonicalProjectedViscousFieldBound_le
  intro state stateMem
  rw [projectedViscousTangent_eq_smul_unit,
    norm_smul, Real.norm_eq_abs]
  exact
    mul_le_mul_of_nonneg_left
      (projectedViscous_norm_le_canonicalFieldBound
        modes 1 radius state stateMem)
      (abs_nonneg ν)

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCanonicalGeneratorSplit
end NavierStokes
end SaturationMonoid
