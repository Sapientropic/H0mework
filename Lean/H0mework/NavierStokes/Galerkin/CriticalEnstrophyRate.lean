import H0mework.NavierStokes.Galerkin.EnstrophyBalance
import H0mework.NavierStokes.Galerkin.StretchingCriticalBound

/-!
# Cutoff-independent critical enstrophy rate

The exact finite Galerkin enstrophy balance and the complete-table
stretching bound combine to give the classical critical differential
inequality without a mode-count or maximum-frequency loss:

```text
d(Y/2)/dt
  <= -(nu/2) (2*pi)^2 Z
       + (1/(2*nu)) U^2 Y
  <= -(nu/2) (2*pi)^2 Z
       + (1/(2*nu)) K_3 Z Y.
```

Here `U` is the actual finite velocity Fourier majorant and `K_3` is the
global summable three-dimensional `|k|^-4` lattice constant.  This theorem
does not assert continuation: it identifies the sole remaining dynamic
responsibility as a cutoff-uniform time budget for `U^2`, or an equivalent
absorption of the final `Z * Y` term.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyRate

open scoped BigOperators Topology ENNReal

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportCriticalSobolev
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalIntegerLatticeCriticalKernel
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinStretchingCriticalBound

noncomputable section

/-- The half-dissipative critical rate before replacing the actual velocity
majorant by the global lattice kernel. -/
def finiteStateVorticityCriticalEnstrophyRate
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) : ℝ :=
  -(ν / 2) *
      ((2 * Real.pi) ^ 2 *
        finiteStateVorticityEnstrophyMass modes state) +
    (ν⁻¹ / 2) *
      finiteStateVelocityMajorant modes state ^ 2 *
      finiteStateVorticityCoefficientEnstrophy modes state

/-- The complete stretching-minus-viscosity rate is bounded by one half of
the viscous enstrophy dissipation plus the actual critical velocity budget. -/
theorem finiteStateVorticity_stretching_sub_viscous_le_criticalRate
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (ν : ℝ)
    (ν_pos : 0 < ν)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0) :
    finiteStateVorticityStretchingWork modes state -
          ν * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state ≤
      finiteStateVorticityCriticalEnstrophyRate modes ν state := by
  have stretchingUpper :
      finiteStateVorticityStretchingWork modes state ≤
        (ν / 2) *
            ((2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes state) +
          (ν⁻¹ / 2) *
            finiteStateVelocityMajorant modes state ^ 2 *
            finiteStateVorticityCoefficientEnstrophy modes state :=
    (le_abs_self _).trans
      (finiteStateVorticityStretchingWork_abs_le_young
        modes state ν ν_pos transverse)
  unfold finiteStateVorticityCriticalEnstrophyRate
  linarith

/-- Cutoff-independent form of the critical rate.  The finite majorant is
replaced by the global summable three-dimensional lattice constant, without
introducing mode cardinality or a maximum shell. -/
theorem finiteStateVorticityCriticalEnstrophyRate_le_globalKernel
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (ν : ℝ)
    (ν_pos : 0 < ν) :
    finiteStateVorticityCriticalEnstrophyRate modes ν state ≤
      -(ν / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) +
        (ν⁻¹ / 2) *
          (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
            finiteStateVorticityEnstrophyMass modes state) *
          finiteStateVorticityCoefficientEnstrophy modes state := by
  have multiplierNonneg :
      0 ≤ (ν⁻¹ / 2) *
        finiteStateVorticityCoefficientEnstrophy modes state := by
    exact mul_nonneg
      (div_nonneg (inv_nonneg.mpr ν_pos.le) (by norm_num))
      (by
        unfold finiteStateVorticityCoefficientEnstrophy
        exact Finset.sum_nonneg fun wave waveMem =>
          complexCoordinateAmplitudeSq_nonneg _)
  have majorantBound :=
    finiteStateVelocityMajorant_sq_le_criticalGlobal modes state
  unfold finiteStateVorticityCriticalEnstrophyRate
  calc
    -(ν / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) +
        (ν⁻¹ / 2) *
          finiteStateVelocityMajorant modes state ^ 2 *
          finiteStateVorticityCoefficientEnstrophy modes state ≤
      -(ν / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) +
        finiteStateVelocityMajorant modes state ^ 2 *
          ((ν⁻¹ / 2) *
            finiteStateVorticityCoefficientEnstrophy modes state) := by
      ring_nf
      exact le_rfl
    _ ≤
      -(ν / 2) *
          ((2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes state) +
        (biotSavartSerrinConstant *
            (∑' wave : IntegerWavevector,
              integerWaveCriticalKernel wave) *
            finiteStateVorticityEnstrophyMass modes state) *
          ((ν⁻¹ / 2) *
            finiteStateVorticityCoefficientEnstrophy modes state) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_right majorantBound multiplierNonneg)
    _ = _ := by ring

/-- Pointwise critical differential inequality for every actual
reality-preserving, transverse finite Galerkin trajectory.  The derivative
is the exact generated stretching rate; its upper bound is uniform in the
finite carrier. -/
theorem finiteStateVorticityHalfEnstrophy_hasDerivAt_and_le_globalCriticalRate
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (ν_pos : 0 < ν)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (t : ℝ)
    (evolves :
      HasDerivAt trajectory
        (finiteStateVorticityGenerator modes ν (trajectory t)) t)
    (reality : FiniteStateFourierReality (trajectory t))
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ trajectory t wave = 0) :
    HasDerivAt
        (fun time =>
          finiteStateVorticityHalfEnstrophy modes (trajectory time))
        (finiteStateVorticityStretchingWork modes (trajectory t) -
          ν * (2 * Real.pi) ^ 2 *
            finiteStateVorticityEnstrophyMass modes (trajectory t)) t ∧
      finiteStateVorticityStretchingWork modes (trajectory t) -
            ν * (2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes (trajectory t) ≤
        -(ν / 2) *
            ((2 * Real.pi) ^ 2 *
              finiteStateVorticityEnstrophyMass modes (trajectory t)) +
          (ν⁻¹ / 2) *
            (biotSavartSerrinConstant *
              (∑' wave : IntegerWavevector,
                integerWaveCriticalKernel wave) *
              finiteStateVorticityEnstrophyMass modes (trajectory t)) *
            finiteStateVorticityCoefficientEnstrophy
              modes (trajectory t) := by
  refine
    ⟨finiteStateVorticityHalfEnstrophy_hasDerivAt_stretchingWork
      modes negClosed ν trajectory t evolves reality, ?_⟩
  exact
    (finiteStateVorticity_stretching_sub_viscous_le_criticalRate
      modes (trajectory t) ν ν_pos transverse).trans
      (finiteStateVorticityCriticalEnstrophyRate_le_globalKernel
        modes (trajectory t) ν ν_pos)

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyRate
end NavierStokes
end SaturationMonoid
