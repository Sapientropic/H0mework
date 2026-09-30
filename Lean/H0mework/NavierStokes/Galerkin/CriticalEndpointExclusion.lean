import H0mework.NavierStokes.Galerkin.AmbientNorm
import H0mework.NavierStokes.Galerkin.CriticalContinuation
import H0mework.NavierStokes.InitialData.FiniteModalPicardBounds

/-!
# Critical exclusion of finite Galerkin right endpoints

At one fixed Fourier inventory, boundedness of an actual Galerkin trajectory
already excludes a finite maximal right endpoint.  The finite-modal
polynomial factorization generates all field and Lipschitz constants on a
slightly larger ball; the quantitative restart theorem then produces an
actual extension strictly past the proposed endpoint.

The second theorem discharges the trajectory bound from the cutoff-independent
critical enstrophy barrier.  Its conclusion is an extension of the original
Galerkin ODE path, not an assumed endpoint state or continuation certificate.

The generated Picard constants may depend on the fixed inventory.  Thus this
module closes the finite-dimensional maximal-time obstruction; it does not
assert an infinite-dimensional Navier--Stokes continuation theorem.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEndpointExclusion

open scoped BigOperators ENNReal

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalContinuation
open ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds

noncomputable section

/-- A bounded trajectory of one fixed finite Galerkin system extends past
every finite right endpoint.

The larger carrier ball and its uniform Picard time are generated internally
from the finite polynomial field.  In particular, no field bound, Lipschitz
constant, endpoint value, or continuation witness occurs in the theorem
mouth. -/
theorem exists_extension_past_finite_endpoint_of_bounded_finiteGenerator
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (intervalNonempty : a < b)
    (innerRadius : NNReal)
    (evolves :
      ∀ t ∈ Ioo a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t)
    (trajectoryMem :
      ∀ t ∈ Ioo a b,
        trajectory t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState)
            innerRadius) :
    ∃ extendedUntil : ℝ,
      b < extendedUntil ∧
        ∃ extension : ℝ → ComplexVorticityHilbertState,
          EqOn extension trajectory (Ioo a b) ∧
            ∀ t ∈ Ioo a extendedUntil,
              HasDerivAt extension
                (finiteStateVorticityGenerator
                  modes ν (extension t)) t := by
  let outerRadius : NNReal := innerRadius + 1
  have radiusRoom : innerRadius < outerRadius := by
    dsimp [outerRadius]
    exact lt_add_of_pos_right innerRadius (by norm_num)
  obtain
      ⟨ε, εPos, fieldBound, lipschitzBound,
        uniformPicard⟩ :=
    exists_uniformPicard_finiteStateVorticityGenerator
      modes ν innerRadius outerRadius radiusRoom
  exact
    exists_extension_past_finite_endpoint_of_uniform_picard
      intervalNonempty εPos evolves trajectoryMem
      uniformPicard

/-- The cutoff-independent critical enstrophy barrier supplies the bounded
trajectory premise required by the fixed-modal restart.  Consequently an
actual physical Galerkin trajectory below the critical threshold cannot stop
at a finite positive right endpoint.

All quantitative restart data are generated after the barrier has bounded
the actual trajectory.  The theorem mouth contains neither a maximality
predicate nor a proposed extension. -/
theorem exists_extension_past_finite_endpoint_of_criticalSmall
    (modes : Finset IntegerWavevector)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (νPos : 0 < ν)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (endpointTime : ℝ)
    (endpointTimePos : 0 < endpointTime)
    (physicalProperties :
      ∀ t ∈ Ico (0 : ℝ) endpointTime,
        HasDerivAt trajectory
            (finiteStateVorticityGenerator
              modes ν (trajectory t)) t ∧
          (∀ wave, wave ∉ modes → trajectory t wave = 0) ∧
          (∀ wave,
            complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
          FiniteStateFourierReality (trajectory t))
    (initialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes (trajectory 0) ≤
        ν ^ 2 * (2 * Real.pi) ^ 2) :
    ∃ extendedUntil : ℝ,
      endpointTime < extendedUntil ∧
        ∃ extension : ℝ → ComplexVorticityHilbertState,
          EqOn extension trajectory (Ioo 0 endpointTime) ∧
            ∀ t ∈ Ioo 0 extendedUntil,
              HasDerivAt extension
                (finiteStateVorticityGenerator
                  modes ν (extension t)) t := by
  let initialEnstrophy : ℝ :=
    finiteStateVorticityCoefficientEnstrophy
      modes (trajectory 0)
  let innerRadius : NNReal :=
    ⟨Real.sqrt initialEnstrophy, Real.sqrt_nonneg _⟩
  have trajectoryMem :
      ∀ t ∈ Ioo (0 : ℝ) endpointTime,
        trajectory t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState)
            innerRadius := by
    intro t timeMem
    have closedIntervalProperties :
        ∀ s ∈ Icc (0 : ℝ) t,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                modes ν (trajectory s)) s ∧
            (∀ wave, wave ∉ modes → trajectory s wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory s wave = 0) ∧
            FiniteStateFourierReality (trajectory s) := by
      intro s sMem
      exact physicalProperties s
        ⟨sMem.1, lt_of_le_of_lt sMem.2 timeMem.2⟩
    have barrierConclusion :=
      finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
        modes negClosed ν νPos trajectory 0 t
        (fun s sMem => (closedIntervalProperties s sMem).1)
        (fun s sMem => (closedIntervalProperties s sMem).2.2.2)
        (fun s sMem wave _ =>
          (closedIntervalProperties s sMem).2.2.1 wave)
        initialSmall
    have halfEnstrophyLe :=
      (barrierConclusion t ⟨timeMem.1.le, le_rfl⟩).1
    have enstrophyLe :
        finiteStateVorticityCoefficientEnstrophy
            modes (trajectory t) ≤
          initialEnstrophy := by
      dsimp [initialEnstrophy]
      unfold finiteStateVorticityHalfEnstrophy at halfEnstrophyLe
      linarith
    have ambientSqLe :=
      complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
        modes (trajectory t)
        (physicalProperties t
          ⟨timeMem.1.le, timeMem.2⟩).2.1
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖trajectory t‖ ≤ Real.sqrt initialEnstrophy
    exact Real.le_sqrt_of_sq_le (ambientSqLe.trans enstrophyLe)
  exact
    exists_extension_past_finite_endpoint_of_bounded_finiteGenerator
      modes ν trajectory 0 endpointTime endpointTimePos
      innerRadius
      (fun t timeMem =>
        (physicalProperties t
          ⟨timeMem.1.le, timeMem.2⟩).1)
      trajectoryMem

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEndpointExclusion
end NavierStokes
end SaturationMonoid
