import H0mework.NavierStokes.Galerkin.AmbientNorm
import H0mework.NavierStokes.Galerkin.KineticEnergyLedger

/-!
# Fixed-mode ambient control from the finite kinetic ledger

On a fixed zero-free Fourier inventory, kinetic energy controls the ambient
Hilbert carrier through a factor generated solely by that inventory.  Along
an actual unforced transverse and Fourier-real Galerkin trajectory, the
kinetic ledger makes this control uniform on every closed time interval.

No smallness, continuation, lifespan, trajectory bound, or caller-selected
compactness certificate is used.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound

open scoped BigOperators ENNReal

open Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger

noncomputable section

/-- Finite kinetic energy is nonnegative on every coefficient state. -/
theorem finiteStateVorticityKineticEnergy_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityKineticEnergy modes state := by
  unfold finiteStateVorticityKineticEnergy
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun wave _ =>
      complexCoordinateVectorNormSq_nonneg
        (finiteStateVelocityCoefficient state wave))

/-- The unweighted vorticity mass is nonnegative. -/
private theorem finiteStateVorticityMass_nonneg
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    0 ≤ finiteStateVorticityMass modes state := by
  unfold finiteStateVorticityMass
  exact Finset.sum_nonneg fun wave _ =>
    complexCoordinateVectorNormSq_nonneg (state wave)

/--
Kinetic energy is antitone along every actual unforced finite Galerkin
trajectory with the physical transverse and Fourier-reality invariants.
The viscosity is the source-owned positive coefficient.
-/
theorem finiteStateVorticityKineticEnergy_antitoneOn
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (ν : Viscosity)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (evolves :
      ∀ time ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory time)) time)
    (transverse :
      ∀ time ∈ Icc a b,
        FiniteStateTransverseOn modes (trajectory time))
    (reality :
      ∀ time ∈ Icc a b,
        FiniteStateRealityOn modes (trajectory time)) :
    AntitoneOn
      (fun time =>
        finiteStateVorticityKineticEnergy modes (trajectory time))
      (Icc a b) := by
  let energy : ℝ → ℝ := fun time =>
    finiteStateVorticityKineticEnergy modes (trajectory time)
  have energyDerivative :
      ∀ time ∈ Icc a b,
        HasDerivAt energy
          (-ν.coeff *
            finiteStateVorticityMass modes (trajectory time))
          time := by
    intro time timeMem
    exact
      finiteStateVorticityKineticEnergy_hasDerivAt_generator
        modes zeroNotMem negClosed ν.coeff trajectory time
        (evolves time timeMem)
        (transverse time timeMem)
        (reality time timeMem)
  apply antitoneOn_of_deriv_nonpos (convex_Icc a b)
  · intro time timeMem
    exact (energyDerivative time timeMem).continuousAt.continuousWithinAt
  · rw [interior_Icc]
    intro time timeMem
    exact
      (energyDerivative time ⟨timeMem.1.le, timeMem.2.le⟩).differentiableAt
        |>.differentiableWithinAt
  · rw [interior_Icc]
    intro time timeMem
    rw [(energyDerivative time
      ⟨timeMem.1.le, timeMem.2.le⟩).deriv]
    exact
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr ν.coeff_pos.le)
        (finiteStateVorticityMass_nonneg modes (trajectory time))

/--
The fixed-mode conversion factor.  It is generated only from the Fourier
inventory; no state, trajectory, time, viscosity, or cutoff parameter is
supplied.
-/
def finiteModeKineticAmbientFactor
    (modes : Finset IntegerWavevector) : ℝ :=
  2 *
    ∑ wave ∈ modes,
      (2 * Real.pi) ^ 2 * (integerWaveNormSq wave : ℝ)

theorem finiteModeKineticAmbientFactor_nonneg
    (modes : Finset IntegerWavevector) :
    0 ≤ finiteModeKineticAmbientFactor modes := by
  unfold finiteModeKineticAmbientFactor
  exact mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun wave _ =>
      mul_nonneg (sq_nonneg _)
        (integerWaveNormSq_nonneg wave))

/--
On a zero-free transverse inventory, coefficient enstrophy is bounded by
the fixed-mode factor times kinetic energy.
-/
theorem finiteStateVorticityCoefficientEnstrophy_le_kineticEnergy_factor
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (transverse : FiniteStateTransverseOn modes state) :
    finiteStateVorticityCoefficientEnstrophy modes state ≤
      finiteModeKineticAmbientFactor modes *
        finiteStateVorticityKineticEnergy modes state := by
  let denominator : IntegerWavevector → ℝ := fun wave =>
    (2 * Real.pi) ^ 2 * (integerWaveNormSq wave : ℝ)
  let denominatorSum : ℝ :=
    ∑ wave ∈ modes, denominator wave
  have denominatorPos :
      ∀ wave ∈ modes, 0 < denominator wave := by
    intro wave waveMem
    have waveNe : wave ≠ 0 := fun waveZero =>
      zeroNotMem (waveZero ▸ waveMem)
    dsimp [denominator]
    exact mul_pos (sq_pos_of_pos (by positivity))
      (by exact_mod_cast integerWaveNormSq_pos waveNe)
  have denominatorLeSum :
      ∀ wave ∈ modes, denominator wave ≤ denominatorSum := by
    intro wave waveMem
    dsimp [denominatorSum]
    exact Finset.single_le_sum
      (fun other _ => (denominatorPos other ‹other ∈ modes›).le)
      waveMem
  have rowBound :
      ∀ wave ∈ modes,
        complexCoordinateVectorNormSq (state wave) ≤
          denominatorSum *
            (complexCoordinateVectorNormSq (state wave) /
              denominator wave) := by
    intro wave waveMem
    have rowNonneg :=
      complexCoordinateVectorNormSq_nonneg (state wave)
    have quotientNonneg :
        0 ≤
          complexCoordinateVectorNormSq (state wave) /
            denominator wave :=
      div_nonneg rowNonneg (denominatorPos wave waveMem).le
    calc
      complexCoordinateVectorNormSq (state wave) =
          denominator wave *
            (complexCoordinateVectorNormSq (state wave) /
              denominator wave) := by
        rw [mul_comm]
        exact
          (div_mul_cancel₀
            (complexCoordinateVectorNormSq (state wave))
            (denominatorPos wave waveMem).ne').symm
      _ ≤
          denominatorSum *
            (complexCoordinateVectorNormSq (state wave) /
              denominator wave) :=
        mul_le_mul_of_nonneg_right
          (denominatorLeSum wave waveMem) quotientNonneg
  rw [finiteStateVorticityKineticEnergy_eq_weightedVorticity
    modes zeroNotMem state transverse]
  unfold finiteStateVorticityCoefficientEnstrophy
  simp_rw [complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
  change
    (∑ wave ∈ modes,
      complexCoordinateVectorNormSq (state wave)) ≤
        (2 * denominatorSum) *
          ((1 / 2 : ℝ) *
            ∑ wave ∈ modes,
              complexCoordinateVectorNormSq (state wave) /
                denominator wave)
  calc
    (∑ wave ∈ modes,
      complexCoordinateVectorNormSq (state wave)) ≤
        ∑ wave ∈ modes,
          denominatorSum *
            (complexCoordinateVectorNormSq (state wave) /
              denominator wave) :=
      Finset.sum_le_sum fun wave waveMem => rowBound wave waveMem
    _ =
        (2 * denominatorSum) *
          ((1 / 2 : ℝ) *
            ∑ wave ∈ modes,
              complexCoordinateVectorNormSq (state wave) /
                denominator wave) := by
      rw [← Finset.mul_sum]
      ring

/--
The ambient Hilbert norm squared is controlled by fixed-mode kinetic
energy.  Sharp support is the only observer premise.
-/
theorem complexVorticityHilbertState_norm_sq_le_kineticEnergy_factor
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : FiniteStateTransverseOn modes state) :
    ‖state‖ ^ 2 ≤
      finiteModeKineticAmbientFactor modes *
        finiteStateVorticityKineticEnergy modes state :=
  (complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
      modes state supported).trans
    (finiteStateVorticityCoefficientEnstrophy_le_kineticEnergy_factor
      modes zeroNotMem state transverse)

/--
Canonical ambient radius generated by the fixed inventory and one initial
state's kinetic energy.
-/
def finiteModeKineticAmbientRadius
    (modes : Finset IntegerWavevector)
    (initialState : ComplexVorticityHilbertState) : NNReal :=
  ⟨Real.sqrt
      (finiteModeKineticAmbientFactor modes *
        finiteStateVorticityKineticEnergy modes initialState),
    Real.sqrt_nonneg _⟩

/-- A supported transverse state lies in its canonical kinetic ambient ball. -/
theorem mem_closedBall_finiteModeKineticAmbientRadius
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse : FiniteStateTransverseOn modes state) :
    state ∈
      Metric.closedBall (0 : ComplexVorticityHilbertState)
        (finiteModeKineticAmbientRadius modes state) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have productNonneg :
      0 ≤ finiteModeKineticAmbientFactor modes *
        finiteStateVorticityKineticEnergy modes state :=
    mul_nonneg
      (finiteModeKineticAmbientFactor_nonneg modes)
      (finiteStateVorticityKineticEnergy_nonneg modes state)
  change
    ‖state‖ ^ 2 ≤
      (Real.sqrt
        (finiteModeKineticAmbientFactor modes *
          finiteStateVorticityKineticEnergy modes state)) ^ 2
  rw [Real.sq_sqrt productNonneg]
  exact
    complexVorticityHilbertState_norm_sq_le_kineticEnergy_factor
      modes zeroNotMem state supported transverse

/--
Every actual unforced physical trajectory remains in the single ambient
ball generated by its initial kinetic energy on the same fixed inventory.
-/
theorem trajectory_mem_closedBall_finiteModeKineticAmbientRadius_of_unforced
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed : FiniteModeNegClosed modes)
    (ν : Viscosity)
    (trajectory : ℝ → ComplexVorticityHilbertState)
    (a b : ℝ)
    (evolves :
      ∀ time ∈ Icc a b,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν.coeff (trajectory time)) time)
    (supported :
      ∀ time ∈ Icc a b,
        ∀ wave, wave ∉ modes → trajectory time wave = 0)
    (transverse :
      ∀ time ∈ Icc a b,
        FiniteStateTransverseOn modes (trajectory time))
    (reality :
      ∀ time ∈ Icc a b,
        FiniteStateRealityOn modes (trajectory time)) :
    ∀ time ∈ Icc a b,
      trajectory time ∈
        Metric.closedBall (0 : ComplexVorticityHilbertState)
          (finiteModeKineticAmbientRadius modes (trajectory a)) := by
  intro time timeMem
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  have productNonneg :
      0 ≤ finiteModeKineticAmbientFactor modes *
        finiteStateVorticityKineticEnergy modes (trajectory a) :=
    mul_nonneg
      (finiteModeKineticAmbientFactor_nonneg modes)
      (finiteStateVorticityKineticEnergy_nonneg modes (trajectory a))
  change
    ‖trajectory time‖ ^ 2 ≤
      (Real.sqrt
        (finiteModeKineticAmbientFactor modes *
          finiteStateVorticityKineticEnergy modes (trajectory a))) ^ 2
  rw [Real.sq_sqrt productNonneg]
  calc
      ‖trajectory time‖ ^ 2 ≤
          finiteModeKineticAmbientFactor modes *
            finiteStateVorticityKineticEnergy modes (trajectory time) :=
        complexVorticityHilbertState_norm_sq_le_kineticEnergy_factor
          modes zeroNotMem (trajectory time)
          (supported time timeMem)
          (transverse time timeMem)
      _ ≤
          finiteModeKineticAmbientFactor modes *
            finiteStateVorticityKineticEnergy modes (trajectory a) :=
        mul_le_mul_of_nonneg_left
          (finiteStateVorticityKineticEnergy_antitoneOn
            modes zeroNotMem negClosed ν trajectory a b
            evolves transverse reality
            ⟨le_rfl, timeMem.1.trans timeMem.2⟩ timeMem timeMem.1)
          (finiteModeKineticAmbientFactor_nonneg modes)

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticAmbientBound
end NavierStokes
end SaturationMonoid
