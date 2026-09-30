import H0mework.NavierStokes.VelocityGalerkin.UniformKineticLedger
import H0mework.NavierStokes.KineticRestart.KineticEndpointTailLocalization

/-!
# Strong initial-data convergence for the endpoint Galerkin family

The source-generated velocity endpoint lives on the complete nonzero Fourier
`ℓ²` carrier.  This module identifies the canonical punctured-cube initial
velocities with the cofinal finite-coordinate projections of that same
endpoint.  Consequently the actual Galerkin initial velocities converge
strongly to the endpoint, and their exact kinetic energies converge to one
half of its physical square norm.

No cutoff sequence, target initial datum, convergence witness, or norm bound
is supplied by the caller.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence

open scoped BigOperators ENNReal Topology

open Filter
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedShellSerrinGeometry
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinUniformKineticLedger

noncomputable section

/-- The exact nonzero-wave index of the generated endpoint carrier.  The
explicit alias avoids confusing it with older, definitionally unrelated
nonzero-wave readout aliases. -/
abbrev WholeRestartNonzeroWave :=
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger.NonzeroIntegerWavevector

/-! ## Canonical nonzero-wave exhaustion -/

/-- Canonical punctured cube reindexed by the complete endpoint carrier. -/
def wholeRestartNonzeroModes
    (radius : ℕ) : Finset WholeRestartNonzeroWave :=
  (wholeRestartModes radius).attach.map
    (wholeRestartVelocityEndpointRetainedWaveEmbedding radius)

@[simp] theorem mem_wholeRestartNonzeroModes
    (radius : ℕ)
    (wave : WholeRestartNonzeroWave) :
    wave ∈ wholeRestartNonzeroModes radius ↔
      wave.1 ∈ wholeRestartModes radius := by
  classical
  constructor
  · intro waveMem
    rw [wholeRestartNonzeroModes, Finset.mem_map] at waveMem
    obtain ⟨sourceWave, _sourceMem, sourceEq⟩ := waveMem
    have valueEq : sourceWave.1 = wave.1 :=
      congrArg (fun indexed : WholeRestartNonzeroWave => indexed.1) sourceEq
    simpa only [← valueEq] using sourceWave.2
  · intro waveMem
    rw [wholeRestartNonzeroModes, Finset.mem_map]
    let sourceWave : {wave // wave ∈ wholeRestartModes radius} :=
      ⟨wave.1, waveMem⟩
    refine ⟨sourceWave, Finset.mem_attach _ sourceWave, ?_⟩
    apply Subtype.ext
    rfl

/-- Canonical nonzero cubes are monotone in the source radius. -/
theorem wholeRestartNonzeroModes_mono :
    Monotone
      (wholeRestartNonzeroModes : ℕ → Finset WholeRestartNonzeroWave) := by
  intro smaller larger radiusLe wave waveMem
  rw [mem_wholeRestartNonzeroModes] at waveMem ⊢
  rw [wholeRestartModes,
    puncturedIntegerWaveFrequencyCube,
    Finset.mem_erase] at waveMem ⊢
  refine ⟨waveMem.1, ?_⟩
  rw [integerWaveFrequencyCube, Fintype.mem_piFinset] at waveMem ⊢
  intro coordinate
  have coordinateMem := waveMem.2 coordinate
  rw [Finset.mem_Icc] at coordinateMem ⊢
  have radiusCastLe : (smaller : ℤ) ≤ larger := by
    exact_mod_cast radiusLe
  constructor <;> omega

/-- Every physical nonzero wave occurs in a canonical source radius. -/
theorem exists_mem_wholeRestartNonzeroModes
    (wave : WholeRestartNonzeroWave) :
    ∃ radius : ℕ, wave ∈ wholeRestartNonzeroModes radius := by
  have eventuallyMem :=
    nonzero_integerWave_eventually_mem_puncturedFrequencyCube
      wave.1 wave.2
  rw [eventually_atTop] at eventuallyMem
  obtain ⟨radius, radiusMem⟩ := eventuallyMem
  exact ⟨radius, (mem_wholeRestartNonzeroModes radius wave).2
    (radiusMem radius le_rfl)⟩

/-- The internally fixed radius family is cofinal in all finite subsets of
the complete nonzero-wave carrier. -/
theorem wholeRestartNonzeroModes_tendsto_atTop :
    Tendsto
      (wholeRestartNonzeroModes : ℕ → Finset WholeRestartNonzeroWave)
      atTop atTop :=
  wholeRestartNonzeroModes_mono.tendsto_atTop_finset
    exists_mem_wholeRestartNonzeroModes

/-! ## Actual initial velocity in the whole physical carrier -/

/-- The canonical finite initial velocity, retained in the same complete
nonzero-wave carrier as the generated endpoint. -/
def wholeRestartVelocityEndpointGalerkinInitialVelocity
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    WholeRestartVelocityEndpointState :=
  wholeRestartKineticFiniteProjection
    (wholeRestartNonzeroModes radius) endpoint

@[simp] theorem wholeRestartVelocityEndpointGalerkinInitialVelocity_apply
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (wave : WholeRestartNonzeroWave) :
    wholeRestartVelocityEndpointGalerkinInitialVelocity
        radius endpoint wave =
      if wave.1 ∈ wholeRestartModes radius then endpoint wave else 0 := by
  classical
  rw [wholeRestartVelocityEndpointGalerkinInitialVelocity,
    wholeRestartKineticFiniteProjection, lp.coeFn_sum,
    Finset.sum_apply]
  by_cases waveMem : wave ∈ wholeRestartNonzeroModes radius
  · rw [Finset.sum_eq_single wave]
    · rw [lp.single_apply_self,
        if_pos ((mem_wholeRestartNonzeroModes radius wave).1 waveMem)]
    · intro other otherMem otherNe
      exact lp.single_apply_ne
        (E := fun _ : WholeRestartNonzeroWave => ComplexCoordinateEuclidean)
        2 other (endpoint other) otherNe.symm
    · intro waveNotMem
      exact (waveNotMem waveMem).elim
  · have valueNotMem : wave.1 ∉ wholeRestartModes radius := by
      simpa only [mem_wholeRestartNonzeroModes] using waveMem
    rw [if_neg valueNotMem]
    apply Finset.sum_eq_zero
    intro other otherMem
    have otherNe : other ≠ wave := by
      intro equality
      exact waveMem (equality ▸ otherMem)
    exact lp.single_apply_ne
      (E := fun _ : WholeRestartNonzeroWave => ComplexCoordinateEuclidean)
      2 other (endpoint other) otherNe.symm

/-- The complete-carrier initial velocity is exactly the Biot--Savart
velocity of the actual curl-generated Galerkin initial state. -/
theorem wholeRestartVelocityEndpointGalerkinInitialVelocity_eq_biotSavart
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse endpoint)
    (wave : WholeRestartNonzeroWave) :
    wholeRestartVelocityEndpointGalerkinInitialVelocity radius endpoint wave =
      biotSavartVelocityCoefficient wave.1
        (wholeRestartVelocityEndpointFiniteVorticityInitialState
          radius endpoint wave.1) := by
  by_cases waveMem : wave.1 ∈ wholeRestartModes radius
  · rw [wholeRestartVelocityEndpointGalerkinInitialVelocity_apply,
      if_pos waveMem,
      wholeRestartVelocityEndpointFiniteVorticityInitialState_biotSavart
        radius endpoint transverse wave.1 waveMem]
    simp [wholeRestartVelocityEndpointFiniteProjection_apply, waveMem,
      wholeRestartVelocityEndpointCoefficient_of_ne endpoint wave.1 wave.2]
  · rw [wholeRestartVelocityEndpointGalerkinInitialVelocity_apply,
      if_neg waveMem,
      wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      if_neg waveMem]
    simp [biotSavartVelocityCoefficient]

/-! ## Strong convergence and exact initial-energy limit -/

/-- Canonical actual Galerkin initial velocities converge strongly to the
source-generated physical endpoint on the whole nonzero-wave carrier. -/
theorem wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto
    (endpoint : WholeRestartVelocityEndpointState) :
    Tendsto
      (fun radius =>
        wholeRestartVelocityEndpointGalerkinInitialVelocity radius endpoint)
      atTop (nhds endpoint) := by
  have fullSum :
      Tendsto
        (fun modes : Finset WholeRestartNonzeroWave =>
          ∑ wave ∈ modes, lp.single 2 wave (endpoint wave))
        atTop (nhds endpoint) :=
    lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) endpoint
  change
    Tendsto
      ((fun modes : Finset WholeRestartNonzeroWave =>
        ∑ wave ∈ modes, lp.single 2 wave (endpoint wave)) ∘
          wholeRestartNonzeroModes)
      atTop (nhds endpoint)
  exact fullSum.comp wholeRestartNonzeroModes_tendsto_atTop

/-- The retained endpoint square is the exact finite Galerkin velocity
square, before passing to the limit. -/
theorem wholeRestartVelocityEndpointGalerkinInitialVelocity_norm_sq
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    ‖wholeRestartVelocityEndpointGalerkinInitialVelocity radius endpoint‖ ^ 2 =
      wholeRestartVelocityEndpointFiniteProjectedSquare radius endpoint := by
  classical
  rw [wholeRestartVelocityEndpointGalerkinInitialVelocity,
    wholeRestartKineticFiniteProjection]
  have normSum :=
    lp.norm_sum_single
      (p := (2 : ENNReal)) (by norm_num)
      (fun wave : WholeRestartNonzeroWave => endpoint wave)
      (wholeRestartNonzeroModes radius)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at normSum
  rw [normSum]
  unfold wholeRestartVelocityEndpointFiniteProjectedSquare
  refine Finset.sum_bij (fun indexed _ => indexed.1) ?_ ?_ ?_ ?_
  · intro indexed indexedMem
    exact (mem_wholeRestartNonzeroModes radius indexed).1 indexedMem
  · intro left leftMem right rightMem valueEq
    exact Subtype.ext valueEq
  · intro wave waveMem
    have puncturedMem :
        wave ∈ puncturedIntegerWaveFrequencyCube radius := waveMem
    rw [puncturedIntegerWaveFrequencyCube, Finset.mem_erase]
      at puncturedMem
    have waveNe : wave ≠ 0 := puncturedMem.1
    let indexed : WholeRestartNonzeroWave := ⟨wave, waveNe⟩
    exact ⟨indexed,
      (mem_wholeRestartNonzeroModes radius indexed).2 waveMem, rfl⟩
  · intro indexed indexedMem
    have waveMem : indexed.1 ∈ wholeRestartModes radius :=
      (mem_wholeRestartNonzeroModes radius indexed).1 indexedMem
    rw [wholeRestartVelocityEndpointFiniteProjection_apply, if_pos waveMem,
      wholeRestartVelocityEndpointCoefficient_of_ne endpoint indexed.1
        indexed.2]
    let indexedWave : WholeRestartNonzeroWave := indexed
    have rowNorm :=
      euclideanCoordinateRow_norm_sq
        (fun coordinate => endpoint indexedWave coordinate)
    have rowEq :
        euclideanCoordinateRow
            (fun coordinate => endpoint indexedWave coordinate) =
          endpoint indexedWave := by
      ext coordinate
      rfl
    rw [rowEq,
      complexCoordinateAmplitudeSq_eq_complexCoordinateVectorNormSq]
      at rowNorm
    simpa only [indexedWave] using rowNorm

/-- Exact initial kinetic energies converge to one half of the generated
physical endpoint square. -/
theorem wholeRestartVelocityEndpointGalerkinInitialKineticEnergy_tendsto
    (endpoint : WholeRestartVelocityEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse endpoint) :
    Tendsto
      (fun radius =>
        finiteStateVorticityKineticEnergy
          (wholeRestartModes radius)
          (wholeRestartVelocityEndpointFiniteVorticityInitialState
            radius endpoint))
      atTop (nhds ((1 / 2 : ℝ) * ‖endpoint‖ ^ 2)) := by
  have velocityTendsto :=
    wholeRestartVelocityEndpointGalerkinInitialVelocity_tendsto endpoint
  have squareTendsto := velocityTendsto.norm.pow 2
  have scaledTendsto :=
    (tendsto_const_nhds.mul squareTendsto :
      Tendsto
        (fun radius =>
          (1 / 2 : ℝ) *
            ‖wholeRestartVelocityEndpointGalerkinInitialVelocity
              radius endpoint‖ ^ 2)
        atTop
        (nhds ((1 / 2 : ℝ) * ‖endpoint‖ ^ 2)))
  convert scaledTendsto using 1
  funext radius
  rw [wholeRestartVelocityEndpointFiniteVorticityInitialState_kineticEnergy
      radius endpoint transverse,
    wholeRestartVelocityEndpointGalerkinInitialVelocity_norm_sq]

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinInitialConvergence
end NavierStokes
end SaturationMonoid
