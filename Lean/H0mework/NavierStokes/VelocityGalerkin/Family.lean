import H0mework.NavierStokes.Restart.VelocityWeakEndpoint
import H0mework.NavierStokes.Restart.CanonicalReplay

/-!
# Canonical Galerkin family generated from the velocity weak endpoint

The bounded whole-restart run already generates a divergence-free, real
physical velocity endpoint on the complete nonzero-frequency `ℓ²` carrier.
This module compiles that endpoint into every canonical punctured Fourier
window.  Curl generates the finite vorticity initial state, Biot--Savart
recovers the retained velocity exactly, and the existing finite-dimensional
existence producer selects an actual unforced Galerkin trajectory on the
fixed interval `[0, 1]`.

The source-facing family accepts neither a radius, a cutoff, a target
trajectory, nor a compactness witness.  Radius is an internally generated
index of the returned Type-valued family.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily

open scoped BigOperators

open Set Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticEnergyLedger
open ThreeDimensionalVorticityCoefficientFiniteGalerkinKineticCommonTimeExistence
open ThreeDimensionalVorticityCoefficientPuncturedCanonicalGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCanonicalReplay
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint

noncomputable section

/-! ## Whole endpoint coefficient and its finite projections -/

/-- Extend the nonzero-wave velocity endpoint by the forced zero row. -/
def wholeRestartVelocityEndpointCoefficient
    (endpoint : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) : ComplexCoordinateVector :=
  if waveZero : wave = 0 then 0
  else fun coordinate => endpoint ⟨wave, waveZero⟩ coordinate

@[simp] theorem wholeRestartVelocityEndpointCoefficient_zero
    (endpoint : WholeRestartVelocityEndpointState) :
    wholeRestartVelocityEndpointCoefficient endpoint 0 = 0 := by
  simp [wholeRestartVelocityEndpointCoefficient]

theorem wholeRestartVelocityEndpointCoefficient_of_ne
    (endpoint : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector)
    (waveNe : wave ≠ 0) :
    wholeRestartVelocityEndpointCoefficient endpoint wave =
      fun coordinate => endpoint ⟨wave, waveNe⟩ coordinate := by
  simp [wholeRestartVelocityEndpointCoefficient, waveNe]

/-- Endpoint transversality survives extension across the forced zero row. -/
theorem wholeRestartVelocityEndpointCoefficient_transverse
    (endpoint : WholeRestartVelocityEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse endpoint)
    (wave : IntegerWavevector) :
    complexWavevector wave ⬝ᵥ
        wholeRestartVelocityEndpointCoefficient endpoint wave =
      0 := by
  by_cases waveZero : wave = 0
  · subst wave
    simp
  · rw [wholeRestartVelocityEndpointCoefficient_of_ne endpoint wave waveZero]
    exact transverse ⟨wave, waveZero⟩

/-- Endpoint Fourier reality survives extension across the zero row. -/
theorem wholeRestartVelocityEndpointCoefficient_waveNeg
    (endpoint : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality endpoint)
    (wave : IntegerWavevector) :
    wholeRestartVelocityEndpointCoefficient endpoint (waveNeg wave) =
      vectorConj (wholeRestartVelocityEndpointCoefficient endpoint wave) := by
  by_cases waveZero : wave = 0
  · subst wave
    simp [waveNeg]
  · have negWaveNe : waveNeg wave ≠ 0 := by
      simpa using waveZero
    rw [wholeRestartVelocityEndpointCoefficient_of_ne
        endpoint (waveNeg wave) negWaveNe,
      wholeRestartVelocityEndpointCoefficient_of_ne endpoint wave waveZero]
    funext coordinate
    exact reality ⟨wave, waveZero⟩ coordinate

/-- Canonical finite projection of a generated velocity endpoint. -/
def wholeRestartVelocityEndpointFiniteProjection
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState
    (wholeRestartModes radius)
    (wholeRestartVelocityEndpointCoefficient endpoint)

@[simp] theorem wholeRestartVelocityEndpointFiniteProjection_apply
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) :
    wholeRestartVelocityEndpointFiniteProjection radius endpoint wave =
      if wave ∈ wholeRestartModes radius then
        wholeRestartVelocityEndpointCoefficient endpoint wave
      else 0 := by
  simp [wholeRestartVelocityEndpointFiniteProjection]

theorem wholeRestartVelocityEndpointFiniteProjection_supported
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    ∀ wave, wave ∉ wholeRestartModes radius →
      wholeRestartVelocityEndpointFiniteProjection radius endpoint wave = 0 := by
  intro wave waveNotMem
  simp [waveNotMem]

@[simp] theorem wholeRestartVelocityEndpointFiniteProjection_zero
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    wholeRestartVelocityEndpointFiniteProjection radius endpoint 0 = 0 := by
  exact wholeRestartVelocityEndpointFiniteProjection_supported
    radius endpoint 0
      (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)

theorem wholeRestartVelocityEndpointFiniteProjection_transverse
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse endpoint) :
    ∀ wave,
      complexWavevector wave ⬝ᵥ
          wholeRestartVelocityEndpointFiniteProjection radius endpoint wave =
        0 := by
  intro wave
  by_cases waveMem : wave ∈ wholeRestartModes radius
  · rw [wholeRestartVelocityEndpointFiniteProjection_apply, if_pos waveMem]
    exact wholeRestartVelocityEndpointCoefficient_transverse
      endpoint transverse wave
  · rw [wholeRestartVelocityEndpointFiniteProjection_apply, if_neg waveMem]
    simp

theorem wholeRestartVelocityEndpointFiniteProjection_reality
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality endpoint) :
    FiniteStateFourierReality
      (wholeRestartVelocityEndpointFiniteProjection radius endpoint) := by
  intro wave
  by_cases waveMem : wave ∈ wholeRestartModes radius
  · have negWaveMem : waveNeg wave ∈ wholeRestartModes radius := by
      exact puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
    rw [wholeRestartVelocityEndpointFiniteProjection_apply,
      wholeRestartVelocityEndpointFiniteProjection_apply,
      if_pos waveMem, if_pos negWaveMem,
      wholeRestartVelocityEndpointCoefficient_waveNeg endpoint reality wave]
  · have negWaveNotMem : waveNeg wave ∉ wholeRestartModes radius := by
      intro negWaveMem
      exact waveMem (by
        simpa [wholeRestartModes] using
          puncturedIntegerWaveFrequencyCube_waveNeg_mem radius negWaveMem)
    rw [wholeRestartVelocityEndpointFiniteProjection_apply,
      wholeRestartVelocityEndpointFiniteProjection_apply,
      if_neg waveMem, if_neg negWaveNotMem]
    exact vectorConj_zero.symm

/-! ## Curl compilation and exact Hodge recovery -/

/-- Curl commutes with the Fourier reality involution. -/
theorem fourierCurlCoefficient_waveNeg_vectorConj
    (wave : IntegerWavevector)
    (velocity : ComplexCoordinateVector) :
    fourierCurlCoefficient (waveNeg wave) (vectorConj velocity) =
      vectorConj (fourierCurlCoefficient wave velocity) := by
  funext coordinate
  fin_cases coordinate <;>
    simp [fourierCurlCoefficient, cross_apply, vectorConj, waveNeg,
      complexWavevector] <;>
    ring

/-- Finite vorticity initial state generated by applying physical curl to
the canonical finite velocity projection. -/
def wholeRestartVelocityEndpointFiniteVorticityInitialState
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    ComplexVorticityHilbertState :=
  finiteComplexVorticityState
    (wholeRestartModes radius)
    (fun wave =>
      fourierCurlCoefficient wave
        (wholeRestartVelocityEndpointFiniteProjection
          radius endpoint wave))

@[simp] theorem wholeRestartVelocityEndpointFiniteVorticityInitialState_apply
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (wave : IntegerWavevector) :
    wholeRestartVelocityEndpointFiniteVorticityInitialState
        radius endpoint wave =
      if wave ∈ wholeRestartModes radius then
        fourierCurlCoefficient wave
          (wholeRestartVelocityEndpointFiniteProjection
            radius endpoint wave)
      else 0 := by
  simp [wholeRestartVelocityEndpointFiniteVorticityInitialState]

theorem wholeRestartVelocityEndpointFiniteVorticityInitialState_supported
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    ∀ wave, wave ∉ wholeRestartModes radius →
      wholeRestartVelocityEndpointFiniteVorticityInitialState
        radius endpoint wave = 0 := by
  intro wave waveNotMem
  simp [waveNotMem]

@[simp] theorem wholeRestartVelocityEndpointFiniteVorticityInitialState_zero
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    wholeRestartVelocityEndpointFiniteVorticityInitialState
        radius endpoint 0 = 0 := by
  exact wholeRestartVelocityEndpointFiniteVorticityInitialState_supported
    radius endpoint 0
      (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)

theorem wholeRestartVelocityEndpointFiniteVorticityInitialState_transverse
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) :
    ∀ wave ∈ wholeRestartModes radius,
      complexWavevector wave ⬝ᵥ
          wholeRestartVelocityEndpointFiniteVorticityInitialState
            radius endpoint wave =
        0 := by
  intro wave waveMem
  rw [wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
    if_pos waveMem, fourierCurlCoefficient, dotProduct_smul,
    dot_self_cross]
  simp

theorem wholeRestartVelocityEndpointFiniteVorticityInitialState_reality
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality endpoint) :
    FiniteStateFourierReality
      (wholeRestartVelocityEndpointFiniteVorticityInitialState
        radius endpoint) := by
  intro wave
  by_cases waveMem : wave ∈ wholeRestartModes radius
  · have negWaveMem : waveNeg wave ∈ wholeRestartModes radius := by
      exact puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem
    rw [wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      if_pos waveMem, if_pos negWaveMem,
      wholeRestartVelocityEndpointFiniteProjection_reality
        radius endpoint reality wave,
      fourierCurlCoefficient_waveNeg_vectorConj]
  · have negWaveNotMem : waveNeg wave ∉ wholeRestartModes radius := by
      intro negWaveMem
      exact waveMem (by
        simpa [wholeRestartModes] using
          puncturedIntegerWaveFrequencyCube_waveNeg_mem radius negWaveMem)
    rw [wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
      if_neg waveMem, if_neg negWaveNotMem]
    exact vectorConj_zero.symm

/-- Biot--Savart exactly recovers every retained finite velocity row from
the curl-generated vorticity initial state. -/
theorem wholeRestartVelocityEndpointFiniteVorticityInitialState_biotSavart
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse endpoint)
    (wave : IntegerWavevector)
    (waveMem : wave ∈ wholeRestartModes radius) :
    biotSavartVelocityCoefficient wave
        (wholeRestartVelocityEndpointFiniteVorticityInitialState
          radius endpoint wave) =
      wholeRestartVelocityEndpointFiniteProjection radius endpoint wave := by
  have waveNe : wave ≠ 0 := fun waveZero =>
    zero_not_mem_puncturedIntegerWaveFrequencyCube radius
      (waveZero ▸ waveMem)
  rw [wholeRestartVelocityEndpointFiniteVorticityInitialState_apply,
    if_pos waveMem,
    biotSavartVelocityCoefficient_fourierCurlCoefficient
      wave
      (wholeRestartVelocityEndpointFiniteProjection radius endpoint wave)
      waveNe,
    transverseProjection, if_neg waveNe,
    wholeRestartVelocityEndpointFiniteProjection_transverse
      radius endpoint transverse wave]
  simp

/-- Exact squared velocity mass retained by one canonical finite window. -/
def wholeRestartVelocityEndpointFiniteProjectedSquare
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState) : ℝ :=
  ∑ wave ∈ wholeRestartModes radius,
    complexCoordinateVectorNormSq
      (wholeRestartVelocityEndpointFiniteProjection radius endpoint wave)

/-- The curl-generated vorticity state has exactly one half of the retained
velocity square as its conventional kinetic energy. -/
theorem wholeRestartVelocityEndpointFiniteVorticityInitialState_kineticEnergy
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse endpoint) :
    finiteStateVorticityKineticEnergy
        (wholeRestartModes radius)
        (wholeRestartVelocityEndpointFiniteVorticityInitialState
          radius endpoint) =
      (1 / 2 : ℝ) *
        wholeRestartVelocityEndpointFiniteProjectedSquare radius endpoint := by
  unfold finiteStateVorticityKineticEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro wave waveMem
  rw [finiteStateVelocityCoefficient,
    wholeRestartVelocityEndpointFiniteVorticityInitialState_biotSavart
    radius endpoint transverse wave waveMem]

theorem two_mul_wholeRestartVelocityEndpointFiniteVorticityInitialState_kineticEnergy
    (radius : ℕ)
    (endpoint : WholeRestartVelocityEndpointState)
    (transverse : WholeRestartVelocityEndpointTransverse endpoint) :
    2 *
        finiteStateVorticityKineticEnergy
          (wholeRestartModes radius)
          (wholeRestartVelocityEndpointFiniteVorticityInitialState
            radius endpoint) =
      wholeRestartVelocityEndpointFiniteProjectedSquare radius endpoint := by
  rw [wholeRestartVelocityEndpointFiniteVorticityInitialState_kineticEnergy
    radius endpoint transverse]
  ring

/-! ## Endpoint-indexed actual unforced family -/

/-- One canonical finite Galerkin trajectory generated from the physical
velocity endpoint at a fixed radius.  Its horizon is definitionally fixed at
one; no target path enters the type. -/
structure GeneratedWholeRestartVelocityEndpointGalerkinStage
    (nu : Viscosity)
    (endpoint : WholeRestartVelocityEndpointState)
    (radius : ℕ) where
  trajectory : ℝ → ComplexVorticityHilbertState
  initial :
    trajectory 0 =
      wholeRestartVelocityEndpointFiniteVorticityInitialState
        radius endpoint
  physical :
    ∀ time ∈ Icc (0 : ℝ) 1,
      HasDerivAt trajectory
          (finiteStateVorticityGenerator
            (wholeRestartModes radius) nu.coeff (trajectory time))
          time ∧
        (∀ wave, wave ∉ wholeRestartModes radius →
          trajectory time wave = 0) ∧
        (∀ wave,
          complexWavevector wave ⬝ᵥ trajectory time wave = 0) ∧
        FiniteStateFourierReality (trajectory time)

/-- The finite existence theorem internally selects the actual unforced
trajectory on `[0,1]` from the generated endpoint projection. -/
noncomputable def generatedWholeRestartVelocityEndpointGalerkinStage
    (nu : Viscosity)
    (endpoint : WholeRestartVelocityEndpointState)
    (reality : WholeRestartVelocityEndpointReality endpoint)
    (radius : ℕ) :
    GeneratedWholeRestartVelocityEndpointGalerkinStage
      nu endpoint radius := by
  let trajectoryResult :=
    exists_finitePhysicalTrajectory_on_Icc
      (wholeRestartModes radius)
      (zero_not_mem_puncturedIntegerWaveFrequencyCube radius)
      (fun _wave waveMem =>
        puncturedIntegerWaveFrequencyCube_waveNeg_mem radius waveMem)
      nu
      (wholeRestartVelocityEndpointFiniteVorticityInitialState
        radius endpoint)
      (wholeRestartVelocityEndpointFiniteVorticityInitialState_supported
        radius endpoint)
      (wholeRestartVelocityEndpointFiniteVorticityInitialState_transverse
        radius endpoint)
      (wholeRestartVelocityEndpointFiniteVorticityInitialState_reality
        radius endpoint reality)
      1 (by norm_num)
  let trajectory := Classical.choose trajectoryResult
  have specifications := Classical.choose_spec trajectoryResult
  exact
    { trajectory := trajectory
      initial := specifications.1
      physical := specifications.2 }

/-- The source data used by the Galerkin compiler after the endpoint has
already been generated. -/
structure GeneratedWholeRestartVelocityEndpointData where
  velocityEndpoint : WholeRestartVelocityEndpointState
  velocityEndpoint_transverse :
    WholeRestartVelocityEndpointTransverse velocityEndpoint
  velocityEndpoint_reality :
    WholeRestartVelocityEndpointReality velocityEndpoint

/-- Every canonical radius and its actual unforced orbit, indexed by the
generated physical endpoint rather than by an analytic clock hypothesis. -/
structure GeneratedWholeRestartVelocityEndpointGalerkinFamilyCore
    (nu : Viscosity) where
  endpointReceipt : GeneratedWholeRestartVelocityEndpointData
  stage :
    ∀ radius : ℕ,
      GeneratedWholeRestartVelocityEndpointGalerkinStage
        nu endpointReceipt.velocityEndpoint radius

/-- Generate the complete Galerkin family from endpoint data already owned
by the source. -/
noncomputable def generatedWholeRestartVelocityEndpointGalerkinFamilyCore
    (nu : Viscosity)
    (endpointReceipt : GeneratedWholeRestartVelocityEndpointData) :
    GeneratedWholeRestartVelocityEndpointGalerkinFamilyCore nu where
  endpointReceipt := endpointReceipt
  stage := fun radius =>
    generatedWholeRestartVelocityEndpointGalerkinStage
      nu endpointReceipt.velocityEndpoint
      endpointReceipt.velocityEndpoint_reality radius

/-- Every canonical finite radius and its actual unforced orbit, generated
from one source-owned bounded-accumulation velocity endpoint. -/
structure GeneratedWholeRestartVelocityEndpointGalerkinFamily
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) where
  endpointReceipt :
    GeneratedWholeRestartVelocityWeakEndpointAtAccumulation
      initial elapsedBounded
  stage :
    ∀ radius : ℕ,
      GeneratedWholeRestartVelocityEndpointGalerkinStage
        nu endpointReceipt.velocityEndpoint radius

/-- Source-facing compiler for the complete canonical Galerkin family.
The source current and bounded elapsed-time case determine the endpoint,
every radius, every finite curl initial state, and every actual trajectory. -/
noncomputable def generatedWholeRestartVelocityEndpointGalerkinFamily
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartVelocityEndpointGalerkinFamily
      initial elapsedBounded := by
  let endpointReceipt :=
    generatedWholeRestartVelocityWeakEndpointAtAccumulation
      initial elapsedBounded
  exact
    { endpointReceipt := endpointReceipt
      stage := fun radius =>
        generatedWholeRestartVelocityEndpointGalerkinStage
          nu endpointReceipt.velocityEndpoint
          endpointReceipt.velocityEndpoint_reality radius }

namespace GeneratedWholeRestartVelocityEndpointGalerkinFamily

/-- The physical endpoint data retained by the endpoint-indexed compiler. -/
def endpointData
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (family :
      GeneratedWholeRestartVelocityEndpointGalerkinFamily
        initial elapsedBounded) :
    GeneratedWholeRestartVelocityEndpointData :=
  { velocityEndpoint := family.endpointReceipt.velocityEndpoint
    velocityEndpoint_transverse :=
      family.endpointReceipt.velocityEndpoint_transverse
    velocityEndpoint_reality :=
      family.endpointReceipt.velocityEndpoint_reality }

/-- Read the endpoint-indexed Galerkin family carried by the conditional
analytic presentation. -/
def toCore
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    {elapsedBounded : BddAbove (Set.range (elapsedTime initial))}
    (family :
      GeneratedWholeRestartVelocityEndpointGalerkinFamily
        initial elapsedBounded) :
    GeneratedWholeRestartVelocityEndpointGalerkinFamilyCore nu where
  endpointReceipt := family.endpointData
  stage := family.stage

end GeneratedWholeRestartVelocityEndpointGalerkinFamily

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityEndpointGalerkinFamily
end NavierStokes
end SaturationMonoid
