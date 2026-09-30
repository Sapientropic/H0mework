import H0mework.NavierStokes.InitialData.FiniteSupportPhysicalInvariantTrajectory

/-!
# Reality-preserving finite three-dimensional vorticity trajectories

The finite Galerkin carrier is complex, while a physical vorticity table must
satisfy the Fourier reality law

```text
omega(-k) = conj (omega(k)).
```

This module bundles wave negation followed by coordinatewise conjugation as a
real continuous linear reflection.  On every negation-closed finite support,
the complete three-dimensional vorticity generator commutes with that
reflection on the whole ambient carrier.  ODE uniqueness then forces the
source-generated transverse trajectory to remain reality fixed on a positive
time interval.

The public source theorem accepts only the raw source and viscosity.  Support
closure, the fixed initial state, the trajectory, its time window, and its
reality law are generated conclusions.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory

open scoped BigOperators Matrix Topology

open Filter Set
open Matrix
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory

noncomputable section

/-! ## The finite-support Fourier reality reflection -/

/-- Coordinatewise complex conjugation as a real continuous linear map. -/
def complexCoordinateVectorConjCLM :
    ComplexCoordinateVector →L[ℝ] ComplexCoordinateVector :=
  (starL' ℝ :
    ComplexCoordinateVector ≃L[ℝ] ComplexCoordinateVector).toContinuousLinearMap

@[simp] theorem complexCoordinateVectorConjCLM_apply
    (vector : ComplexCoordinateVector) :
    complexCoordinateVectorConjCLM vector = vectorConj vector :=
  rfl

@[simp] theorem star_complexCoordinateVector_eq_vectorConj
    (vector : ComplexCoordinateVector) :
    star vector = vectorConj vector := by
  funext coordinate
  simp [vectorConj]

/-- Read the negative Fourier row, conjugate it, and write it at the current
frequency.  Rows outside `modes` are zero. -/
def complexFourierRealityReflection
    (modes : Finset IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ] ComplexVorticityHilbertState :=
  ∑ wave ∈ modes,
    (lp.singleContinuousLinearMap
        ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2 wave).comp
      (complexCoordinateVectorConjCLM.comp
        (lp.evalCLM
          ℝ (fun _ : IntegerWavevector => ComplexCoordinateVector) 2
          (waveNeg wave)))

@[simp] theorem complexFourierRealityReflection_apply
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (wave : IntegerWavevector) :
    complexFourierRealityReflection modes state wave =
      if wave ∈ modes
      then vectorConj (state (waveNeg wave))
      else 0 := by
  classical
  simp only [complexFourierRealityReflection, _root_.sum_apply,
    ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply]
  rw [lp.coeFn_sum]
  simp [lp.single_apply, lp.evalCLM, lp.evalₗ_apply,
    complexCoordinateVectorConjCLM]

/-- The reflection is an involution on states sharply supported on a
negation-closed finite mode set. -/
theorem complexFourierRealityReflection_involutive_of_neg_closed
    {modes : Finset IntegerWavevector}
    (negClosed :
      ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    {state : ComplexVorticityHilbertState}
    (supported :
      ∀ wave, wave ∉ modes → state wave = 0) :
    complexFourierRealityReflection modes
        (complexFourierRealityReflection modes state) =
      state := by
  apply Subtype.ext
  funext wave
  by_cases waveMem : wave ∈ modes
  · have negWaveMem := negClosed waveMem
    simp [waveMem, negWaveMem]
  · simp [waveMem, supported wave waveMem]

/-! ## Whole-carrier generator equivariance -/

private theorem complexWavevector_dot_vectorConj
    (wave : IntegerWavevector)
    (vector : ComplexCoordinateVector) :
    complexWavevector wave ⬝ᵥ vectorConj vector =
      star (complexWavevector wave ⬝ᵥ vector) := by
  simp [dotProduct, complexWavevector, vectorConj]

private theorem vectorConj_real_smul
    (scalar : ℝ)
    (vector : ComplexCoordinateVector) :
    vectorConj (scalar • vector) =
      scalar • vectorConj vector := by
  funext coordinate
  simp [vectorConj]

/-- Biot--Savart evaluation commutes with the finite reality reflection at
every owned frequency. -/
theorem finiteStateVelocityCoefficient_realityReflection
    {modes : Finset IntegerWavevector}
    (state : ComplexVorticityHilbertState)
    {wave : IntegerWavevector}
    (waveMem : wave ∈ modes) :
    finiteStateVelocityCoefficient
        (complexFourierRealityReflection modes state) wave =
      vectorConj
        (finiteStateVelocityCoefficient state (waveNeg wave)) := by
  rw [finiteStateVelocityCoefficient,
    complexFourierRealityReflection_apply, if_pos waveMem,
    finiteStateVelocityCoefficient]
  simpa using
    (biotSavartVelocityCoefficient_waveNeg_vectorConj
      (waveNeg wave) (state (waveNeg wave)))

/-- One ordered nonlinear row is carried to the conjugate row of the
simultaneously negated pair. -/
theorem finiteStateVorticityNonlinearPairContribution_realityReflection
    {modes : Finset IntegerWavevector}
    (state : ComplexVorticityHilbertState)
    (pair : StretchingPair)
    (firstMem : pair.1 ∈ modes)
    (secondMem : pair.2 ∈ modes) :
    finiteStateVorticityNonlinearPairContribution
        (complexFourierRealityReflection modes state) pair =
      vectorConj
        (finiteStateVorticityNonlinearPairContribution
          state (stretchingPairNeg pair)) := by
  rw [finiteStateVorticityNonlinearPairContribution,
    finiteStateVorticityNonlinearPairContribution]
  simp only [stretchingPairNeg,
    complexFourierRealityReflection_apply,
    if_pos firstMem, if_pos secondMem,
    finiteStateVelocityCoefficient_realityReflection
      state firstMem,
    finiteStateVelocityCoefficient_realityReflection
      state secondMem,
    complexWavevector_dot_vectorConj,
    vectorConj_sub, vectorConj_smul]
  funext coordinate
  simp [vectorConj, complexWavevector_waveNeg]

/-- Simultaneous wave negation as an involution of the ambient lattice. -/
def integerWaveNegEquiv : IntegerWavevector ≃ IntegerWavevector where
  toFun := waveNeg
  invFun := waveNeg
  left_inv := waveNeg_involutive
  right_inv := waveNeg_involutive

@[simp] theorem integerWaveNegEquiv_apply
    (wave : IntegerWavevector) :
    integerWaveNegEquiv wave = waveNeg wave :=
  rfl

/-- The complete nonlinear output aggregate commutes with reality reflection
on every negation-closed finite support.  No reality premise is placed on the
ambient state. -/
theorem finiteStateVorticityNonlinearCoefficientAt_realityReflection
    {modes : Finset IntegerWavevector}
    (negClosed :
      ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (state : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    finiteStateVorticityNonlinearCoefficientAt modes
        (complexFourierRealityReflection modes state) output =
      vectorConj
        (finiteStateVorticityNonlinearCoefficientAt
          modes state (waveNeg output)) := by
  classical
  simp only [finiteStateVorticityNonlinearCoefficientAt,
    vectorConj_finset_sum]
  rw [Finset.sum_equiv integerWaveNegEquiv]
  · intro first
    exact (show waveNeg first ∈ modes ↔ first ∈ modes from
      ⟨fun membership => by
        simpa using negClosed membership,
       negClosed⟩).symm
  · intro first firstMem
    rw [Finset.sum_equiv integerWaveNegEquiv]
    · intro second
      exact (show waveNeg second ∈ modes ↔ second ∈ modes from
        ⟨fun membership => by
          simpa using negClosed membership,
         negClosed⟩).symm
    · intro second secondMem
      rw [
        finiteStateVorticityNonlinearPairContribution_realityReflection
          state (first, second) firstMem secondMem]
      have pairCondition :
          first + second = output ↔
            integerWaveNegEquiv first + integerWaveNegEquiv second =
              waveNeg output := by
        constructor
        · intro pairSum
          simpa [integerWaveNegEquiv_apply, waveNeg, add_comm] using
            congrArg waveNeg pairSum
        · intro pairSum
          have := congrArg waveNeg pairSum
          simpa [integerWaveNegEquiv_apply, waveNeg, add_comm] using this
      by_cases pairSum : first + second = output
      · rw [if_pos pairSum, if_pos (pairCondition.mp pairSum)]
        simp [integerWaveNegEquiv_apply, stretchingPairNeg]
      · rw [if_neg pairSum,
          if_neg (fun equality => pairSum (pairCondition.mpr equality))]
        simp

@[simp] theorem integerWaveViscousMultiplier_waveNeg
    (wave : IntegerWavevector) :
    integerWaveViscousMultiplier (waveNeg wave) =
      integerWaveViscousMultiplier wave := by
  simp [integerWaveViscousMultiplier]

/-- Wave-negation plus conjugation commutes with the whole finite Galerkin
vorticity generator on a negation-closed support.  This is a whole-carrier
identity: `state` is arbitrary. -/
theorem finiteStateVorticityGenerator_realityReflection_commutes
    {modes : Finset IntegerWavevector}
    (negClosed :
      ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    complexFourierRealityReflection modes
        (finiteStateVorticityGenerator modes ν state) =
      finiteStateVorticityGenerator modes ν
        (complexFourierRealityReflection modes state) := by
  apply Subtype.ext
  funext output
  by_cases outputMem : output ∈ modes
  · have negOutputMem : waveNeg output ∈ modes :=
      negClosed outputMem
    rw [complexFourierRealityReflection_apply, if_pos outputMem,
      finiteStateVorticityGenerator_apply, if_pos negOutputMem,
      finiteStateVorticityGenerator_apply, if_pos outputMem,
      finiteStateVorticityNonlinearCoefficientAt_realityReflection
        negClosed state output,
      complexFourierRealityReflection_apply, if_pos outputMem,
      integerWaveViscousMultiplier_waveNeg,
      vectorConj_sub, vectorConj_real_smul]
  · rw [complexFourierRealityReflection_apply, if_neg outputMem,
      finiteStateVorticityGenerator_apply, if_neg outputMem]

/-! ## Source-generated fixed initial state -/

/-- The source-generated complex coefficient table is fixed by the reality
reflection on its own generated support. -/
theorem complexFourierRealityReflection_generatedSourceInitial
    (source : RawVorticityFourierSource) :
    complexFourierRealityReflection (generatedSupport source)
        (generatedComplexVorticityState source (generatedSupport source)) =
      generatedComplexVorticityState source (generatedSupport source) := by
  apply Subtype.ext
  funext wave
  by_cases waveMem : wave ∈ generatedSupport source
  · have negWaveMem :=
      generatedSupport_waveNeg_mem source waveMem
    calc
      complexFourierRealityReflection (generatedSupport source)
          (generatedComplexVorticityState source
            (generatedSupport source)) wave =
          vectorConj
            (generatedComplexVorticityState source
              (generatedSupport source) (waveNeg wave)) := by
            rw [complexFourierRealityReflection_apply,
              if_pos waveMem]
      _ = vectorConj
          (generatedVorticityCoefficient source (waveNeg wave)) := by
            congr 1
            simp [negWaveMem]
      _ = generatedVorticityCoefficient source wave := by
            rw [generatedVorticityCoefficient_waveNeg,
              vectorConj_involutive]
      _ = generatedComplexVorticityState source
          (generatedSupport source) wave := by
            symm
            simp [waveMem]
  · calc
      complexFourierRealityReflection (generatedSupport source)
          (generatedComplexVorticityState source
            (generatedSupport source)) wave = 0 := by
            rw [complexFourierRealityReflection_apply,
              if_neg waveMem]
      _ = generatedComplexVorticityState source
          (generatedSupport source) wave := by
            symm
            simp [waveMem]

/-! ## Reality generated along an actual transverse trajectory -/

/-- Global Fourier reality on the common coefficient carrier. -/
def FiniteStateFourierReality
    (state : ComplexVorticityHilbertState) : Prop :=
  ∀ wave,
    state (waveNeg wave) = vectorConj (state wave)

/-- A sharply supported state fixed by the finite reflection satisfies the
global Fourier reality law. -/
theorem finiteStateFourierReality_of_reflection_fixed
    {modes : Finset IntegerWavevector}
    (negClosed :
      ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes)
    {state : ComplexVorticityHilbertState}
    (supported :
      ∀ wave, wave ∉ modes → state wave = 0)
    (fixed :
      complexFourierRealityReflection modes state = state) :
    FiniteStateFourierReality state := by
  intro wave
  by_cases waveMem : wave ∈ modes
  · have negWaveMem : waveNeg wave ∈ modes :=
      negClosed waveMem
    have rowEquality :=
      congrArg
        (fun value : ComplexVorticityHilbertState =>
          value (waveNeg wave)) fixed
    rw [complexFourierRealityReflection_apply,
      if_pos negWaveMem, waveNeg_involutive] at rowEquality
    exact rowEquality.symm
  · have negWaveNotMem : waveNeg wave ∉ modes := by
      intro negWaveMem
      exact waveMem (by simpa using negClosed negWaveMem)
    rw [supported wave waveMem,
      supported (waveNeg wave) negWaveNotMem,
      vectorConj_zero]

/-- Every raw source generates one positive-time trajectory on which the
original finite three-dimensional Galerkin law, sharp finite support,
transversality, and Fourier reality hold simultaneously.

Reality of the path is not a premise.  It follows from source-generated
negation closure, whole-carrier generator equivariance, and local ODE
uniqueness. -/
theorem generatedSource_transverseRealityLocalTrajectory
    (source : RawVorticityFourierSource)
    (ν : ℝ) :
    ∃ (trajectory : ℝ → ComplexVorticityHilbertState)
        (physicalTime : ℝ),
      0 < physicalTime ∧
        trajectory 0 =
          generatedComplexVorticityState source
            (generatedSupport source) ∧
        ∀ t ∈ Icc (0 : ℝ) physicalTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                (generatedSupport source) ν (trajectory t)) t ∧
            (∀ wave,
              wave ∉ generatedSupport source →
                trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t) := by
  obtain
      ⟨trajectory, originalTime, originalTimePos, initial, evolves⟩ :=
    generatedSource_transverseLocalTrajectory source ν
  let modes := generatedSupport source
  let generator := finiteStateVorticityGenerator modes ν
  let reflection := complexFourierRealityReflection modes
  have negClosed :
      ∀ {wave}, wave ∈ modes → waveNeg wave ∈ modes := by
    intro wave waveMem
    exact generatedSupport_waveNeg_mem source waveMem
  have zeroMem : (0 : ℝ) ∈ Icc (0 : ℝ) originalTime :=
    ⟨le_rfl, le_of_lt originalTimePos⟩
  have actualZero :
      HasDerivAt trajectory (generator (trajectory 0)) 0 := by
    simpa [generator, modes] using (evolves 0 zeroMem).1
  have initialFixed :
      reflection
          (generatedComplexVorticityState source
            (generatedSupport source)) =
        generatedComplexVorticityState source
          (generatedSupport source) := by
    simpa [reflection, modes] using
      complexFourierRealityReflection_generatedSourceInitial source
  have sameInitial :
      trajectory 0 = (reflection ∘ trajectory) 0 := by
    calc
      trajectory 0 =
          generatedComplexVorticityState source
            (generatedSupport source) := initial
      _ = reflection
          (generatedComplexVorticityState source
            (generatedSupport source)) := initialFixed.symm
      _ = reflection (trajectory 0) :=
        congrArg reflection initial.symm
      _ = (reflection ∘ trajectory) 0 := rfl
  have generatorContDiffAt :
      ContDiffAt ℝ 1 generator (trajectory 0) := by
    exact
      (finiteStateVorticityGenerator_contDiff modes ν).contDiffAt
  obtain ⟨K, neighborhood, neighborhoodMem, lipschitz⟩ :=
    generatorContDiffAt.exists_lipschitzOnWith
  have trajectoryContinuous : ContinuousAt trajectory 0 :=
    actualZero.continuousAt
  have reflectedContinuous :
      ContinuousAt (reflection ∘ trajectory) 0 :=
    reflection.continuous.continuousAt.comp trajectoryContinuous
  have trajectoryMem :
      ∀ᶠ time in 𝓝 (0 : ℝ),
        trajectory time ∈ neighborhood := by
    apply trajectoryContinuous
    exact neighborhoodMem
  have reflectedMem :
      ∀ᶠ time in 𝓝 (0 : ℝ),
        (reflection ∘ trajectory) time ∈ neighborhood := by
    apply reflectedContinuous
    rw [← sameInitial]
    exact neighborhoodMem
  have timeBelow :
      ∀ᶠ time in 𝓝 (0 : ℝ), time < originalTime :=
    eventually_lt_nhds originalTimePos
  obtain ⟨ε, εPos, localData⟩ :=
    Metric.eventually_nhds_iff_ball.mp
      (trajectoryMem.and (reflectedMem.and timeBelow))
  let physicalTime := min ε originalTime / 2
  have minTimePos : 0 < min ε originalTime :=
    lt_min εPos originalTimePos
  have physicalTimePos : 0 < physicalTime := by
    dsimp [physicalTime]
    positivity
  have physicalTimeLtEpsilon : physicalTime < ε := by
    dsimp [physicalTime]
    have minLe : min ε originalTime ≤ ε :=
      min_le_left _ _
    linarith
  have physicalTimeLeOriginal : physicalTime ≤ originalTime := by
    dsimp [physicalTime]
    have minLe : min ε originalTime ≤ originalTime :=
      min_le_right _ _
    linarith
  have localMembership :
      ∀ t ∈ Icc (0 : ℝ) physicalTime,
        trajectory t ∈ neighborhood ∧
          (reflection ∘ trajectory) t ∈ neighborhood := by
    intro t timeMem
    have timeLtEpsilon :
        t < ε :=
      lt_of_le_of_lt timeMem.2 physicalTimeLtEpsilon
    have ballMem : t ∈ Metric.ball (0 : ℝ) ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      simpa [abs_of_nonneg timeMem.1] using timeLtEpsilon
    exact
      ⟨(localData t ballMem).1,
        (localData t ballMem).2.1⟩
  have actualLaw :
      ∀ t ∈ Icc (0 : ℝ) physicalTime,
        HasDerivAt trajectory (generator (trajectory t)) t := by
    intro t timeMem
    apply (evolves t ?_).1
    exact
      ⟨timeMem.1,
        le_trans timeMem.2 physicalTimeLeOriginal⟩
  have reflectedLaw :
      ∀ t ∈ Icc (0 : ℝ) physicalTime,
        HasDerivAt (reflection ∘ trajectory)
          (generator ((reflection ∘ trajectory) t)) t := by
    intro t timeMem
    have reflected :=
      reflection.hasFDerivAt.comp_hasDerivAt
        t (actualLaw t timeMem)
    rw [finiteStateVorticityGenerator_realityReflection_commutes
      negClosed ν] at reflected
    simpa [Function.comp_def, reflection, generator, modes] using reflected
  have trajectoryContinuousOn :
      ContinuousOn trajectory (Icc (0 : ℝ) physicalTime) :=
    HasDerivAt.continuousOn actualLaw
  have reflectedContinuousOn :
      ContinuousOn (reflection ∘ trajectory)
        (Icc (0 : ℝ) physicalTime) :=
    HasDerivAt.continuousOn reflectedLaw
  have fixedForward :
      EqOn trajectory (reflection ∘ trajectory)
        (Icc (0 : ℝ) physicalTime) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ : ℝ => generator)
      (s := fun _ : ℝ => neighborhood)
      (K := K)
    · intro t timeMem
      exact lipschitz
    · exact trajectoryContinuousOn
    · intro t timeMem
      exact
        (actualLaw t (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact (localMembership t (mem_Icc_of_Ico timeMem)).1
    · exact reflectedContinuousOn
    · intro t timeMem
      exact
        (reflectedLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact (localMembership t (mem_Icc_of_Ico timeMem)).2
    · exact sameInitial
  refine
    ⟨trajectory, physicalTime, physicalTimePos, initial, ?_⟩
  intro t timeMem
  have originalMem : t ∈ Icc (0 : ℝ) originalTime :=
    ⟨timeMem.1,
      le_trans timeMem.2 physicalTimeLeOriginal⟩
  obtain ⟨actual, supported, transverse⟩ :=
    evolves t originalMem
  have reflectionFixed :
      reflection (trajectory t) = trajectory t := by
    exact (fixedForward timeMem).symm
  refine
    ⟨actual, supported, transverse,
      finiteStateFourierReality_of_reflection_fixed
        negClosed supported ?_⟩
  simpa [reflection] using reflectionFixed

end

end ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
end NavierStokes
end SaturationMonoid
