import H0mework.NavierStokes.Galerkin.CriticalEndpointExclusion
import H0mework.NavierStokes.InitialData.FinitePhysicalTrajectoryEndpointSplice

/-!
# Common-time existence for a fixed physical Galerkin system

At one fixed finite Fourier inventory, the critical enstrophy barrier keeps
every physical trajectory in one ambient ball.  Finite-dimensional
compactness then generates a single positive Picard window which works from
every state in that ball.

This module first applies that construction to the source-owned
transverse-support projection of the actual generator.  Idempotent
write-back recovers the unprojected Galerkin equation, while the commuting
Fourier-reality reflection and ODE uniqueness recover reality on the same
window.  The resulting uniform physical restart is then iterated a finite
number of times to meet any requested finite time.

Thus the target time is only a consumer request.  No trajectory, maximal
solution, continuation witness, target coverage, or cutoff-uniform lifespan
occurs in the theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence

open scoped BigOperators ENNReal Topology

open Set ODE
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportPhysicalInvariantTrajectory
open ThreeDimensionalVorticityCoefficientFiniteSupportRealityTrajectory
open ThreeDimensionalVorticityCoefficientFiniteGalerkinEnstrophyBalance
open ThreeDimensionalVorticityCoefficientFiniteGalerkinAmbientNorm
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalEnstrophyBarrier
open ThreeDimensionalVorticityCoefficientFiniteGalerkinCriticalContinuation
open ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds
open ThreeDimensionalVorticityCoefficientFinitePhysicalTrajectoryEndpointSplice

noncomputable section

private theorem finiteTransverseSupportProjection_fixed_of_physical
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ state wave = 0) :
    finiteTransverseSupportProjection modes state = state := by
  apply lp.ext
  funext wave
  rw [finiteTransverseSupportProjection_apply]
  by_cases waveMem : wave ∈ modes
  · rw [if_pos waveMem]
    exact
      transverseProjection_eq_self_of_transverse
        (fun waveZero => zeroNotMem (waveZero ▸ waveMem))
        (transverse wave waveMem)
  · rw [if_neg waveMem, supported wave waveMem]

private theorem complexFourierRealityReflection_fixed_of_physical
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (supported : ∀ wave, wave ∉ modes → state wave = 0)
    (reality : FiniteStateFourierReality state) :
    complexFourierRealityReflection modes state = state := by
  apply lp.ext
  funext wave
  rw [complexFourierRealityReflection_apply]
  by_cases waveMem : wave ∈ modes
  · rw [if_pos waveMem]
    have reflectedReality := reality (waveNeg wave)
    simpa using reflectedReality.symm
  · rw [if_neg waveMem, supported wave waveMem]

/-! ## Canonical fixed-inventory generator bound -/

/-- Actual norm range of the transverse-support projected generator on one
closed carrier ball. -/
def projectedGeneratorNormRange
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) : Set ℝ :=
  (fun state : ComplexVorticityHilbertState =>
    ‖finiteStateTransverseProjectedGenerator modes ν state‖) ''
      Metric.closedBall
        (0 : ComplexVorticityHilbertState) radius

theorem projectedGeneratorNormRange_nonempty
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    (projectedGeneratorNormRange modes ν radius).Nonempty := by
  refine
    ⟨‖finiteStateTransverseProjectedGenerator modes ν 0‖,
      0, ?_, rfl⟩
  simp

theorem projectedGeneratorNormRange_bddAbove
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    BddAbove (projectedGeneratorNormRange modes ν radius) := by
  obtain
      ⟨generatorBound, _generatorLipschitz,
        generatorNormLe, _generatorLipschitzOn⟩ :=
    exists_finiteStateVorticityGenerator_bounds
      modes ν (radius : ℝ)
  let projection :=
    finiteTransverseSupportProjection modes
  refine
    ⟨‖projection‖ * (generatorBound : ℝ), ?_⟩
  rintro value ⟨state, stateMem, rfl⟩
  change
    ‖projection
        (finiteStateVorticityGenerator modes ν state)‖ ≤
      ‖projection‖ * (generatorBound : ℝ)
  exact
    (projection.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left
        (generatorNormLe state stateMem)
        (norm_nonneg projection))

/-- Canonical least-upper-bound norm of the actual projected generator on
one fixed carrier ball. -/
def projectedGeneratorFieldNormSup
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) : ℝ :=
  sSup (projectedGeneratorNormRange modes ν radius)

theorem projectedGeneratorFieldNormSup_nonneg
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    0 ≤ projectedGeneratorFieldNormSup modes ν radius := by
  let zeroValue :=
    ‖finiteStateTransverseProjectedGenerator modes ν 0‖
  have zeroValueMem :
      zeroValue ∈ projectedGeneratorNormRange modes ν radius := by
    refine ⟨0, ?_, rfl⟩
    simp
  exact
    (norm_nonneg _).trans
      (le_csSup
        (projectedGeneratorNormRange_bddAbove
          modes ν radius)
        zeroValueMem)

/-- Canonical nonnegative field bound used by the quantified local Picard
producer.  Unlike an arbitrary compactness witness, this value is fixed by
the actual norm range. -/
def canonicalProjectedGeneratorFieldBound
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) : NNReal :=
  ⟨projectedGeneratorFieldNormSup modes ν radius,
    projectedGeneratorFieldNormSup_nonneg modes ν radius⟩

@[simp] theorem coe_canonicalProjectedGeneratorFieldBound
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal) :
    (canonicalProjectedGeneratorFieldBound
      modes ν radius : ℝ) =
        projectedGeneratorFieldNormSup modes ν radius :=
  rfl

theorem projectedGenerator_norm_le_canonicalFieldBound
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal)
    (state : ComplexVorticityHilbertState)
    (stateMem :
      state ∈
        Metric.closedBall
          (0 : ComplexVorticityHilbertState) radius) :
    ‖finiteStateTransverseProjectedGenerator modes ν state‖ ≤
      canonicalProjectedGeneratorFieldBound modes ν radius := by
  exact
    le_csSup
      (projectedGeneratorNormRange_bddAbove modes ν radius)
      ⟨state, stateMem, rfl⟩

/-- The canonical field bound is below every other valid upper bound on the
same actual projected-generator norm range. -/
theorem canonicalProjectedGeneratorFieldBound_le
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : NNReal)
    (bound : ℝ)
    (bounds :
      ∀ state ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) radius,
        ‖finiteStateTransverseProjectedGenerator
            modes ν state‖ ≤
          bound) :
    (canonicalProjectedGeneratorFieldBound
        modes ν radius : ℝ) ≤
      bound := by
  apply csSup_le
    (projectedGeneratorNormRange_nonempty modes ν radius)
  intro value valueMem
  rcases valueMem with ⟨state, stateMem, rfl⟩
  exact bounds state stateMem

/-! ## Uniform projected Picard window -/

/-- Fixed-mode compactness generates one positive Picard window for the
transverse-support projected generator on every restart time.  All bounds
are conclusions and may depend on the fixed inventory and viscosity. -/
theorem exists_uniformPicard_finiteStateTransverseProjectedGenerator
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (innerRadius outerRadius : NNReal)
    (radiusRoom : innerRadius < outerRadius) :
    ∃ (ε : ℝ) (εPos : 0 < ε)
        (fieldBound lipschitzBound : NNReal),
      ∀ restartTime : ℝ,
        IsPicardLindelof
          (fun _ =>
            finiteStateTransverseProjectedGenerator modes ν)
          (tmin := restartTime - ε)
          (tmax := restartTime + ε)
          ⟨restartTime, by
            constructor <;> linarith⟩
          (0 : ComplexVorticityHilbertState)
          outerRadius innerRadius
          fieldBound lipschitzBound := by
  obtain
      ⟨generatorBound, generatorLipschitz,
        generatorNormLe, generatorLipschitzOn⟩ :=
    exists_finiteStateVorticityGenerator_bounds
      modes ν (outerRadius : ℝ)
  let projection :=
    finiteTransverseSupportProjection modes
  let projectionNorm : NNReal := ‖projection‖₊
  let fieldBound : NNReal := projectionNorm * generatorBound
  let lipschitzBound : NNReal :=
    projectionNorm * generatorLipschitz
  have fieldNormLe :
      ∀ state ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) outerRadius,
        ‖finiteStateTransverseProjectedGenerator modes ν state‖ ≤
          fieldBound := by
    intro state stateMem
    change
      ‖projection
          (finiteStateVorticityGenerator modes ν state)‖ ≤
        fieldBound
    calc
      ‖projection
          (finiteStateVorticityGenerator modes ν state)‖ ≤
          ‖projection‖ *
            ‖finiteStateVorticityGenerator modes ν state‖ :=
        projection.le_opNorm _
      _ ≤ ‖projection‖ * generatorBound := by
        exact
          mul_le_mul_of_nonneg_left
            (generatorNormLe state stateMem)
            (norm_nonneg projection)
      _ = fieldBound := by
        rfl
  have fieldLipschitz :
      LipschitzOnWith lipschitzBound
        (finiteStateTransverseProjectedGenerator modes ν)
        (Metric.closedBall
          (0 : ComplexVorticityHilbertState) outerRadius) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro left leftMem right rightMem
    change
      ‖projection
          (finiteStateVorticityGenerator modes ν left) -
        projection
          (finiteStateVorticityGenerator modes ν right)‖ ≤
        lipschitzBound * ‖left - right‖
    rw [← map_sub]
    calc
      ‖projection
          (finiteStateVorticityGenerator modes ν left -
            finiteStateVorticityGenerator modes ν right)‖ ≤
          ‖projection‖ *
            ‖finiteStateVorticityGenerator modes ν left -
              finiteStateVorticityGenerator modes ν right‖ :=
        projection.le_opNorm _
      _ ≤
          ‖projection‖ *
            (generatorLipschitz * ‖left - right‖) := by
        exact
          mul_le_mul_of_nonneg_left
            ((lipschitzOnWith_iff_norm_sub_le.mp
              generatorLipschitzOn) leftMem rightMem)
            (norm_nonneg projection)
      _ = lipschitzBound * ‖left - right‖ := by
        simp [lipschitzBound, projectionNorm]
        ring
  have gapPos :
      0 < (outerRadius : ℝ) - (innerRadius : ℝ) := by
    exact sub_pos.mpr (NNReal.coe_lt_coe.mpr radiusRoom)
  let ε : ℝ :=
    ((outerRadius : ℝ) - (innerRadius : ℝ)) /
      (2 * ((fieldBound : ℝ) + 1))
  have denominatorPos :
      0 < 2 * ((fieldBound : ℝ) + 1) := by
    positivity
  have εPos : 0 < ε :=
    div_pos gapPos denominatorPos
  refine
    ⟨ε, εPos, fieldBound, lipschitzBound, ?_⟩
  intro restartTime
  apply IsPicardLindelof.of_time_independent
      fieldNormLe fieldLipschitz
  have fieldBoundNonneg : 0 ≤ (fieldBound : ℝ) :=
    NNReal.coe_nonneg _
  have gapNonneg :
      0 ≤ (outerRadius : ℝ) - (innerRadius : ℝ) :=
    gapPos.le
  simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
  dsimp [ε]
  have ratioLeOne :
      (fieldBound : ℝ) /
          (2 * ((fieldBound : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one denominatorPos).mpr
    linarith
  calc
    (fieldBound : ℝ) *
          (((outerRadius : ℝ) - (innerRadius : ℝ)) /
            (2 * ((fieldBound : ℝ) + 1))) =
        ((fieldBound : ℝ) /
          (2 * ((fieldBound : ℝ) + 1))) *
          ((outerRadius : ℝ) - (innerRadius : ℝ)) := by
      ring
    _ ≤
        1 * ((outerRadius : ℝ) - (innerRadius : ℝ)) :=
      mul_le_mul_of_nonneg_right ratioLeOne gapNonneg
    _ =
        (outerRadius : ℝ) - (innerRadius : ℝ) := by
      ring

/-- Quantified form of the projected Picard producer.  In addition to the
actual Picard object, it exposes the precise radius/field-bound lifetime
chosen by the construction. -/
theorem
    exists_quantifiedUniformPicard_finiteStateTransverseProjectedGenerator
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (innerRadius outerRadius : NNReal)
    (radiusRoom : innerRadius < outerRadius) :
    ∃ (ε : ℝ) (εPos : 0 < ε)
        (fieldBound lipschitzBound : NNReal),
      fieldBound =
          canonicalProjectedGeneratorFieldBound
            modes ν outerRadius ∧
        ε =
            ((outerRadius : ℝ) - (innerRadius : ℝ)) /
              (2 * ((fieldBound : ℝ) + 1)) ∧
          ∀ restartTime : ℝ,
            IsPicardLindelof
              (fun _ =>
                finiteStateTransverseProjectedGenerator modes ν)
              (tmin := restartTime - ε)
              (tmax := restartTime + ε)
              ⟨restartTime, by
                constructor <;> linarith⟩
              (0 : ComplexVorticityHilbertState)
              outerRadius innerRadius
              fieldBound lipschitzBound := by
  obtain
      ⟨_generatorBound, generatorLipschitz,
        _generatorNormLe, generatorLipschitzOn⟩ :=
    exists_finiteStateVorticityGenerator_bounds
      modes ν (outerRadius : ℝ)
  let projection :=
    finiteTransverseSupportProjection modes
  let projectionNorm : NNReal := ‖projection‖₊
  let fieldBound : NNReal :=
    canonicalProjectedGeneratorFieldBound
      modes ν outerRadius
  let lipschitzBound : NNReal :=
    projectionNorm * generatorLipschitz
  have fieldNormLe :
      ∀ state ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) outerRadius,
        ‖finiteStateTransverseProjectedGenerator modes ν state‖ ≤
          fieldBound := by
    intro state stateMem
    exact
      projectedGenerator_norm_le_canonicalFieldBound
        modes ν outerRadius state stateMem
  have fieldLipschitz :
      LipschitzOnWith lipschitzBound
        (finiteStateTransverseProjectedGenerator modes ν)
        (Metric.closedBall
          (0 : ComplexVorticityHilbertState) outerRadius) := by
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro left leftMem right rightMem
    change
      ‖projection
          (finiteStateVorticityGenerator modes ν left) -
        projection
          (finiteStateVorticityGenerator modes ν right)‖ ≤
        lipschitzBound * ‖left - right‖
    rw [← map_sub]
    calc
      ‖projection
          (finiteStateVorticityGenerator modes ν left -
            finiteStateVorticityGenerator modes ν right)‖ ≤
          ‖projection‖ *
            ‖finiteStateVorticityGenerator modes ν left -
              finiteStateVorticityGenerator modes ν right‖ :=
        projection.le_opNorm _
      _ ≤
          ‖projection‖ *
            (generatorLipschitz * ‖left - right‖) := by
        exact
          mul_le_mul_of_nonneg_left
            ((lipschitzOnWith_iff_norm_sub_le.mp
              generatorLipschitzOn) leftMem rightMem)
            (norm_nonneg projection)
      _ = lipschitzBound * ‖left - right‖ := by
        simp [lipschitzBound, projectionNorm]
        ring
  have gapPos :
      0 < (outerRadius : ℝ) - (innerRadius : ℝ) := by
    exact sub_pos.mpr (NNReal.coe_lt_coe.mpr radiusRoom)
  let ε : ℝ :=
    ((outerRadius : ℝ) - (innerRadius : ℝ)) /
      (2 * ((fieldBound : ℝ) + 1))
  have denominatorPos :
      0 < 2 * ((fieldBound : ℝ) + 1) := by
    positivity
  have εPos : 0 < ε :=
    div_pos gapPos denominatorPos
  refine
    ⟨ε, εPos, fieldBound, lipschitzBound, rfl, rfl, ?_⟩
  intro restartTime
  apply IsPicardLindelof.of_time_independent
      fieldNormLe fieldLipschitz
  have fieldBoundNonneg : 0 ≤ (fieldBound : ℝ) :=
    NNReal.coe_nonneg _
  have gapNonneg :
      0 ≤ (outerRadius : ℝ) - (innerRadius : ℝ) :=
    gapPos.le
  simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
  dsimp [ε]
  have ratioLeOne :
      (fieldBound : ℝ) /
          (2 * ((fieldBound : ℝ) + 1)) ≤ 1 := by
    apply (div_le_one denominatorPos).mpr
    linarith
  calc
    (fieldBound : ℝ) *
          (((outerRadius : ℝ) - (innerRadius : ℝ)) /
            (2 * ((fieldBound : ℝ) + 1))) =
        ((fieldBound : ℝ) /
          (2 * ((fieldBound : ℝ) + 1))) *
          ((outerRadius : ℝ) - (innerRadius : ℝ)) := by
      ring
    _ ≤
        1 * ((outerRadius : ℝ) - (innerRadius : ℝ)) :=
      mul_le_mul_of_nonneg_right ratioLeOne gapNonneg
    _ =
        (outerRadius : ℝ) - (innerRadius : ℝ) := by
      ring

/-! ## One uniform physical restart -/

/-- On a fixed mode inventory and a fixed inner carrier ball, one positive
time works for every physical initial state in that ball.  The actual
trajectory, its support law, transversality, and Fourier reality are all
generated in the conclusion. -/
theorem exists_uniform_finitePhysicalTrajectory
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (innerRadius : NNReal) :
    ∃ uniformTime > (0 : ℝ),
      ∀ initialState : ComplexVorticityHilbertState,
        initialState ∈
            Metric.closedBall
              (0 : ComplexVorticityHilbertState) innerRadius →
          (∀ wave, wave ∉ modes → initialState wave = 0) →
          (∀ wave ∈ modes,
            complexWavevector wave ⬝ᵥ initialState wave = 0) →
          FiniteStateFourierReality initialState →
          ∃ trajectory : ℝ → ComplexVorticityHilbertState,
            trajectory 0 = initialState ∧
              ∀ t ∈ Icc (0 : ℝ) uniformTime,
                HasDerivAt trajectory
                    (finiteStateVorticityGenerator
                      modes ν (trajectory t)) t ∧
                  (∀ wave, wave ∉ modes → trajectory t wave = 0) ∧
                  (∀ wave,
                    complexWavevector wave ⬝ᵥ
                      trajectory t wave = 0) ∧
                  FiniteStateFourierReality (trajectory t) := by
  let outerRadius : NNReal := innerRadius + 1
  have radiusRoom : innerRadius < outerRadius := by
    dsimp [outerRadius]
    exact lt_add_of_pos_right innerRadius (by norm_num)
  obtain
      ⟨ε, εPos, fieldBound, lipschitzBound,
        uniformPicard⟩ :=
    exists_uniformPicard_finiteStateTransverseProjectedGenerator
      modes ν innerRadius outerRadius radiusRoom
  let uniformTime : ℝ := ε / 2
  have uniformTimePos : 0 < uniformTime := by
    dsimp [uniformTime]
    linarith
  refine ⟨uniformTime, uniformTimePos, ?_⟩
  intro initialState initialMem supported transverse reality
  have initialProjectionFixed :
      finiteTransverseSupportProjection modes initialState =
        initialState :=
    finiteTransverseSupportProjection_fixed_of_physical
      modes zeroNotMem initialState supported transverse
  let picard :=
    uniformPicard 0
  obtain
      ⟨trajectory, trajectoryInitial,
        picardProperties⟩ :=
    exists_picard_path_hasDerivWithinAt_mem_closedBall
      picard initialMem
  have timeInPicardInterior :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        t ∈ Ioo (-ε) ε := by
    intro t timeMem
    constructor
    · linarith [timeMem.1]
    · dsimp [uniformTime] at timeMem
      linarith [timeMem.2]
  have projectedLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt trajectory
          (finiteStateTransverseProjectedGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    have interior := timeInPicardInterior t timeMem
    have picardInterior :
        t ∈ Ioo (0 - ε) (0 + ε) := by
      simpa using interior
    exact
      (picardProperties t
        (Ioo_subset_Icc_self picardInterior)).1
        |>.hasDerivAt
          (Icc_mem_nhds picardInterior.1 picardInterior.2)
  have trajectoryOuterMem :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        trajectory t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) outerRadius := by
    intro t timeMem
    have picardInterior :
        t ∈ Ioo (0 - ε) (0 + ε) := by
      simpa using timeInPicardInterior t timeMem
    exact
      (picardProperties t
        (Ioo_subset_Icc_self
          picardInterior)).2
  have projectedPathLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt
          ((finiteTransverseSupportProjection modes) ∘ trajectory)
          (finiteStateTransverseProjectedGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    have projected :=
      (finiteTransverseSupportProjection modes).hasFDerivAt
        |>.comp_hasDerivAt t (projectedLaw t timeMem)
    simpa [finiteStateTransverseProjectedGenerator,
      finiteTransverseSupportProjection_idempotent] using projected
  have trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) uniformTime) :=
    HasDerivAt.continuousOn projectedLaw
  have projectedPathContinuous :
      ContinuousOn
        ((finiteTransverseSupportProjection modes) ∘ trajectory)
        (Icc (0 : ℝ) uniformTime) :=
    HasDerivAt.continuousOn projectedPathLaw
  have sameProjectionInitial :
      trajectory 0 =
        finiteTransverseSupportProjection modes (trajectory 0) := by
    rw [trajectoryInitial, initialProjectionFixed]
  have fixedForward :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        trajectory t =
          finiteTransverseSupportProjection modes (trajectory t) := by
    apply eq_of_has_deriv_right_eq
      (f' := fun t =>
        finiteStateTransverseProjectedGenerator
          modes ν (trajectory t))
    · intro t timeMem
      exact
        (projectedLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact
        (projectedPathLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · exact trajectoryContinuous
    · exact projectedPathContinuous
    · exact sameProjectionInitial
  have actualLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    have fixed :
        finiteTransverseSupportProjection modes (trajectory t) =
          trajectory t :=
      (fixedForward t timeMem).symm
    have generatorFixed :=
      finiteTransverseSupportProjection_generator_of_fixed
        zeroNotMem ν fixed
    have actual := projectedLaw t timeMem
    rw [finiteStateTransverseProjectedGenerator,
      generatorFixed] at actual
    exact actual
  have trajectorySupported :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        ∀ wave, wave ∉ modes → trajectory t wave = 0 := by
    intro t timeMem wave waveNotMem
    exact
      finiteTransverseSupportProjection_fixed_support
        (fixedForward t timeMem).symm waveNotMem
  have trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        ∀ wave,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0 := by
    intro t timeMem wave
    exact
      finiteTransverseSupportProjection_fixed_transverse
        (fixedForward t timeMem).symm wave
  let reflection :=
    complexFourierRealityReflection modes
  have initialReflectionFixed :
      reflection initialState = initialState := by
    exact
      complexFourierRealityReflection_fixed_of_physical
        modes initialState supported reality
  have sameReflectionInitial :
      trajectory 0 = (reflection ∘ trajectory) 0 := by
    calc
      trajectory 0 = initialState := trajectoryInitial
      _ = reflection initialState := initialReflectionFixed.symm
      _ = (reflection ∘ trajectory) 0 := by
        rw [Function.comp_apply, trajectoryInitial]
  have reflectedLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt (reflection ∘ trajectory)
          (finiteStateVorticityGenerator modes ν
            ((reflection ∘ trajectory) t)) t := by
    intro t timeMem
    have reflected :=
      reflection.hasFDerivAt.comp_hasDerivAt
        t (actualLaw t timeMem)
    rw [finiteStateVorticityGenerator_realityReflection_commutes
      (fun {wave} waveMem => negClosed wave waveMem) ν] at reflected
    simpa [Function.comp_def, reflection] using reflected
  have reflectedContinuous :
      ContinuousOn (reflection ∘ trajectory)
        (Icc (0 : ℝ) uniformTime) :=
    HasDerivAt.continuousOn reflectedLaw
  let comparisonRadius : ℝ :=
    max (outerRadius : ℝ)
      (‖reflection‖ * (outerRadius : ℝ))
  obtain
      ⟨comparisonBound, comparisonLipschitz,
        comparisonNormLe, comparisonLipschitzOn⟩ :=
    exists_finiteStateVorticityGenerator_bounds
      modes ν comparisonRadius
  have trajectoryComparisonMem :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        trajectory t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) comparisonRadius := by
    intro t timeMem
    rw [Metric.mem_closedBall, dist_zero_right]
    have outerMem := trajectoryOuterMem t timeMem
    rw [Metric.mem_closedBall, dist_zero_right] at outerMem
    exact outerMem.trans (le_max_left _ _)
  have reflectedComparisonMem :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        (reflection ∘ trajectory) t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) comparisonRadius := by
    intro t timeMem
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖(reflection ∘ trajectory) t‖ =
          ‖reflection (trajectory t)‖ := rfl
      _ ≤ ‖reflection‖ * ‖trajectory t‖ :=
        reflection.le_opNorm _
      _ ≤ ‖reflection‖ * (outerRadius : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · have outerMem := trajectoryOuterMem t timeMem
          rwa [Metric.mem_closedBall, dist_zero_right] at outerMem
        · exact norm_nonneg reflection
      _ ≤ comparisonRadius :=
        le_max_right _ _
  have realityFixed :
      EqOn trajectory (reflection ∘ trajectory)
        (Icc (0 : ℝ) uniformTime) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ =>
        finiteStateVorticityGenerator modes ν)
      (s := fun _ =>
        Metric.closedBall
          (0 : ComplexVorticityHilbertState)
          comparisonRadius)
      (K := comparisonLipschitz)
    · intro t timeMem
      exact comparisonLipschitzOn
    · exact HasDerivAt.continuousOn actualLaw
    · intro t timeMem
      exact
        (actualLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact
        trajectoryComparisonMem t
          (mem_Icc_of_Ico timeMem)
    · exact reflectedContinuous
    · intro t timeMem
      exact
        (reflectedLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact
        reflectedComparisonMem t
          (mem_Icc_of_Ico timeMem)
    · exact sameReflectionInitial
  refine ⟨trajectory, trajectoryInitial, ?_⟩
  intro t timeMem
  refine
    ⟨actualLaw t timeMem,
      trajectorySupported t timeMem,
      trajectoryTransverse t timeMem, ?_⟩
  apply finiteStateFourierReality_of_reflection_fixed
      (fun waveMem => negClosed _ waveMem)
      (trajectorySupported t timeMem)
  exact (realityFixed timeMem).symm

/-- The same physical restart with the local lifetime exposed as the exact
Picard radius-gap/field-bound time

```text
T = 1 / (4 (fieldBound + 1)).
```

The field bound is generated from the fixed inventory, viscosity, and
endpoint carrier ball.  It is an output, not a cutoff-uniform premise. -/
theorem exists_quantified_uniform_finitePhysicalTrajectory
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (innerRadius : NNReal) :
    ∃ fieldBound : NNReal,
      fieldBound =
          canonicalProjectedGeneratorFieldBound
            modes ν (innerRadius + 1) ∧
        ∃ uniformTime > (0 : ℝ),
          uniformTime =
              1 / (4 * ((fieldBound : ℝ) + 1)) ∧
            ∀ initialState : ComplexVorticityHilbertState,
            initialState ∈
                Metric.closedBall
                  (0 : ComplexVorticityHilbertState) innerRadius →
              (∀ wave, wave ∉ modes → initialState wave = 0) →
              (∀ wave ∈ modes,
                complexWavevector wave ⬝ᵥ initialState wave = 0) →
              FiniteStateFourierReality initialState →
              ∃ trajectory : ℝ → ComplexVorticityHilbertState,
                trajectory 0 = initialState ∧
                  ∀ t ∈ Icc (0 : ℝ) uniformTime,
                    HasDerivAt trajectory
                        (finiteStateVorticityGenerator
                          modes ν (trajectory t)) t ∧
                      (∀ wave,
                        wave ∉ modes → trajectory t wave = 0) ∧
                      (∀ wave,
                        complexWavevector wave ⬝ᵥ
                          trajectory t wave = 0) ∧
                      FiniteStateFourierReality (trajectory t) ∧
                      ‖finiteStateVorticityGenerator
                          modes ν (trajectory t)‖ ≤
                        fieldBound := by
  let outerRadius : NNReal := innerRadius + 1
  have radiusRoom : innerRadius < outerRadius := by
    dsimp [outerRadius]
    exact lt_add_of_pos_right innerRadius (by norm_num)
  obtain
      ⟨ε, εPos, fieldBound, lipschitzBound,
        fieldBoundEq, εEq, uniformPicard⟩ :=
    exists_quantifiedUniformPicard_finiteStateTransverseProjectedGenerator
      modes ν innerRadius outerRadius radiusRoom
  let uniformTime : ℝ := ε / 2
  have uniformTimePos : 0 < uniformTime := by
    dsimp [uniformTime]
    linarith
  have uniformTimeEq :
      uniformTime =
        1 / (4 * ((fieldBound : ℝ) + 1)) := by
    dsimp [uniformTime]
    rw [εEq]
    simp [outerRadius]
    ring
  refine
    ⟨fieldBound,
      by simpa [outerRadius] using fieldBoundEq,
      uniformTime, uniformTimePos, uniformTimeEq, ?_⟩
  intro initialState initialMem supported transverse reality
  have initialProjectionFixed :
      finiteTransverseSupportProjection modes initialState =
        initialState :=
    finiteTransverseSupportProjection_fixed_of_physical
      modes zeroNotMem initialState supported transverse
  let picard :=
    uniformPicard 0
  obtain
      ⟨trajectory, trajectoryInitial,
        picardProperties⟩ :=
    exists_picard_path_hasDerivWithinAt_mem_closedBall
      picard initialMem
  have timeInPicardInterior :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        t ∈ Ioo (-ε) ε := by
    intro t timeMem
    constructor
    · linarith [timeMem.1]
    · dsimp [uniformTime] at timeMem
      linarith [timeMem.2]
  have projectedLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt trajectory
          (finiteStateTransverseProjectedGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    have interior := timeInPicardInterior t timeMem
    have picardInterior :
        t ∈ Ioo (0 - ε) (0 + ε) := by
      simpa using interior
    exact
      (picardProperties t
        (Ioo_subset_Icc_self picardInterior)).1
        |>.hasDerivAt
          (Icc_mem_nhds picardInterior.1 picardInterior.2)
  have trajectoryOuterMem :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        trajectory t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) outerRadius := by
    intro t timeMem
    have picardInterior :
        t ∈ Ioo (0 - ε) (0 + ε) := by
      simpa using timeInPicardInterior t timeMem
    exact
      (picardProperties t
        (Ioo_subset_Icc_self
          picardInterior)).2
  have projectedPathLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt
          ((finiteTransverseSupportProjection modes) ∘ trajectory)
          (finiteStateTransverseProjectedGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    have projected :=
      (finiteTransverseSupportProjection modes).hasFDerivAt
        |>.comp_hasDerivAt t (projectedLaw t timeMem)
    simpa [finiteStateTransverseProjectedGenerator,
      finiteTransverseSupportProjection_idempotent] using projected
  have trajectoryContinuous :
      ContinuousOn trajectory (Icc (0 : ℝ) uniformTime) :=
    HasDerivAt.continuousOn projectedLaw
  have projectedPathContinuous :
      ContinuousOn
        ((finiteTransverseSupportProjection modes) ∘ trajectory)
        (Icc (0 : ℝ) uniformTime) :=
    HasDerivAt.continuousOn projectedPathLaw
  have sameProjectionInitial :
      trajectory 0 =
        finiteTransverseSupportProjection modes (trajectory 0) := by
    rw [trajectoryInitial, initialProjectionFixed]
  have fixedForward :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        trajectory t =
          finiteTransverseSupportProjection modes (trajectory t) := by
    apply eq_of_has_deriv_right_eq
      (f' := fun t =>
        finiteStateTransverseProjectedGenerator
          modes ν (trajectory t))
    · intro t timeMem
      exact
        (projectedLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact
        (projectedPathLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · exact trajectoryContinuous
    · exact projectedPathContinuous
    · exact sameProjectionInitial
  have actualLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt trajectory
          (finiteStateVorticityGenerator
            modes ν (trajectory t)) t := by
    intro t timeMem
    have fixed :
        finiteTransverseSupportProjection modes (trajectory t) =
          trajectory t :=
      (fixedForward t timeMem).symm
    have generatorFixed :=
      finiteTransverseSupportProjection_generator_of_fixed
        zeroNotMem ν fixed
    have actual := projectedLaw t timeMem
    rw [finiteStateTransverseProjectedGenerator,
      generatorFixed] at actual
    exact actual
  have trajectorySupported :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        ∀ wave, wave ∉ modes → trajectory t wave = 0 := by
    intro t timeMem wave waveNotMem
    exact
      finiteTransverseSupportProjection_fixed_support
        (fixedForward t timeMem).symm waveNotMem
  have trajectoryTransverse :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        ∀ wave,
          complexWavevector wave ⬝ᵥ trajectory t wave = 0 := by
    intro t timeMem wave
    exact
      finiteTransverseSupportProjection_fixed_transverse
        (fixedForward t timeMem).symm wave
  have trajectoryGeneratorNormLe :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        ‖finiteStateVorticityGenerator
            modes ν (trajectory t)‖ ≤
          fieldBound := by
    intro t timeMem
    have picardInterior :
        t ∈ Ioo (0 - ε) (0 + ε) := by
      simpa using timeInPicardInterior t timeMem
    have projectedBound :=
      picard.norm_le t
        (Ioo_subset_Icc_self picardInterior)
        (trajectory t)
        (trajectoryOuterMem t timeMem)
    have fixed :
        finiteTransverseSupportProjection modes (trajectory t) =
          trajectory t :=
      (fixedForward t timeMem).symm
    have generatorFixed :=
      finiteTransverseSupportProjection_generator_of_fixed
        zeroNotMem ν fixed
    rw [finiteStateTransverseProjectedGenerator,
      generatorFixed] at projectedBound
    exact projectedBound
  let reflection :=
    complexFourierRealityReflection modes
  have initialReflectionFixed :
      reflection initialState = initialState := by
    exact
      complexFourierRealityReflection_fixed_of_physical
        modes initialState supported reality
  have sameReflectionInitial :
      trajectory 0 = (reflection ∘ trajectory) 0 := by
    calc
      trajectory 0 = initialState := trajectoryInitial
      _ = reflection initialState := initialReflectionFixed.symm
      _ = (reflection ∘ trajectory) 0 := by
        rw [Function.comp_apply, trajectoryInitial]
  have reflectedLaw :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        HasDerivAt (reflection ∘ trajectory)
          (finiteStateVorticityGenerator modes ν
            ((reflection ∘ trajectory) t)) t := by
    intro t timeMem
    have reflected :=
      reflection.hasFDerivAt.comp_hasDerivAt
        t (actualLaw t timeMem)
    rw [finiteStateVorticityGenerator_realityReflection_commutes
      (fun {wave} waveMem => negClosed wave waveMem) ν] at reflected
    simpa [Function.comp_def, reflection] using reflected
  have reflectedContinuous :
      ContinuousOn (reflection ∘ trajectory)
        (Icc (0 : ℝ) uniformTime) :=
    HasDerivAt.continuousOn reflectedLaw
  let comparisonRadius : ℝ :=
    max (outerRadius : ℝ)
      (‖reflection‖ * (outerRadius : ℝ))
  obtain
      ⟨comparisonBound, comparisonLipschitz,
        comparisonNormLe, comparisonLipschitzOn⟩ :=
    exists_finiteStateVorticityGenerator_bounds
      modes ν comparisonRadius
  have trajectoryComparisonMem :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        trajectory t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState)
            comparisonRadius := by
    intro t timeMem
    rw [Metric.mem_closedBall, dist_zero_right]
    have outerMem := trajectoryOuterMem t timeMem
    rw [Metric.mem_closedBall, dist_zero_right] at outerMem
    exact outerMem.trans (le_max_left _ _)
  have reflectedComparisonMem :
      ∀ t ∈ Icc (0 : ℝ) uniformTime,
        (reflection ∘ trajectory) t ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState)
            comparisonRadius := by
    intro t timeMem
    rw [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖(reflection ∘ trajectory) t‖ =
          ‖reflection (trajectory t)‖ := rfl
      _ ≤ ‖reflection‖ * ‖trajectory t‖ :=
        reflection.le_opNorm _
      _ ≤ ‖reflection‖ * (outerRadius : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · have outerMem := trajectoryOuterMem t timeMem
          rwa [Metric.mem_closedBall, dist_zero_right] at outerMem
        · exact norm_nonneg reflection
      _ ≤ comparisonRadius :=
        le_max_right _ _
  have realityFixed :
      EqOn trajectory (reflection ∘ trajectory)
        (Icc (0 : ℝ) uniformTime) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ =>
        finiteStateVorticityGenerator modes ν)
      (s := fun _ =>
        Metric.closedBall
          (0 : ComplexVorticityHilbertState)
          comparisonRadius)
      (K := comparisonLipschitz)
    · intro t timeMem
      exact comparisonLipschitzOn
    · exact HasDerivAt.continuousOn actualLaw
    · intro t timeMem
      exact
        (actualLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact
        trajectoryComparisonMem t
          (mem_Icc_of_Ico timeMem)
    · exact reflectedContinuous
    · intro t timeMem
      exact
        (reflectedLaw t
          (mem_Icc_of_Ico timeMem)).hasDerivWithinAt
    · intro t timeMem
      exact
        reflectedComparisonMem t
          (mem_Icc_of_Ico timeMem)
    · exact sameReflectionInitial
  refine ⟨trajectory, trajectoryInitial, ?_⟩
  intro t timeMem
  refine
    ⟨actualLaw t timeMem,
      trajectorySupported t timeMem,
      trajectoryTransverse t timeMem, ?_,
      trajectoryGeneratorNormLe t timeMem⟩
  · apply finiteStateFourierReality_of_reflection_fixed
        (fun waveMem => negClosed _ waveMem)
        (trajectorySupported t timeMem)
    exact (realityFixed timeMem).symm

/-! ## Exact physical concatenation -/

private theorem hasDerivAt_comp_sub_const
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (trajectory : ℝ → E)
    (joinTime time : ℝ)
    (tangent : E)
    (derivative :
      HasDerivAt trajectory tangent (time - joinTime)) :
    HasDerivAt
      (fun shiftedTime => trajectory (shiftedTime - joinTime))
      tangent time := by
  have shiftDerivative :
      HasDerivAt
        (fun shiftedTime : ℝ => shiftedTime - joinTime)
        1 time := by
    simpa only [id_eq] using
      (hasDerivAt_id time).sub_const joinTime
  have composed :=
    derivative.hasFDerivAt.comp_hasDerivAt time shiftDerivative
  simpa only [Function.comp_def,
    ContinuousLinearMap.toSpanSingleton_apply_one] using composed

private theorem endpointSplice_hasDerivAt_join
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (joinTime : ℝ)
    (prior restart : ℝ → E)
    (tangent : E)
    (sameValue : restart 0 = prior joinTime)
    (priorDerivative :
      HasDerivAt prior tangent joinTime)
    (restartDerivative :
      HasDerivAt restart tangent 0) :
    HasDerivAt
      (endpointSplice joinTime prior restart)
      tangent joinTime := by
  have priorWithin :
      HasDerivWithinAt
        (endpointSplice joinTime prior restart)
        tangent (Iic joinTime) joinTime := by
    apply priorDerivative.hasDerivWithinAt.congr
    · intro time timeMem
      exact endpointSplice_of_le
        joinTime prior restart time timeMem
    · exact endpointSplice_of_le
        joinTime prior restart joinTime le_rfl
  have shiftedRestartDerivative :
      HasDerivAt
        (fun time => restart (time - joinTime))
        tangent joinTime := by
    have atJoin : joinTime - joinTime = 0 :=
      sub_self joinTime
    rw [← atJoin] at restartDerivative
    exact hasDerivAt_comp_sub_const
      restart joinTime joinTime tangent restartDerivative
  have restartWithin :
      HasDerivWithinAt
        (endpointSplice joinTime prior restart)
        tangent (Ici joinTime) joinTime := by
    apply shiftedRestartDerivative.hasDerivWithinAt.congr
    · intro time timeMem
      by_cases timeEq : time = joinTime
      · subst time
        simp [endpointSplice, sameValue]
      · have joinLt : joinTime < time :=
          lt_of_le_of_ne timeMem (Ne.symm timeEq)
        exact endpointSplice_of_lt
          joinTime prior restart time joinLt
    · simp [endpointSplice, sameValue]
  have joined := priorWithin.union restartWithin
  rw [Iic_union_Ici, hasDerivWithinAt_univ] at joined
  exact joined

theorem finitePhysicalTrajectory_splice
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (prior restart : ℝ → ComplexVorticityHilbertState)
    (joinTime additionalTime : ℝ)
    (joinTimeNonneg : 0 ≤ joinTime)
    (additionalTimePos : 0 < additionalTime)
    (priorProperties :
      ∀ t ∈ Icc (0 : ℝ) joinTime,
        HasDerivAt prior
            (finiteStateVorticityGenerator
              modes ν (prior t)) t ∧
          (∀ wave, wave ∉ modes → prior t wave = 0) ∧
          (∀ wave,
            complexWavevector wave ⬝ᵥ prior t wave = 0) ∧
          FiniteStateFourierReality (prior t))
    (sameValue : restart 0 = prior joinTime)
    (restartProperties :
      ∀ t ∈ Icc (0 : ℝ) additionalTime,
        HasDerivAt restart
            (finiteStateVorticityGenerator
              modes ν (restart t)) t ∧
          (∀ wave, wave ∉ modes → restart t wave = 0) ∧
          (∀ wave,
            complexWavevector wave ⬝ᵥ restart t wave = 0) ∧
          FiniteStateFourierReality (restart t)) :
    ∃ extended : ℝ → ComplexVorticityHilbertState,
      (∀ t ∈ Icc (0 : ℝ) joinTime,
        extended t = prior t) ∧
        ∀ t ∈ Icc (0 : ℝ) (joinTime + additionalTime),
          HasDerivAt extended
              (finiteStateVorticityGenerator
                modes ν (extended t)) t ∧
            (∀ wave, wave ∉ modes → extended t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ extended t wave = 0) ∧
            FiniteStateFourierReality (extended t) := by
  let extended : ℝ → ComplexVorticityHilbertState :=
    endpointSplice joinTime prior restart
  have joinMem : joinTime ∈ Icc (0 : ℝ) joinTime :=
    ⟨joinTimeNonneg, le_rfl⟩
  have restartZeroMem :
      (0 : ℝ) ∈ Icc (0 : ℝ) additionalTime :=
    ⟨le_rfl, additionalTimePos.le⟩
  have priorDerivativeAtJoin :
      HasDerivAt prior
        (finiteStateVorticityGenerator
          modes ν (prior joinTime)) joinTime :=
    (priorProperties joinTime joinMem).1
  have restartDerivativeAtJoin :
      HasDerivAt restart
        (finiteStateVorticityGenerator
          modes ν (prior joinTime)) 0 := by
    simpa only [sameValue] using
      (restartProperties 0 restartZeroMem).1
  have extendedDerivativeAtJoin :
      HasDerivAt extended
        (finiteStateVorticityGenerator
          modes ν (extended joinTime)) joinTime := by
    have joined :=
      endpointSplice_hasDerivAt_join
        joinTime prior restart
        (finiteStateVorticityGenerator
          modes ν (prior joinTime))
        sameValue priorDerivativeAtJoin
        restartDerivativeAtJoin
    simpa [extended, endpointSplice] using joined
  have extendedDerivative :
      ∀ t ∈ Icc (0 : ℝ) (joinTime + additionalTime),
        HasDerivAt extended
          (finiteStateVorticityGenerator
            modes ν (extended t)) t := by
    intro t timeMem
    rcases lt_trichotomy t joinTime with timeLt | timeEq | joinLt
    · have priorMem : t ∈ Icc (0 : ℝ) joinTime :=
        ⟨timeMem.1, timeLt.le⟩
      have eventuallyPrior :
          extended =ᶠ[𝓝 t] prior := by
        filter_upwards [Iio_mem_nhds timeLt] with time nearbyLt
        exact endpointSplice_of_le
          joinTime prior restart time nearbyLt.le
      have derivative :=
        (priorProperties t priorMem).1
          |>.congr_of_eventuallyEq eventuallyPrior
      simpa [extended, endpointSplice, timeLt.le] using derivative
    · subst t
      exact extendedDerivativeAtJoin
    · have shiftedMem :
          t - joinTime ∈ Icc (0 : ℝ) additionalTime := by
        constructor <;> linarith [timeMem.2]
      have shiftedDerivative :=
        hasDerivAt_comp_sub_const
          restart joinTime t
          (finiteStateVorticityGenerator
            modes ν (restart (t - joinTime)))
          (restartProperties
            (t - joinTime) shiftedMem).1
      have eventuallyRestart :
          extended =ᶠ[𝓝 t]
            (fun time => restart (time - joinTime)) := by
        filter_upwards [Ioi_mem_nhds joinLt] with time nearbyLt
        exact endpointSplice_of_lt
          joinTime prior restart time nearbyLt
      have derivative :=
        shiftedDerivative.congr_of_eventuallyEq
          eventuallyRestart
      simpa [extended, endpointSplice,
        not_le.mpr joinLt] using derivative
  refine ⟨extended, ?_, ?_⟩
  · intro t timeMem
    exact endpointSplice_of_le
      joinTime prior restart t timeMem.2
  · intro t timeMem
    refine ⟨extendedDerivative t timeMem, ?_⟩
    by_cases timeLe : t ≤ joinTime
    · have priorMem : t ∈ Icc (0 : ℝ) joinTime :=
        ⟨timeMem.1, timeLe⟩
      have priorData := priorProperties t priorMem
      have stateEq : extended t = prior t :=
        endpointSplice_of_le
          joinTime prior restart t timeLe
      refine ⟨?_, ?_, ?_⟩
      · intro wave waveNotMem
        rw [stateEq]
        exact priorData.2.1 wave waveNotMem
      · intro wave
        rw [stateEq]
        exact priorData.2.2.1 wave
      · rw [stateEq]
        exact priorData.2.2.2
    · have joinLt : joinTime < t :=
        lt_of_not_ge timeLe
      have shiftedMem :
          t - joinTime ∈ Icc (0 : ℝ) additionalTime := by
        constructor <;> linarith [timeMem.2]
      have restartData :=
        restartProperties (t - joinTime) shiftedMem
      have stateEq :
          extended t = restart (t - joinTime) :=
        endpointSplice_of_lt
          joinTime prior restart t joinLt
      refine ⟨?_, ?_, ?_⟩
      · intro wave waveNotMem
        rw [stateEq]
        exact restartData.2.1 wave waveNotMem
      · intro wave
        rw [stateEq]
        exact restartData.2.2.1 wave
      · rw [stateEq]
        exact restartData.2.2.2

/-! ## Arbitrary requested finite time -/

/-- Every physical fixed-mode initial state below the critical enstrophy
threshold generates an actual physical Galerkin trajectory on any requested
finite positive interval.

The generated uniform step may depend on `modes`, viscosity, and the initial
critical ball.  It is independent of the requested target time and of all
subsequent restart states. -/
theorem exists_finitePhysicalTrajectory_on_Icc_of_criticalSmall
    (modes : Finset IntegerWavevector)
    (zeroNotMem : 0 ∉ modes)
    (negClosed :
      ∀ wave, wave ∈ modes → waveNeg wave ∈ modes)
    (ν : ℝ)
    (νPos : 0 < ν)
    (initialState : ComplexVorticityHilbertState)
    (supported :
      ∀ wave, wave ∉ modes → initialState wave = 0)
    (transverse :
      ∀ wave ∈ modes,
        complexWavevector wave ⬝ᵥ initialState wave = 0)
    (reality : FiniteStateFourierReality initialState)
    (initialSmall :
      criticalEnstrophyLatticeConstant *
          finiteStateVorticityCoefficientEnstrophy
            modes initialState ≤
        ν ^ 2 * (2 * Real.pi) ^ 2)
    (targetTime : ℝ)
    (targetTimePos : 0 < targetTime) :
    ∃ trajectory : ℝ → ComplexVorticityHilbertState,
      trajectory 0 = initialState ∧
        ∀ t ∈ Icc (0 : ℝ) targetTime,
          HasDerivAt trajectory
              (finiteStateVorticityGenerator
                modes ν (trajectory t)) t ∧
            (∀ wave, wave ∉ modes → trajectory t wave = 0) ∧
            (∀ wave,
              complexWavevector wave ⬝ᵥ trajectory t wave = 0) ∧
            FiniteStateFourierReality (trajectory t) := by
  let initialEnstrophy : ℝ :=
    finiteStateVorticityCoefficientEnstrophy
      modes initialState
  let innerRadius : NNReal :=
    ⟨Real.sqrt initialEnstrophy, Real.sqrt_nonneg _⟩
  have initialMem :
      initialState ∈
        Metric.closedBall
          (0 : ComplexVorticityHilbertState) innerRadius := by
    rw [Metric.mem_closedBall, dist_zero_right]
    apply Real.le_sqrt_of_sq_le
    exact
      complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
        modes initialState supported
  obtain
      ⟨uniformTime, uniformTimePos,
        uniformLocal⟩ :=
    exists_uniform_finitePhysicalTrajectory
      modes zeroNotMem negClosed ν innerRadius
  have generatedPrefixes :
      ∀ step : ℕ,
        ∃ trajectory : ℝ → ComplexVorticityHilbertState,
          trajectory 0 = initialState ∧
            ∀ t ∈ Icc (0 : ℝ)
                (((step : ℝ) + 1) * uniformTime),
              HasDerivAt trajectory
                  (finiteStateVorticityGenerator
                    modes ν (trajectory t)) t ∧
                (∀ wave, wave ∉ modes → trajectory t wave = 0) ∧
                (∀ wave,
                  complexWavevector wave ⬝ᵥ
                    trajectory t wave = 0) ∧
                FiniteStateFourierReality (trajectory t) := by
    intro step
    induction step with
    | zero =>
        obtain
            ⟨trajectory, trajectoryInitial,
              physicalProperties⟩ :=
          uniformLocal initialState initialMem
            supported transverse reality
        refine ⟨trajectory, trajectoryInitial, ?_⟩
        simpa using physicalProperties
    | succ step inductionHypothesis =>
        obtain
            ⟨trajectory, trajectoryInitial,
              physicalProperties⟩ :=
          inductionHypothesis
        let joinTime : ℝ :=
          (((step : ℝ) + 1) * uniformTime)
        have joinTimeNonneg : 0 ≤ joinTime := by
          dsimp [joinTime]
          positivity
        have joinMem :
            joinTime ∈ Icc (0 : ℝ) joinTime :=
          ⟨joinTimeNonneg, le_rfl⟩
        have endpointProperties :=
          physicalProperties joinTime (by
            simpa [joinTime] using joinMem)
        have pathInitialSmall :
            criticalEnstrophyLatticeConstant *
                finiteStateVorticityCoefficientEnstrophy
                  modes (trajectory 0) ≤
              ν ^ 2 * (2 * Real.pi) ^ 2 := by
          simpa only [trajectoryInitial] using initialSmall
        have barrier :=
          finiteStateVorticityHalfEnstrophy_le_initial_of_criticalSmall
            modes negClosed ν νPos trajectory 0 joinTime
            (fun t timeMem =>
              (physicalProperties t (by
                simpa [joinTime] using timeMem)).1)
            (fun t timeMem =>
              (physicalProperties t (by
                simpa [joinTime] using timeMem)).2.2.2)
            (fun t timeMem wave waveMem =>
              (physicalProperties t (by
                simpa [joinTime] using timeMem)).2.2.1 wave)
            pathInitialSmall
        have halfEnstrophyLe :=
          (barrier joinTime joinMem).1
        have endpointEnstrophyLe :
            finiteStateVorticityCoefficientEnstrophy
                modes (trajectory joinTime) ≤
              initialEnstrophy := by
          dsimp [initialEnstrophy]
          rw [trajectoryInitial] at halfEnstrophyLe
          unfold finiteStateVorticityHalfEnstrophy at halfEnstrophyLe
          linarith
        have endpointAmbientSqLe :=
          complexVorticityHilbertState_norm_sq_le_coefficientEnstrophy
            modes (trajectory joinTime)
            endpointProperties.2.1
        have endpointMem :
            trajectory joinTime ∈
              Metric.closedBall
                (0 : ComplexVorticityHilbertState) innerRadius := by
          rw [Metric.mem_closedBall, dist_zero_right]
          change ‖trajectory joinTime‖ ≤
            Real.sqrt initialEnstrophy
          exact
            Real.le_sqrt_of_sq_le
              (endpointAmbientSqLe.trans endpointEnstrophyLe)
        obtain
            ⟨restart, restartInitial,
              restartProperties⟩ :=
          uniformLocal (trajectory joinTime) endpointMem
            endpointProperties.2.1
            (fun wave waveMem =>
              endpointProperties.2.2.1 wave)
            endpointProperties.2.2.2
        obtain
            ⟨extended, extendedEqPrior,
              extendedProperties⟩ :=
          finitePhysicalTrajectory_splice
            modes ν trajectory restart
            joinTime uniformTime joinTimeNonneg
            uniformTimePos
            (fun t timeMem =>
              physicalProperties t (by
                simpa [joinTime] using timeMem))
            restartInitial restartProperties
        have zeroJoinMem :
            (0 : ℝ) ∈ Icc (0 : ℝ) joinTime :=
          ⟨le_rfl, joinTimeNonneg⟩
        refine ⟨extended, ?_, ?_⟩
        · calc
            extended 0 = trajectory 0 :=
              extendedEqPrior 0 zeroJoinMem
            _ = initialState := trajectoryInitial
        · intro t timeMem
          apply extendedProperties t
          have nextHorizon :
              (((step.succ : ℝ) + 1) * uniformTime) =
                joinTime + uniformTime := by
            dsimp [joinTime]
            push_cast
            ring
          rwa [nextHorizon] at timeMem
  obtain ⟨step, stepLarge⟩ :=
    exists_nat_gt (targetTime / uniformTime)
  obtain
      ⟨trajectory, trajectoryInitial,
        physicalProperties⟩ :=
    generatedPrefixes step
  have targetBeforeStep :
      targetTime <
        (step : ℝ) * uniformTime := by
    exact (div_lt_iff₀ uniformTimePos).mp stepLarge
  have targetLeHorizon :
      targetTime ≤
        ((step : ℝ) + 1) * uniformTime := by
    have stepPositive : 0 < (step : ℝ) :=
      lt_trans
        (div_pos targetTimePos uniformTimePos)
        stepLarge
    have stepLe : (step : ℝ) ≤ (step : ℝ) + 1 := by
      linarith [stepPositive]
    have scaledLe :
        (step : ℝ) * uniformTime ≤
          ((step : ℝ) + 1) * uniformTime :=
      mul_le_mul_of_nonneg_right stepLe uniformTimePos.le
    exact (le_of_lt targetBeforeStep).trans scaledLe
  refine ⟨trajectory, trajectoryInitial, ?_⟩
  intro t timeMem
  exact
    physicalProperties t
      ⟨timeMem.1, timeMem.2.trans targetLeHorizon⟩

end

end ThreeDimensionalVorticityCoefficientFiniteGalerkinCommonTimeExistence
end NavierStokes
end SaturationMonoid
