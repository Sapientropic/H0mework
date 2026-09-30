import Mathlib.Analysis.ODE.ExistUnique
import H0mework.NavierStokes.Galerkin.CriticalEnstrophyBarrier

/-!
# Finite-modal Picard bounds for the three-dimensional Galerkin generator

For a fixed finite Fourier inventory, the ambient `lp 2` Galerkin generator
factors through the genuinely finite-dimensional carrier

```text
(k : {k // k ∈ modes}) → ℂ³.
```

The restriction and extension maps below are actual continuous linear maps.
The finite generator is `C¹`, so compactness of a finite-dimensional closed
ball generates both a field-norm bound and a Lipschitz constant.  Exact
factorization then transports those bounds back to the ambient carrier.

All constants are conclusions.  They may depend on the fixed inventory,
viscosity, and radius; no maximum frequency, mode count, pre-supplied bound,
target lifespan, or continuation witness occurs in a theorem mouth.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds

open scoped BigOperators ENNReal

open Set ODE
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory

noncomputable section

/-! ## The finite carrier and its exact ambient retraction -/

/-- Exact finite-dimensional coefficient carrier owned by `modes`. -/
abbrev FiniteModeVorticityCarrier
    (modes : Finset IntegerWavevector) :=
  (wave : {wave // wave ∈ modes}) → ComplexCoordinateVector

/-- Read precisely the coefficient rows owned by `modes`. -/
def finiteModeRestriction
    (modes : Finset IntegerWavevector) :
    ComplexVorticityHilbertState →L[ℝ]
      FiniteModeVorticityCarrier modes :=
  ContinuousLinearMap.pi fun wave =>
    lp.evalCLM ℝ
      (fun _ : IntegerWavevector => ComplexCoordinateVector)
      2 wave.1

/-- Extend a finite modal table by zero to the ambient `lp 2` carrier. -/
def finiteModeExtension
    (modes : Finset IntegerWavevector) :
    FiniteModeVorticityCarrier modes →L[ℝ]
      ComplexVorticityHilbertState where
  toFun coefficient :=
    ∑ wave : {wave // wave ∈ modes},
      lp.single 2 wave.1 (coefficient wave)
  map_add' left right := by
    simp_rw [Pi.add_apply, lp.single_add]
    exact Finset.sum_add_distrib
  map_smul' scalar coefficient := by
    simp_rw [Pi.smul_apply, lp.single_smul]
    exact Finset.smul_sum.symm
  cont := by
    apply continuous_finsetSum
    intro wave waveMem
    exact
      (lp.singleContinuousLinearMap ℝ
        (fun _ : IntegerWavevector => ComplexCoordinateVector)
        2 wave.1).continuous.comp
          (continuous_apply wave)

@[simp] theorem finiteModeRestriction_apply
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState)
    (wave : {wave // wave ∈ modes}) :
    finiteModeRestriction modes state wave = state wave.1 :=
  rfl

@[simp] theorem finiteModeExtension_apply
    (modes : Finset IntegerWavevector)
    (coefficient : FiniteModeVorticityCarrier modes)
    (wave : IntegerWavevector) :
    finiteModeExtension modes coefficient wave =
      if waveMem : wave ∈ modes
      then coefficient ⟨wave, waveMem⟩
      else 0 := by
  classical
  change
    ((∑ index : {wave // wave ∈ modes},
        lp.single 2 index.1 (coefficient index)) :
        ComplexVorticityHilbertState) wave = _
  rw [lp.coeFn_sum, Fintype.sum_apply]
  by_cases waveMem : wave ∈ modes
  · rw [dif_pos waveMem]
    have condition :
        ∀ index : {wave // wave ∈ modes},
          (wave = index.1 ↔
            (⟨wave, waveMem⟩ :
              {wave // wave ∈ modes}) = index) := by
      intro index
      constructor
      · exact fun equality => Subtype.ext equality
      · exact fun equality =>
          congrArg Subtype.val equality
    simp only [lp.single_apply, Pi.single_apply]
    simp_rw [condition]
    exact Fintype.sum_ite_eq _ _
  · rw [dif_neg waveMem]
    apply Fintype.sum_eq_zero
    intro index
    rw [lp.single_apply, Pi.single_apply, if_neg]
    intro equality
    apply waveMem
    rw [equality]
    exact index.2

theorem finiteModeRestriction_norm_le
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    ‖finiteModeRestriction modes state‖ ≤ ‖state‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg state)]
  intro wave
  exact
    lp.norm_apply_le_norm (by norm_num) state wave.1

theorem finiteModeRestriction_lipschitz :
    LipschitzWith 1 (finiteModeRestriction modes) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro left right
  rw [← map_sub]
  simpa using
    finiteModeRestriction_norm_le modes (left - right)

@[simp] theorem finiteModeRestriction_extension
    (modes : Finset IntegerWavevector)
    (coefficient : FiniteModeVorticityCarrier modes) :
    finiteModeRestriction modes
        (finiteModeExtension modes coefficient) =
      coefficient := by
  funext wave
  simp [wave.2]

theorem finiteModeExtension_restriction
    (modes : Finset IntegerWavevector)
    (state : ComplexVorticityHilbertState) :
    finiteModeExtension modes
        (finiteModeRestriction modes state) =
      complexSharpSupportProjection modes state := by
  apply lp.ext
  funext wave
  simp [complexSharpSupportProjection_apply]

/-! ## Exact finite-field factorization -/

/-- The complete Galerkin generator only reads the rows in its own finite
inventory. -/
theorem finiteStateVorticityGenerator_sharpProjection
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    finiteStateVorticityGenerator modes ν
        (complexSharpSupportProjection modes state) =
      finiteStateVorticityGenerator modes ν state := by
  apply lp.ext
  funext output
  by_cases outputMem : output ∈ modes
  · rw [finiteStateVorticityGenerator_apply,
      if_pos outputMem,
      finiteStateVorticityGenerator_apply,
      if_pos outputMem,
      finiteStateVorticityNonlinearCoefficientAt_projection_of_subset
        (smaller := modes) (larger := modes) (by rfl),
      complexSharpSupportProjection_apply,
      if_pos outputMem]
  · simp [finiteStateVorticityGenerator_apply, outputMem]

/-- Every generated tangent is already sharply supported on `modes`. -/
theorem complexSharpSupportProjection_generator
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    complexSharpSupportProjection modes
        (finiteStateVorticityGenerator modes ν state) =
      finiteStateVorticityGenerator modes ν state := by
  apply lp.ext
  funext output
  by_cases outputMem : output ∈ modes <;>
    simp [complexSharpSupportProjection_apply,
      finiteStateVorticityGenerator_apply, outputMem]

/-- Polynomial vector field induced on the exact finite modal carrier. -/
def finiteModeVorticityGenerator
    (modes : Finset IntegerWavevector)
    (ν : ℝ) :
    FiniteModeVorticityCarrier modes →
      FiniteModeVorticityCarrier modes :=
  fun coefficient =>
    finiteModeRestriction modes
      (finiteStateVorticityGenerator modes ν
        (finiteModeExtension modes coefficient))

theorem finiteModeVorticityGenerator_contDiff
    (modes : Finset IntegerWavevector)
    (ν : ℝ) :
    ContDiff ℝ 1 (finiteModeVorticityGenerator modes ν) := by
  exact
    (finiteModeRestriction modes).contDiff.comp
      ((finiteStateVorticityGenerator_contDiff modes ν).comp
        (finiteModeExtension modes).contDiff)

/-- Whole-carrier commuting square: restrict, run the finite polynomial
field, and extend gives exactly the original ambient generator. -/
theorem finiteModeVorticityGenerator_factorization
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (state : ComplexVorticityHilbertState) :
    finiteModeExtension modes
        (finiteModeVorticityGenerator modes ν
          (finiteModeRestriction modes state)) =
      finiteStateVorticityGenerator modes ν state := by
  unfold finiteModeVorticityGenerator
  rw [finiteModeExtension_restriction,
    complexSharpSupportProjection_generator,
    finiteModeExtension_restriction,
    finiteStateVorticityGenerator_sharpProjection]

/-! ## Bounds generated by finite-dimensional compactness -/

/-- At a fixed inventory, viscosity, and radius, compactness generates both
a norm bound and a Lipschitz constant for the finite polynomial field. -/
theorem exists_finiteModeVorticityGenerator_bounds
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : ℝ) :
    ∃ fieldBound lipschitzBound : NNReal,
      (∀ coefficient ∈
          Metric.closedBall
            (0 : FiniteModeVorticityCarrier modes) radius,
        ‖finiteModeVorticityGenerator modes ν coefficient‖ ≤
          fieldBound) ∧
      LipschitzOnWith lipschitzBound
        (finiteModeVorticityGenerator modes ν)
        (Metric.closedBall
          (0 : FiniteModeVorticityCarrier modes) radius) := by
  letI : ProperSpace (FiniteModeVorticityCarrier modes) :=
    FiniteDimensional.proper ℝ _
  have compact :
      IsCompact
        (Metric.closedBall
          (0 : FiniteModeVorticityCarrier modes) radius) :=
    ProperSpace.isCompact_closedBall 0 radius
  obtain ⟨lipschitzBound, lipschitz⟩ :=
    (finiteModeVorticityGenerator_contDiff modes ν).contDiffOn
      |>.exists_lipschitzOnWith
        (by norm_num)
        (convex_closedBall 0 radius)
        compact
  have imageCompact :
      IsCompact
        (finiteModeVorticityGenerator modes ν ''
          Metric.closedBall
            (0 : FiniteModeVorticityCarrier modes) radius) :=
    compact.image_of_continuousOn
      (finiteModeVorticityGenerator_contDiff
        modes ν).continuous.continuousOn
  obtain ⟨bound, boundPos, fieldBound⟩ :=
    imageCompact.isBounded.exists_pos_norm_le
  let boundNN : NNReal := ⟨bound, boundPos.le⟩
  refine ⟨boundNN, lipschitzBound, ?_, lipschitz⟩
  intro coefficient coefficientMem
  exact
    fieldBound
      (finiteModeVorticityGenerator modes ν coefficient)
      ⟨coefficient, coefficientMem, rfl⟩

theorem finiteModeRestriction_maps_closedBall
    (modes : Finset IntegerWavevector)
    (radius : ℝ) :
    MapsTo (finiteModeRestriction modes)
      (Metric.closedBall
        (0 : ComplexVorticityHilbertState) radius)
      (Metric.closedBall
        (0 : FiniteModeVorticityCarrier modes) radius) := by
  intro state stateMem
  rw [Metric.mem_closedBall, dist_zero_right] at stateMem ⊢
  exact
    (finiteModeRestriction_norm_le modes state).trans stateMem

/-- The finite-factor bounds transport back to the ambient generator.  The
constants are generated here and may depend on `modes`, `ν`, and `radius`. -/
theorem exists_finiteStateVorticityGenerator_bounds
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (radius : ℝ) :
    ∃ fieldBound lipschitzBound : NNReal,
      (∀ state ∈
          Metric.closedBall
            (0 : ComplexVorticityHilbertState) radius,
        ‖finiteStateVorticityGenerator modes ν state‖ ≤
          fieldBound) ∧
      LipschitzOnWith lipschitzBound
        (finiteStateVorticityGenerator modes ν)
        (Metric.closedBall
          (0 : ComplexVorticityHilbertState) radius) := by
  obtain ⟨finiteBound, finiteLipschitz, fieldBound,
      lipschitz⟩ :=
    exists_finiteModeVorticityGenerator_bounds modes ν radius
  let extensionNorm : NNReal :=
    ‖finiteModeExtension modes‖₊
  refine
    ⟨extensionNorm * finiteBound,
      extensionNorm * finiteLipschitz, ?_, ?_⟩
  · intro state stateMem
    rw [← finiteModeVorticityGenerator_factorization
      modes ν state]
    calc
      ‖finiteModeExtension modes
          (finiteModeVorticityGenerator modes ν
            (finiteModeRestriction modes state))‖ ≤
          ‖finiteModeExtension modes‖ *
            ‖finiteModeVorticityGenerator modes ν
              (finiteModeRestriction modes state)‖ :=
        (finiteModeExtension modes).le_opNorm _
      _ ≤
          ‖finiteModeExtension modes‖ * finiteBound := by
        apply mul_le_mul_of_nonneg_left
        · exact
            fieldBound
              (finiteModeRestriction modes state)
              (finiteModeRestriction_maps_closedBall
                modes radius stateMem)
        · exact norm_nonneg _
      _ = (extensionNorm * finiteBound : NNReal) := by
        rfl
  · rw [lipschitzOnWith_iff_norm_sub_le]
    intro left leftMem right rightMem
    rw [← finiteModeVorticityGenerator_factorization
        modes ν left,
      ← finiteModeVorticityGenerator_factorization
        modes ν right,
      ← map_sub]
    calc
      ‖finiteModeExtension modes
          (finiteModeVorticityGenerator modes ν
              (finiteModeRestriction modes left) -
            finiteModeVorticityGenerator modes ν
              (finiteModeRestriction modes right))‖ ≤
          ‖finiteModeExtension modes‖ *
            ‖finiteModeVorticityGenerator modes ν
                (finiteModeRestriction modes left) -
              finiteModeVorticityGenerator modes ν
                (finiteModeRestriction modes right)‖ :=
        (finiteModeExtension modes).le_opNorm _
      _ ≤
          ‖finiteModeExtension modes‖ *
            (finiteLipschitz *
              ‖finiteModeRestriction modes left -
                finiteModeRestriction modes right‖) := by
        apply mul_le_mul_of_nonneg_left
        · exact
            (lipschitzOnWith_iff_norm_sub_le.mp lipschitz)
              (finiteModeRestriction_maps_closedBall
                modes radius leftMem)
              (finiteModeRestriction_maps_closedBall
                modes radius rightMem)
        · exact norm_nonneg _
      _ ≤
          ‖finiteModeExtension modes‖ *
            (finiteLipschitz * ‖left - right‖) := by
        gcongr
        rw [← map_sub]
        exact
          finiteModeRestriction_norm_le modes (left - right)
      _ =
          (extensionNorm * finiteLipschitz : NNReal) *
            ‖left - right‖ := by
        simp [extensionNorm]
        ring

/-! ## Uniform restart time on a fixed Galerkin inventory -/

/-- Once the outer ball is strictly larger than the inner barrier ball, the
generated fixed-cutoff bounds produce one positive Picard time which works
for every restart time and every initial point in the inner ball.  The
initial point itself remains an input to Picard's fixed-point construction,
not a field of this theorem. -/
theorem exists_uniformPicard_finiteStateVorticityGenerator
    (modes : Finset IntegerWavevector)
    (ν : ℝ)
    (innerRadius outerRadius : NNReal)
    (radiusRoom : innerRadius < outerRadius) :
    ∃ (ε : ℝ) (εPos : 0 < ε)
        (fieldBound lipschitzBound : NNReal),
      ∀ restartTime : ℝ,
        IsPicardLindelof
          (fun _ =>
            finiteStateVorticityGenerator modes ν)
          (tmin := restartTime - ε)
          (tmax := restartTime + ε)
          ⟨restartTime, by
            constructor <;> linarith⟩
          (0 : ComplexVorticityHilbertState)
          outerRadius innerRadius
          fieldBound lipschitzBound := by
  obtain ⟨fieldBound, lipschitzBound,
      fieldNormLe, lipschitz⟩ :=
    exists_finiteStateVorticityGenerator_bounds
      modes ν (outerRadius : ℝ)
  have gapPos :
      0 < (outerRadius : ℝ) - (innerRadius : ℝ) := by
    exact sub_pos.mpr (NNReal.coe_lt_coe.mpr radiusRoom)
  let ε : ℝ :=
    ((outerRadius : ℝ) - (innerRadius : ℝ)) /
      (2 * ((fieldBound : ℝ) + 1))
  have denominatorPos :
      0 < 2 * ((fieldBound : ℝ) + 1) := by
    positivity
  have εPos : 0 < ε := by
    exact div_pos gapPos denominatorPos
  refine
    ⟨ε, εPos, fieldBound, lipschitzBound, ?_⟩
  intro restartTime
  apply IsPicardLindelof.of_time_independent
      fieldNormLe lipschitz
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
        1 *
          ((outerRadius : ℝ) - (innerRadius : ℝ)) :=
      mul_le_mul_of_nonneg_right ratioLeOne gapNonneg
    _ =
        (outerRadius : ℝ) - (innerRadius : ℝ) := by
      ring

end

end ThreeDimensionalVorticityCoefficientFiniteModalPicardBounds
end NavierStokes
end SaturationMonoid
