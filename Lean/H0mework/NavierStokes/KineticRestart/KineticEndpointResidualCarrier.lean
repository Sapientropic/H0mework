import H0mework.Realization.Residual.Process
import H0mework.NavierStokes.KineticRestart.KineticEndpointTailLocalization

/-!
# The actual whole-carrier residual at a kinetic accumulation endpoint

The kinetic endpoint defect is not introduced as a detached scalar.  On the
same source-selected cofinal occurrence lineage, subtract the generated weak
endpoint before taking any Fourier projection.  The resulting complete
Hilbert-carrier residual has its own literal shift update:

```text
selected occurrence `i`
  -> selected occurrence `i + 1`
  -> keep = future-tail shift
  -> trace = current residual - next residual.
```

Its square norm converges exactly to the source-generated endpoint defect,
while every finite Fourier projection converges strongly to zero.  Hence a
positive defect is a genuine escape through the kernel of all fixed finite
observations, with the exact actual-occurrence provenance still present.
No endpoint, subsequence, cutoff, defect branch, residual, or nonzero witness
is accepted by the source-facing construction.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier

open Filter Set
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open
  ThreeDimensionalVorticityCoefficientStrongContinuationDifferenceKineticEnergy
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization
open AffineRelaxation
open ResidualProjection

noncomputable section

/-! ## Same-lineage selected residual -/

/-- The actual whole restart current at one occurrence selected by the
generated kinetic weak endpoint. -/
def wholeRestartKineticEndpointSelectedCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) : GeneratedWholeRestartCurrent nu :=
  run initial (receipt.subsequence index)

/-- Consecutive residual indices are consecutive points of the generated
cofinal subsequence, rather than caller-selected observations. -/
theorem wholeRestartKineticEndpointSelectedCurrent_index_strict
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) :
    receipt.subsequence index < receipt.subsequence (index + 1) :=
  receipt.subsequence_strictMono (Nat.lt_succ_self index)

/-- Complete pre-projection residual of one selected actual contact against
the generated weak endpoint. -/
def wholeRestartKineticEndpointResidual
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) : WholeRestartKineticEndpointState :=
  wholeRestartContactKineticState initial (receipt.subsequence index) -
    receipt.endpoint

/-- The residual is literally read from the physical contact carried by the
same selected whole-restart current. -/
theorem wholeRestartKineticEndpointResidual_eq_selectedCurrent
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) :
    wholeRestartKineticEndpointResidual initial receipt index =
      puncturedWholeVorticityKineticEuclideanState
          (wholeRestartKineticEndpointSelectedCurrent
            initial receipt index).contact.physicalState -
        receipt.endpoint := by
  rfl

/-! ## Actual update law and uniquely forced trace -/

/-- Future residuals beginning at one selected actual occurrence. -/
abbrev WholeRestartKineticEndpointResidualTail :=
  ℕ → WholeRestartKineticEndpointState

/-- Forget the current selected occurrence and retain its generated future. -/
def wholeRestartKineticEndpointResidualTailKeep :
    WholeRestartKineticEndpointResidualTail →ₗ[ℂ]
      WholeRestartKineticEndpointResidualTail where
  toFun residual offset := residual (offset + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual future endpoint residual tail on the selected source lineage. -/
def wholeRestartKineticEndpointResidualTail
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) : WholeRestartKineticEndpointResidualTail :=
  fun offset =>
    wholeRestartKineticEndpointResidual initial receipt (index + offset)

/-- The selected actual occurrence lineage is an effective residual process;
the update and keep are generated, not supplied by a caller. -/
def generatedWholeRestartKineticEndpointResidualEffectiveProcess
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial) :
    EffectiveResidualProcess
      ℂ WholeRestartKineticEndpointResidualTail ℕ where
  target := 0
  keep := wholeRestartKineticEndpointResidualTailKeep
  residual := wholeRestartKineticEndpointResidualTail initial receipt
  update := fun index => index + 1
  residual_transport_law := by
    intro index
    funext offset
    simp only [wholeRestartKineticEndpointResidualTail,
      wholeRestartKineticEndpointResidualTailKeep,
      LinearMap.coe_mk, AddHom.coe_mk]
    congr 1
    omega

/-- Whole-carrier commuting square for the next selected actual occurrence. -/
theorem wholeRestartKineticEndpointResidual_transport
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) :
    wholeRestartKineticEndpointResidualTail initial receipt (index + 1) =
      wholeRestartKineticEndpointResidualTailKeep
        (wholeRestartKineticEndpointResidualTail initial receipt index) :=
  (generatedWholeRestartKineticEndpointResidualEffectiveProcess
    initial receipt).residual_transport_law index

/-- The selected-occurrence trace is the uniquely forced complement between
the current and next complete endpoint residuals. -/
theorem wholeRestartKineticEndpointResidual_trace_head
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) :
    linearResidualTrace wholeRestartKineticEndpointResidualTailKeep
          (wholeRestartKineticEndpointResidualTail initial receipt index) 0 =
      wholeRestartKineticEndpointResidual initial receipt index -
        wholeRestartKineticEndpointResidual initial receipt (index + 1) := by
  rfl

/-- Exact residual conservation on the selected actual update. -/
theorem wholeRestartKineticEndpointResidual_eq_next_add_trace
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (index : ℕ) :
    wholeRestartKineticEndpointResidual initial receipt index =
      wholeRestartKineticEndpointResidual initial receipt (index + 1) +
        linearResidualTrace wholeRestartKineticEndpointResidualTailKeep
          (wholeRestartKineticEndpointResidualTail initial receipt index) 0 := by
  rw [wholeRestartKineticEndpointResidual_trace_head]
  abel

/-! ## Exact defect carried by the residual -/

/-- The actual endpoint residual converges weakly to zero on the complete
kinetic Hilbert carrier. -/
theorem wholeRestartKineticEndpointResidual_weak_tendsto_zero
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (test : WholeRestartKineticEndpointState) :
    Tendsto
      (fun index =>
        inner ℂ
          (wholeRestartKineticEndpointResidual initial receipt index)
          test)
      atTop (nhds 0) := by
  have weak := receipt.weak_tendsto test
  have shifted := weak.sub_const (inner ℂ receipt.endpoint test)
  convert shifted using 1
  · funext index
    rw [wholeRestartKineticEndpointResidual, inner_sub_left]
  · simp

/-- The square norm of the complete actual residual converges exactly to the
internally generated kinetic endpoint defect. -/
theorem wholeRestartKineticEndpointResidual_norm_sq_tendsto_defect
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial) :
    Tendsto
      (fun index =>
        ‖wholeRestartKineticEndpointResidual initial receipt index‖ ^ 2)
      atTop
      (nhds
        (wholeRestartKineticWeakEndpointDefect
          initial receipt.endpoint)) := by
  have normSqTendsto :
      Tendsto
        (fun index =>
          ‖wholeRestartContactKineticState
            initial (receipt.subsequence index)‖ ^ 2)
        atTop
        (nhds (wholeRestartKineticMassLimit initial)) := by
    simpa only [wholeRestartContactKineticMass] using receipt.mass_tendsto
  have weakRealTendsto :
      Tendsto
        (fun index =>
          (inner ℂ
            (wholeRestartContactKineticState
              initial (receipt.subsequence index))
            receipt.endpoint).re)
        atTop
        (nhds (‖receipt.endpoint‖ ^ 2)) := by
    have evaluated :=
      (Complex.continuous_re.tendsto
        (inner ℂ receipt.endpoint receipt.endpoint)).comp
          (receipt.weak_tendsto receipt.endpoint)
    change
      Tendsto
        (fun index =>
          (inner ℂ
            (wholeRestartContactKineticState
              initial (receipt.subsequence index))
            receipt.endpoint).re)
        atTop
        (nhds ((inner ℂ receipt.endpoint receipt.endpoint).re)) at evaluated
    have endpointInnerEq :
        (inner ℂ receipt.endpoint receipt.endpoint).re =
          ‖receipt.endpoint‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) receipt.endpoint
    rw [endpointInnerEq] at evaluated
    exact evaluated
  have expanded :
      Tendsto
        (fun index =>
          ‖wholeRestartContactKineticState
              initial (receipt.subsequence index)‖ ^ 2 -
            2 *
              (inner ℂ
                (wholeRestartContactKineticState
                  initial (receipt.subsequence index))
                receipt.endpoint).re +
              ‖receipt.endpoint‖ ^ 2)
        atTop
        (nhds
          (wholeRestartKineticMassLimit initial -
            2 * ‖receipt.endpoint‖ ^ 2 + ‖receipt.endpoint‖ ^ 2)) :=
    (normSqTendsto.sub (weakRealTendsto.const_mul 2)).add_const
      (‖receipt.endpoint‖ ^ 2)
  convert expanded using 1
  · funext index
    exact norm_sub_sq (𝕜 := ℂ)
      (wholeRestartContactKineticState
        initial (receipt.subsequence index)) receipt.endpoint
  · unfold wholeRestartKineticWeakEndpointDefect
    ring_nf

/-- Every finite Fourier observation of the actual residual converges
strongly to zero. -/
private theorem wholeRestartKineticFiniteProjection_sub
    (modes : Finset NonzeroIntegerWavevector)
    (left right : WholeRestartKineticEndpointState) :
    wholeRestartKineticFiniteProjection modes (left - right) =
      wholeRestartKineticFiniteProjection modes left -
        wholeRestartKineticFiniteProjection modes right := by
  classical
  unfold wholeRestartKineticFiniteProjection
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro wave _waveMem
  rw [show (left - right) wave = left wave - right wave by rfl,
    lp.single_sub]

theorem wholeRestartKineticEndpointResidual_finiteProjection_tendsto_zero
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (modes : Finset NonzeroIntegerWavevector) :
    Tendsto
      (fun index =>
        wholeRestartKineticFiniteProjection modes
          (wholeRestartKineticEndpointResidual initial receipt index))
      atTop (nhds 0) := by
  have projected :=
    wholeRestartKineticFiniteProjection_tendsto receipt modes
  have shifted := projected.sub_const
    (wholeRestartKineticFiniteProjection modes receipt.endpoint)
  simpa only [wholeRestartKineticEndpointResidual,
    wholeRestartKineticFiniteProjection_sub, sub_self] using shifted

/-- A positive endpoint defect is quantitatively present in every
sufficiently late whole-carrier residual, even though every fixed finite
Fourier projection tends to zero. -/
theorem wholeRestartKineticEndpointResidual_eventually_gt_half_defect
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (defectPos :
      0 < wholeRestartKineticWeakEndpointDefect
        initial receipt.endpoint) :
    ∀ᶠ index : ℕ in atTop,
      wholeRestartKineticWeakEndpointDefect initial receipt.endpoint / 2 <
        ‖wholeRestartKineticEndpointResidual initial receipt index‖ ^ 2 := by
  exact
    (wholeRestartKineticEndpointResidual_norm_sq_tendsto_defect receipt)
      (eventually_gt_nhds (by linarith))

/-! ## Source-facing canonical process -/

/-- The authoritative source chooses the weak endpoint and its occurrence
subsequence before the residual process is formed. -/
noncomputable def sourceGeneratedWholeRestartKineticEndpointResidualProcess
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    EffectiveResidualProcess
      ℂ WholeRestartKineticEndpointResidualTail ℕ :=
  generatedWholeRestartKineticEndpointResidualEffectiveProcess initial
    (generatedWholeRestartKineticWeakEndpoint initial)

/-- Source-facing whole-carrier update law.  Its mouth contains only the
actual initial whole-restart current. -/
theorem sourceGeneratedWholeRestartKineticEndpointResidual_transport
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (index : ℕ) :
    let receipt := generatedWholeRestartKineticWeakEndpoint initial
    wholeRestartKineticEndpointResidualTail initial receipt (index + 1) =
      wholeRestartKineticEndpointResidualTailKeep
        (wholeRestartKineticEndpointResidualTail initial receipt index) := by
  exact wholeRestartKineticEndpointResidual_transport initial
    (generatedWholeRestartKineticWeakEndpoint initial) index

/-- Source-facing exact identification of the scalar defect with the square
mass of the complete residual. -/
theorem
    sourceGeneratedWholeRestartKineticEndpointResidual_norm_sq_tendsto_defect
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) :
    let receipt := generatedWholeRestartKineticWeakEndpoint initial
    Tendsto
      (fun index =>
        ‖wholeRestartKineticEndpointResidual initial receipt index‖ ^ 2)
      atTop
      (nhds
        (wholeRestartKineticWeakEndpointDefect
          initial receipt.endpoint)) := by
  exact wholeRestartKineticEndpointResidual_norm_sq_tendsto_defect
    (generatedWholeRestartKineticWeakEndpoint initial)

/-- Source-facing finite-observer kernel law on the identical generated
residual lineage.  The finite observation is a consumer parameter, not a
producer cutoff. -/
theorem
    sourceGeneratedWholeRestartKineticEndpointResidual_finiteProjection_tendsto_zero
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (modes : Finset NonzeroIntegerWavevector) :
    let receipt := generatedWholeRestartKineticWeakEndpoint initial
    Tendsto
      (fun index =>
        wholeRestartKineticFiniteProjection modes
          (wholeRestartKineticEndpointResidual initial receipt index))
      atTop (nhds 0) := by
  exact
    wholeRestartKineticEndpointResidual_finiteProjection_tendsto_zero
      (generatedWholeRestartKineticWeakEndpoint initial) modes

/-- Under bounded elapsed time, this exact residual lineage approaches the
same source-generated physical accumulation time used by the endpoint write. -/
theorem sourceGeneratedWholeRestartKineticEndpointResidual_time_tendsto
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    let receipt :=
      generatedWholeRestartKineticWeakEndpointAtAccumulation
        initial elapsedBounded
    Tendsto
      (fun index => elapsedTime initial (receipt.subsequence index))
      atTop (nhds (wholeRestartAccumulationTime initial)) := by
  exact
    (generatedWholeRestartKineticWeakEndpointAtAccumulation
      initial elapsedBounded).elapsed_tendsto

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointResidualCarrier
end NavierStokes
end SaturationMonoid
