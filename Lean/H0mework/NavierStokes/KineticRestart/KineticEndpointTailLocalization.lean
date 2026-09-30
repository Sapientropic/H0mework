import H0mework.NavierStokes.KineticRestart.KineticWeakEndpoint

/-!
# High-frequency localization of the generated kinetic endpoint defect

The source-generated kinetic weak endpoint already carries the exact limit
of the actual kinetic masses and an internal zero/positive defect
disposition.  This module identifies that defect before any infinite-mode
quotient:

* every finite set of nonzero Fourier rows converges strongly along the
  same generated subsequence;
* the complementary square mass has the exact limit
  `defect + endpoint-tail-square`;
* a positive defect therefore survives outside every finite Fourier
  window, while the zero branch retains the existing whole-carrier strong
  convergence.

No endpoint, subsequence, finite cutoff, defect branch, norm bound, target
trajectory, or continuation witness enters the source-facing theorem.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization

open Filter Metric Set
open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open
  ThreeDimensionalVorticityCoefficientGeneratedIntegerShellStrongContinuationEnergyLedger
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion.GeneratedWholeRestartCurrent
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartCrossingTangentCoercivity
open
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticWeakEndpoint

noncomputable section

/-! ## Finite Fourier windows in the kinetic carrier -/

/-- The exact finite Fourier projection in the kinetic `lp²` endpoint
carrier.  It is a readout of a supplied state, not a source producer. -/
def wholeRestartKineticFiniteProjection
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartKineticEndpointState) :
    WholeRestartKineticEndpointState :=
  ∑ wave ∈ modes, lp.single 2 wave (state wave)

/-- The complementary kinetic responsibility outside a finite Fourier
window. -/
def wholeRestartKineticFiniteTail
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartKineticEndpointState) :
    WholeRestartKineticEndpointState :=
  state - wholeRestartKineticFiniteProjection modes state

/-- The finite projection and its complement form an exact square-mass
partition in the kinetic Hilbert carrier. -/
theorem wholeRestartKineticFiniteTail_norm_sq
    (modes : Finset NonzeroIntegerWavevector)
    (state : WholeRestartKineticEndpointState) :
    ‖wholeRestartKineticFiniteTail modes state‖ ^ 2 =
      ‖state‖ ^ 2 -
        ‖wholeRestartKineticFiniteProjection modes state‖ ^ 2 := by
  classical
  have complementEq :=
    lp.norm_compl_sum_single
      (p := (2 : ENNReal)) (by norm_num) state modes
  have projectionEq :=
    lp.norm_sum_single
      (p := (2 : ENNReal)) (by norm_num)
      (fun wave => state wave) modes
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at complementEq projectionEq
  calc
    ‖wholeRestartKineticFiniteTail modes state‖ ^ 2 =
        ‖state‖ ^ 2 - ∑ wave ∈ modes, ‖state wave‖ ^ 2 := by
      simpa only [wholeRestartKineticFiniteTail,
        wholeRestartKineticFiniteProjection] using complementEq
    _ = ‖state‖ ^ 2 -
        ‖wholeRestartKineticFiniteProjection modes state‖ ^ 2 := by
      simpa only [wholeRestartKineticFiniteProjection] using
        congrArg (fun value => ‖state‖ ^ 2 - value) projectionEq.symm

/-! ## Weak convergence is strong on every finite window -/

private theorem kineticRow_tendsto_of_weak_tendsto
    (sequence : ℕ → WholeRestartKineticEndpointState)
    (endpoint : WholeRestartKineticEndpointState)
    (weakTendsto :
      ∀ test : WholeRestartKineticEndpointState,
        Tendsto
          (fun index => inner ℂ (sequence index) test)
          atTop
          (nhds (inner ℂ endpoint test)))
    (wave : NonzeroIntegerWavevector) :
    Tendsto (fun index => sequence index wave) atTop
      (nhds (endpoint wave)) := by
  classical
  have coordinateTendsto :
      ∀ coordinate : Coordinate,
        Tendsto
          (fun index => sequence index wave coordinate)
          atTop
          (nhds (endpoint wave coordinate)) := by
    intro coordinate
    let test : WholeRestartKineticEndpointState :=
      lp.single 2 wave (EuclideanSpace.single coordinate 1)
    have innerTendsto := weakTendsto test
    have conjugateTendsto :
        Tendsto
          (fun index => starRingEnd ℂ (sequence index wave coordinate))
          atTop
          (nhds (starRingEnd ℂ (endpoint wave coordinate))) := by
      simpa only [test, lp.inner_single_right,
        EuclideanSpace.inner_single_right, one_mul] using innerTendsto
    have unconjugated :=
      (Complex.continuous_conj.tendsto
        (starRingEnd ℂ (endpoint wave coordinate))).comp conjugateTendsto
    change
      Tendsto
        (fun index =>
          starRingEnd ℂ (starRingEnd ℂ (sequence index wave coordinate)))
        atTop
        (nhds (starRingEnd ℂ (starRingEnd ℂ (endpoint wave coordinate)))) at unconjugated
    simpa only [starRingEnd_self_apply] using unconjugated
  have functionTendsto :
      Tendsto
        (fun index => WithLp.ofLp (sequence index wave))
        atTop
        (nhds (WithLp.ofLp (endpoint wave))) := by
    exact tendsto_pi_nhds.mpr coordinateTendsto
  have lifted :
      Tendsto
        (fun index =>
          WithLp.toLp 2 (WithLp.ofLp (sequence index wave)))
        atTop
        (nhds (WithLp.toLp 2 (WithLp.ofLp (endpoint wave)))) :=
    (PiLp.continuous_toLp
      (p := (2 : ENNReal))
      (β := fun _ : Coordinate => ℂ)).tendsto
        (WithLp.ofLp (endpoint wave))
      |>.comp functionTendsto
  simpa only [WithLp.toLp_ofLp] using lifted

/-- Every finite Fourier projection converges strongly along the exact
subsequence selected by the generated weak endpoint receipt. -/
theorem wholeRestartKineticFiniteProjection_tendsto
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (modes : Finset NonzeroIntegerWavevector) :
    Tendsto
      (fun index =>
        wholeRestartKineticFiniteProjection modes
          (wholeRestartContactKineticState
            initial (receipt.subsequence index)))
      atTop
      (nhds
        (wholeRestartKineticFiniteProjection modes receipt.endpoint)) := by
  classical
  unfold wholeRestartKineticFiniteProjection
  apply tendsto_finsetSum modes
  intro wave _waveMem
  have rowTendsto := kineticRow_tendsto_of_weak_tendsto
    (fun index =>
      wholeRestartContactKineticState
        initial (receipt.subsequence index))
    receipt.endpoint receipt.weak_tendsto wave
  exact
    (lp.singleContinuousLinearMap
      ℂ (fun _ : NonzeroIntegerWavevector => ComplexCoordinateEuclidean)
      2 wave).continuous.tendsto _ |>.comp rowTendsto

/-! ## Exact localization of the endpoint defect -/

/-- For every finite Fourier window, the actual complementary square mass
converges to the endpoint tail plus the unique weak-endpoint defect. -/
theorem wholeRestartKineticFiniteTail_norm_sq_tendsto
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (modes : Finset NonzeroIntegerWavevector) :
    Tendsto
      (fun index =>
        ‖wholeRestartKineticFiniteTail modes
          (wholeRestartContactKineticState
            initial (receipt.subsequence index))‖ ^ 2)
      atTop
      (nhds
        (wholeRestartKineticWeakEndpointDefect initial receipt.endpoint +
          ‖wholeRestartKineticFiniteTail modes receipt.endpoint‖ ^ 2)) := by
  have massTendsto :
      Tendsto
        (fun index =>
          ‖wholeRestartContactKineticState
            initial (receipt.subsequence index)‖ ^ 2)
        atTop
        (nhds (wholeRestartKineticMassLimit initial)) := by
    simpa only [wholeRestartContactKineticMass] using receipt.mass_tendsto
  have projectionTendsto :=
    wholeRestartKineticFiniteProjection_tendsto receipt modes
  have projectionSquareTendsto :
      Tendsto
        (fun index =>
          ‖wholeRestartKineticFiniteProjection modes
            (wholeRestartContactKineticState
              initial (receipt.subsequence index))‖ ^ 2)
        atTop
        (nhds
          (‖wholeRestartKineticFiniteProjection modes receipt.endpoint‖ ^ 2)) :=
    (projectionTendsto.norm.pow 2)
  have differenceTendsto := massTendsto.sub projectionSquareTendsto
  convert differenceTendsto using 1
  · funext index
    exact wholeRestartKineticFiniteTail_norm_sq modes
      (wholeRestartContactKineticState
        initial (receipt.subsequence index))
  · rw [wholeRestartKineticFiniteTail_norm_sq]
    unfold wholeRestartKineticWeakEndpointDefect
    ring_nf

/-- A positive source-generated defect cannot be hidden in any finite
Fourier window: eventually at least half of that defect remains in the
actual complementary kinetic square mass. -/
theorem wholeRestartKineticFiniteTail_eventually_gt_half_defect
    {nu : Viscosity}
    {initial : GeneratedWholeRestartCurrent nu}
    (receipt : GeneratedWholeRestartKineticWeakEndpoint initial)
    (defectPos :
      0 < wholeRestartKineticWeakEndpointDefect
        initial receipt.endpoint)
    (modes : Finset NonzeroIntegerWavevector) :
    ∀ᶠ index : ℕ in atTop,
      wholeRestartKineticWeakEndpointDefect initial receipt.endpoint / 2 <
        ‖wholeRestartKineticFiniteTail modes
          (wholeRestartContactKineticState
            initial (receipt.subsequence index))‖ ^ 2 := by
  have limitGtHalf :
      wholeRestartKineticWeakEndpointDefect initial receipt.endpoint / 2 <
        wholeRestartKineticWeakEndpointDefect initial receipt.endpoint +
          ‖wholeRestartKineticFiniteTail modes receipt.endpoint‖ ^ 2 := by
    have tailNonneg :
        0 ≤ ‖wholeRestartKineticFiniteTail modes receipt.endpoint‖ ^ 2 :=
      sq_nonneg _
    linarith
  exact
    (wholeRestartKineticFiniteTail_norm_sq_tendsto receipt modes)
      (eventually_gt_nhds limitGtHalf)

/-! ## Source-generated accumulation endpoint disposition -/

/-- The bounded-time kinetic endpoint together with exact localization of
its defect outside every finite Fourier window. -/
structure GeneratedWholeRestartKineticEndpointTailLocalization
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu) extends
      GeneratedWholeRestartKineticWeakEndpointAtAccumulation initial where
  finite_projection_tendsto :
    ∀ modes : Finset NonzeroIntegerWavevector,
      Tendsto
        (fun index =>
          wholeRestartKineticFiniteProjection modes
            (wholeRestartContactKineticState
              initial (subsequence index)))
        atTop
        (nhds (wholeRestartKineticFiniteProjection modes endpoint))
  finite_tail_norm_sq_tendsto :
    ∀ modes : Finset NonzeroIntegerWavevector,
      Tendsto
        (fun index =>
          ‖wholeRestartKineticFiniteTail modes
            (wholeRestartContactKineticState
              initial (subsequence index))‖ ^ 2)
        atTop
        (nhds
          (wholeRestartKineticWeakEndpointDefect initial endpoint +
            ‖wholeRestartKineticFiniteTail modes endpoint‖ ^ 2))
  defect_tail_disposition :
    (0 < wholeRestartKineticWeakEndpointDefect initial endpoint ∧
      ∀ modes : Finset NonzeroIntegerWavevector,
        ∀ᶠ index : ℕ in atTop,
          wholeRestartKineticWeakEndpointDefect initial endpoint / 2 <
            ‖wholeRestartKineticFiniteTail modes
              (wholeRestartContactKineticState
                initial (subsequence index))‖ ^ 2) ∨
      (wholeRestartKineticWeakEndpointDefect initial endpoint = 0 ∧
        Tendsto
          (fun index =>
            wholeRestartContactKineticState initial (subsequence index))
          atTop
          (nhds endpoint))

/-- Bounded elapsed time itself generates the endpoint, subsequence and
defect branch.  A positive defect is forced beyond every finite Fourier
window; the complementary branch is strong whole-carrier convergence. -/
noncomputable def generates_wholeRestartKineticEndpointTailLocalization
    {nu : Viscosity}
    (initial : GeneratedWholeRestartCurrent nu)
    (elapsedBounded : BddAbove (Set.range (elapsedTime initial))) :
    GeneratedWholeRestartKineticEndpointTailLocalization initial := by
  let receipt :=
    generatedWholeRestartKineticWeakEndpointAtAccumulation
      initial elapsedBounded
  let weakReceipt := receipt.toGeneratedWholeRestartKineticWeakEndpoint
  have projectionTendsto :
      ∀ modes : Finset NonzeroIntegerWavevector,
        Tendsto
          (fun index =>
            wholeRestartKineticFiniteProjection modes
              (wholeRestartContactKineticState
                initial (weakReceipt.subsequence index)))
          atTop
          (nhds
            (wholeRestartKineticFiniteProjection modes
              weakReceipt.endpoint)) :=
    wholeRestartKineticFiniteProjection_tendsto weakReceipt
  have tailTendsto :
      ∀ modes : Finset NonzeroIntegerWavevector,
        Tendsto
          (fun index =>
            ‖wholeRestartKineticFiniteTail modes
              (wholeRestartContactKineticState
                initial (weakReceipt.subsequence index))‖ ^ 2)
          atTop
          (nhds
            (wholeRestartKineticWeakEndpointDefect
                initial weakReceipt.endpoint +
              ‖wholeRestartKineticFiniteTail modes
                weakReceipt.endpoint‖ ^ 2)) :=
    wholeRestartKineticFiniteTail_norm_sq_tendsto weakReceipt
  have disposition :
      (0 < wholeRestartKineticWeakEndpointDefect
          initial weakReceipt.endpoint ∧
        ∀ modes : Finset NonzeroIntegerWavevector,
          ∀ᶠ index : ℕ in atTop,
            wholeRestartKineticWeakEndpointDefect
                initial weakReceipt.endpoint / 2 <
              ‖wholeRestartKineticFiniteTail modes
                (wholeRestartContactKineticState
                  initial (weakReceipt.subsequence index))‖ ^ 2) ∨
        (wholeRestartKineticWeakEndpointDefect
            initial weakReceipt.endpoint = 0 ∧
          Tendsto
            (fun index =>
              wholeRestartContactKineticState
                initial (weakReceipt.subsequence index))
            atTop
            (nhds weakReceipt.endpoint)) := by
    rcases weakReceipt.defect_disposition with defectPos | strongBranch
    · exact Or.inl
        ⟨defectPos,
          wholeRestartKineticFiniteTail_eventually_gt_half_defect
            weakReceipt defectPos⟩
    · exact Or.inr strongBranch
  exact
    { toGeneratedWholeRestartKineticWeakEndpointAtAccumulation := receipt
      finite_projection_tendsto := projectionTendsto
      finite_tail_norm_sq_tendsto := tailTendsto
      defect_tail_disposition := disposition }

end

end
  ThreeDimensionalVorticityCoefficientGeneratedWholeRestartKineticEndpointTailLocalization
end NavierStokes
end SaturationMonoid
