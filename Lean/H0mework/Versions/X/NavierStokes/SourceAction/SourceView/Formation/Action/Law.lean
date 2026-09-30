import H0mework.NavierStokes.SourceAction.SourceView.Formation.Occurrence.Material
import H0mework.Versions.X.NavierStokes.SourceAction.SourceView.Formation.Action.Material
import H0mework.Versions.X.NavierStokes.WindowPhysics.WindowEvolution
import H0mework.Versions.X.NavierStokes.SourceWindow.PairingReadout

set_option autoImplicit false
open scoped Topology

namespace SaturationMonoid.NavierStokes.NativeWindowMotherActualLaw

open Set Filter MeasureTheory
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeRecursion
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartNativeAccumulationRoot
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartVelocityWeakEndpoint
open NativeCompleteStressAction NativeWindowMotherOccurrenceMaterial
open NativeWindowMotherActionMaterial
open PhysicsCore.Stage10.SourceUniqueness MotherStreamLaws MotherClosedRestrictions

noncomputable section
variable {nu : Viscosity}

def target (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) : NativeTemporalCurrent seed :=
  match anchor.1 with
  | .finite index => .finite (index + 1)
  | .cofinal => .galerkin 0
  | .galerkin radius => .galerkin (radius + 1)

theorem target_compiled (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) :
    ((nativeTemporalSource seed).toRootSource.actual.compile anchor.2).nextCurrent? =
      some (target seed anchor) := by
  rcases anchor with ⟨current, support, event⟩
  cases event <;> rfl

def timeAt (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : ℝ :=
  sourceClock seed input.1.1 + input.2.time

/-- Complete real-time event observations precede the full Hilbert action rows. -/
def actual (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : Stream :=
  pairStream (fun index => if index = 0 then (currentCode seed input.1.1 : ℝ)
    else (currentCode seed (target seed input.1) : ℝ))
    (pairStream (observation seed input.1 input.2.time)
      (pairStream (samples (NativeUnifiedCompleteSource.source seed (timeAt seed input)))
        (pairStream (samples (NativeForwardWindowJets.jet seed input.2.order (timeAt seed input)))
          (pairStream (actionSamples (momentumCLM nu
            (NativeForwardWindowJets.jet seed input.2.order (timeAt seed input))))
            (samples (NativeForwardWindowJets.jet seed input.2.order
              (sourceClock seed (target seed input.1) + input.2.time)))))))

theorem exists_law (seed : GeneratedWholeRestartCurrent nu) :
    ∃ law : MotherPhysicalLaws.Law, ∀ input : Input seed,
      MotherPhysicalLaws.eval law (nsRawInput seed input) = actual seed input := by
  obtain ⟨law, generated, _⟩ := MotherPhysicalLaws.every_law
    (fun raw => actual seed (recover seed raw))
  refine ⟨law, fun input => ?_⟩
  rw [generated, recover_nsRawInput]

def law (seed : GeneratedWholeRestartCurrent nu) : MotherPhysicalLaws.Law := (exists_law seed).choose

def read (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : Stream :=
  MotherPhysicalLaws.eval (law seed) (nsRawInput seed input)

theorem read_original (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    read seed input = actual seed input := (exists_law seed).choose_spec input

def next (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : NativeTemporalCurrent seed := by
  letI : Nonempty (NativeTemporalCurrent seed) := ⟨.finite 0⟩
  exact Function.invFun (currentCode seed) (Nat.floor (firstStream (read seed input) 1))

theorem next_original (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    next seed input = target seed input.1 := by
  let : Nonempty (NativeTemporalCurrent seed) := ⟨.finite 0⟩
  unfold next
  simp only [read_original, actual, first_pair, one_ne_zero, ↓reduceIte, Nat.floor_natCast]
  exact Function.leftInverse_invFun (currentCode_injective seed) _

theorem next_compiled (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    ((nativeTemporalSource seed).toRootSource.actual.compile input.1.2).nextCurrent? =
      some (next seed input) := by
  rw [next_original]
  exact target_compiled seed input.1

def eventRead (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : Stream :=
  firstStream (lastStream (read seed input))

def raw (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : FullSpace :=
  restore (firstStream (lastStream (lastStream (read seed input))))

def window (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : FullSpace :=
  restore (firstStream (lastStream (lastStream (lastStream (read seed input)))))

def action (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : WholeRestartVelocityEndpointState :=
  restoreAction (firstStream (lastStream (lastStream (lastStream (lastStream (read seed input))))))

def after (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) : FullSpace :=
  restore (lastStream (lastStream (lastStream (lastStream (lastStream (read seed input))))))

theorem eventRead_original (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    eventRead seed input = observation seed input.1 input.2.time := by
  simp only [eventRead, read_original, actual, first_pair, last_pair]

theorem read_family_injective (seed : GeneratedWholeRestartCurrent nu) :
    Function.Injective (fun anchor : Anchor seed => fun query : Query => read seed (anchor, query)) := by
  rintro ⟨first, firstOccurrence⟩ ⟨last, lastOccurrence⟩ same
  have codes := congrArg (fun value : Query → Stream => firstStream (value ⟨0, 0, 0⟩) 0) same
  simp only [read_original, actual, first_pair, ↓reduceIte] at codes
  have currents : first = last := currentCode_injective seed (Nat.cast_injective codes)
  cases currents
  have observations : observation seed ⟨first, firstOccurrence⟩ =
      observation seed ⟨first, lastOccurrence⟩ := by
    funext time index
    have values := congrArg (fun value : Query → Stream =>
      firstStream (lastStream (value ⟨time, 0, 0⟩)) index) same
    simpa only [read_original, actual, first_pair, last_pair] using values
  have occurrences := occurrence_recovered seed first firstOccurrence lastOccurrence observations
  cases occurrences
  rfl

def restoreAnchor (seed : GeneratedWholeRestartCurrent nu) (values : Query → Stream) : Anchor seed := by
  letI : Nonempty (Anchor seed) := ⟨⟨.finite 0, nativeTemporalEmitted seed (.finite 0)⟩⟩
  exact Function.invFun (fun anchor : Anchor seed => fun query => read seed (anchor, query)) values

theorem whole_occurrence_restored (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) :
    restoreAnchor seed (fun query => read seed (anchor, query)) = anchor := by
  let : Nonempty (Anchor seed) := ⟨⟨.finite 0, nativeTemporalEmitted seed (.finite 0)⟩⟩
  exact Function.leftInverse_invFun (read_family_injective seed) anchor

theorem raw_original (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    raw seed input = NativeUnifiedCompleteSource.source seed (timeAt seed input) := by
  simp only [raw, read_original, actual, first_pair, last_pair, restore_samples]

theorem window_original (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    window seed input = NativeForwardWindowJets.jet seed input.2.order (timeAt seed input) := by
  simp only [window, read_original, actual, first_pair, last_pair, restore_samples]

theorem action_original (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    action seed input = momentumCLM nu (window seed input) := by
  simp only [action, read_original, actual, first_pair, last_pair, restore_actionSamples, window_original]

theorem after_original (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    after seed input = NativeForwardWindowJets.jet seed input.2.order
      (sourceClock seed (target seed input.1) + input.2.time) := by
  simp only [after, read_original, actual, last_pair, restore_samples]

theorem after_is_next (seed : GeneratedWholeRestartCurrent nu) (input : Input seed) :
    after seed input = window seed
      (⟨next seed input, nativeTemporalEmitted seed (next seed input)⟩, input.2) := by
  rw [after_original, window_original]
  simp only [timeAt, next_original]

theorem full_history (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed) :
    (fun time => raw seed (anchor, ⟨time, 0, 0⟩)) =
      fun time => NativeUnifiedCompleteSource.source seed (sourceClock seed anchor.1 + time) := by
  funext time
  exact raw_original seed _

theorem window_hasDerivAt (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed)
    (radius order : ℕ) (time : ℝ) :
    HasDerivAt (fun sample => window seed (anchor, ⟨sample, radius, order⟩))
      (window seed (anchor, ⟨time, radius, order + 1⟩)) time := by
  simp only [window_original, timeAt]
  simpa only [Function.comp_def, one_smul] using
    (NativeForwardWindowJets.jet_hasDerivAt seed order (sourceClock seed anchor.1 + time)).scomp time
      ((hasDerivAt_id time).const_add (sourceClock seed anchor.1))

theorem source_action (seed : GeneratedWholeRestartCurrent nu) (input : Input seed)
    (valid : -1 < timeAt seed input) :
    NativeNegativeFourMomentum.embed
      (window seed (input.1, {input.2 with order := input.2.order + 1})).fst = action seed input := by
  rw [action_original, window_original, window_original]
  exact NativeForwardWindowEvolution.source_physical_word seed input.2.order (timeAt seed input) valid

theorem source_integral (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed)
    (radius : ℕ) (a b : ℝ) (aValid : -1 ≤ sourceClock seed anchor.1 + a)
    (bValid : -1 ≤ sourceClock seed anchor.1 + b) :
    NativeForwardWindowWrite.stateCLM (window seed (anchor, ⟨b, radius, 0⟩)) -
      NativeForwardWindowWrite.stateCLM (window seed (anchor, ⟨a, radius, 0⟩)) =
        ∫ time in a..b, action seed (anchor, ⟨time, radius, 0⟩) := by
  simp only [window_original, action_original, timeAt, NativeForwardWindowJets.jet_zero]
  rw [intervalIntegral.integral_comp_add_left
    (fun time => momentumCLM nu (NativeForwardWindowSource.source seed time)) (sourceClock seed anchor.1)]
  simpa only [NativeForwardWindowWrite.state_embedded, NativeForwardWindowWrite.stateCLM,
    ContinuousLinearMap.comp_apply, WithLp.fstL_apply] using
    NativeForwardWindowWrite.state_integral seed (sourceClock seed anchor.1 + a)
      (sourceClock seed anchor.1 + b) aValid bValid

theorem full_residual (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed)
    (radius : ℕ) (time : ℝ) :
    NativeCompleteCorrectionRead.residual (window seed (anchor, ⟨time, radius, 0⟩)) =
      NativeCompleteStressCarrier.read (NativeForwardWindowSource.source seed (sourceClock seed anchor.1 + time)).snd -
        NativeStressSource.quadraticFlux (NativeEndpointVelocityCarrier.wholeVelocity
          (NativeForwardWindowSource.source seed (sourceClock seed anchor.1 + time)).fst) := by
  rw [window_original, NativeForwardWindowJets.jet_zero]
  rfl

theorem native_action (seed : GeneratedWholeRestartCurrent nu) (input : Input seed)
    (modes : Finset IntegerWavevector) :
    NativeCompleteFilteredWrite.readCLM modes (action seed input) =
      NativeCompleteEvolution.nativeRHS nu modes (window seed input) := by
  rw [action_original, NativeCompleteActionOperator.nativeRHS_eq_actionCLM]
  rfl

theorem native_write (seed : GeneratedWholeRestartCurrent nu) (anchor : Anchor seed)
    (modes : Finset IntegerWavevector) (radius : ℕ) (time : ℝ)
    (valid : -1 < sourceClock seed anchor.1 + time) :
    HasDerivAt (fun sample => NativeCompleteFilteredWrite.readCLM modes
      (NativeForwardWindowWrite.stateCLM (window seed (anchor, ⟨sample, radius, 0⟩))))
      (NativeCompleteEvolution.nativeRHS nu modes (window seed (anchor, ⟨time, radius, 0⟩))) time := by
  simp only [window_original, timeAt, NativeForwardWindowJets.jet_zero]
  simpa only [Function.comp_def, one_smul, NativeForwardWindowWrite.state_embedded,
    NativeForwardWindowWrite.stateCLM, ContinuousLinearMap.comp_apply, WithLp.fstL_apply] using
    (NativeForwardWindowEvolution.complete_native_rate seed modes
      (sourceClock seed anchor.1 + time) valid).scomp time
        ((hasDerivAt_id time).const_add (sourceClock seed anchor.1))

end
end SaturationMonoid.NavierStokes.NativeWindowMotherActualLaw
