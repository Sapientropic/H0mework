import H0mework.NavierStokes.Completion.OmittedNativeSuccessor

/-!
# Versioned complete-support scale/time response

The legacy scale/time responder enters physical time as soon as the radial
outer-shell read is empty.  A nonzero nonlinear output may nevertheless lie
in an interior support hole.  This module adds one conservative source-owned
event before that time branch:

```text
legacy outer response = some
→ exact legacy shell event

legacy outer response = none, complete missing support nonempty
→ zero-filled complete-support event

legacy outer response = none, complete missing support empty
→ exact legacy positive-time event.
```

The current carrier remains the existing `ScaleTimeCurrent`.  Successful old
shell and old time branches retain their literal targets and receipts.  The
new support branch changes no physical coefficient and no elapsed time; it
only installs source-generated missing coordinates.  Its target has no
remaining missing coordinate, so the branch cannot repeat silently.

No caller supplies a branch, missing mode, target, nonzero witness, or
coverage certificate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellTraceCumulative
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellReflexiveWrite
open ThreeDimensionalVorticityCoefficientGeneratedScaleTimeReflexiveResponse
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedNativeSuccessor

noncomputable section

/-! ## Native support event on the existing current carrier -/

/-- Target of the complete zero-filled support installation. -/
def completeSupportTarget
    (current : ScaleTimeCurrent) :
    ScaleTimeCurrent where
  source := completeOmittedPhysicalLiftSource current.source
  elapsed := current.elapsed

@[simp] theorem completeSupportTarget_source
    (current : ScaleTimeCurrent) :
    (completeSupportTarget current).source =
      completeOmittedPhysicalLiftSource current.source :=
  rfl

@[simp] theorem completeSupportTarget_elapsed
    (current : ScaleTimeCurrent) :
    (completeSupportTarget current).elapsed =
      current.elapsed :=
  rfl

/--
Versioned native edge.  Branch provenance is generated inside the responder
and retained by the dependent constructor.
-/
inductive NativeStep
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    ScaleTimeCurrent → Type
  | shell
      (response :
        Response GeneratedIntegerShellStep current.source)
      (generated :
        generatedIntegerShellRespond current.source =
          some response) :
      NativeStep ν current (shellTarget current response)
  | support
      (outerStopped :
        generatedIntegerShellRespond current.source = none)
      (missingNonempty :
        (generatedMissingNonlinearModes current.source).Nonempty) :
      NativeStep ν current (completeSupportTarget current)
  | time
      (outerStopped :
        generatedIntegerShellRespond current.source = none)
      (missingEmpty :
        generatedMissingNonlinearModes current.source = ∅) :
      NativeStep ν current (timeTarget ν current)

/--
Observation of the same native event.  The support event retains its source
and generated missing-support witness, so all old `q` rows remain computable
before later coefficient aggregation.
-/
inductive Observation
    (ν : Viscosity) : Type
  | shell (receipt : GeneratedIntegerShellReceipt)
  | support
      (source : RawVorticityFourierSource)
      (missingNonempty :
        (generatedMissingNonlinearModes source).Nonempty)
  | time
      (source : RawVorticityFourierSource)
      (receipt :
        GeneratedTimeAdvanceReceipt source ν.coeff)

namespace NativeStep

/-- Read the exact receipt belonging to one generated native occurrence. -/
def observation
    {ν : Viscosity}
    {current next : ScaleTimeCurrent}
    (step : NativeStep ν current next) :
    Observation ν :=
  match step with
  | .shell response generated =>
      .shell
        (receiptOfResponse current.source response generated)
  | .support _ missingNonempty =>
      .support current.source missingNonempty
  | .time _ _ =>
      .time current.source
        (generatedTimeAdvanceReceipt current.source ν.coeff)

end NativeStep

/-! ## Total source-owned responder -/

/--
Total versioned response.  The old outer responder has first priority; the
complete missing-support inspection is reached only on its actual `none`
branch.
-/
noncomputable def generatedCompleteScaleTimeRespond
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    Response (NativeStep ν) current :=
  match outer :
      generatedIntegerShellRespond current.source with
  | some response =>
      ⟨shellTarget current response,
        NativeStep.shell response outer⟩
  | none =>
      if missingNonempty :
          (generatedMissingNonlinearModes current.source).Nonempty
      then
        ⟨completeSupportTarget current,
          NativeStep.support outer missingNonempty⟩
      else
        let missingEmpty :
            generatedMissingNonlinearModes current.source = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp missingNonempty
        ⟨timeTarget ν current,
          NativeStep.time outer missingEmpty⟩

/-- Read and write are projections of the same generated dependent event. -/
noncomputable def completeScaleTimeReflexiveQuery
    (ν : Viscosity) :
    ReflexiveQuery ScaleTimeCurrent (Observation ν) where
  read := fun current =>
    (generatedCompleteScaleTimeRespond ν current).2.observation
  write := fun current =>
    (generatedCompleteScaleTimeRespond ν current).1

/-! ## Exact old-branch conservativity -/

theorem generatedCompleteScaleTimeRespond_of_some
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.source)
    (generated :
      generatedIntegerShellRespond current.source =
        some response) :
    generatedCompleteScaleTimeRespond ν current =
      ⟨shellTarget current response,
        NativeStep.shell response generated⟩ := by
  unfold generatedCompleteScaleTimeRespond
  split
  · rename_i response' generated'
    have responseEq : response' = response :=
      Option.some.inj (generated'.symm.trans generated)
    subst response'
    have generatedEq : generated' = generated :=
      Subsingleton.elim _ _
    cases generatedEq
    rfl
  · rename_i stopped
    cases stopped.symm.trans generated

theorem generatedCompleteScaleTimeRespond_of_none_missing
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none)
    (missingNonempty :
      (generatedMissingNonlinearModes current.source).Nonempty) :
    generatedCompleteScaleTimeRespond ν current =
      ⟨completeSupportTarget current,
        NativeStep.support outerStopped missingNonempty⟩ := by
  unfold generatedCompleteScaleTimeRespond
  split
  · rename_i _response generated
    cases generated.symm.trans outerStopped
  · rename_i generated
    have generatedEq : generated = outerStopped :=
      Subsingleton.elim _ _
    cases generatedEq
    simp only [dif_pos missingNonempty]

theorem generatedCompleteScaleTimeRespond_of_none_closed
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none)
    (missingEmpty :
      generatedMissingNonlinearModes current.source = ∅) :
    generatedCompleteScaleTimeRespond ν current =
      ⟨timeTarget ν current,
        NativeStep.time outerStopped missingEmpty⟩ := by
  unfold generatedCompleteScaleTimeRespond
  split
  · rename_i _response generated
    cases generated.symm.trans outerStopped
  · rename_i generated
    have generatedEq : generated = outerStopped :=
      Subsingleton.elim _ _
    cases generatedEq
    have notNonempty :
        ¬(generatedMissingNonlinearModes current.source).Nonempty := by
      rw [missingEmpty]
      exact Finset.not_nonempty_empty
    simp only [dif_neg notNonempty]

theorem completeScaleTimeReflexiveQuery_run_of_some
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (response :
      Response GeneratedIntegerShellStep current.source)
    (generated :
      generatedIntegerShellRespond current.source =
        some response) :
    ReflexiveQuery.run (completeScaleTimeReflexiveQuery ν) current =
      (.shell
          (receiptOfResponse current.source response generated),
        shellTarget current response) := by
  unfold ReflexiveQuery.run completeScaleTimeReflexiveQuery
  change
    ((generatedCompleteScaleTimeRespond ν current).2.observation,
      (generatedCompleteScaleTimeRespond ν current).1) =
      (.shell
          (receiptOfResponse current.source response generated),
        shellTarget current response)
  rw [generatedCompleteScaleTimeRespond_of_some
    ν current response generated]
  rfl

theorem completeScaleTimeReflexiveQuery_run_of_none_missing
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none)
    (missingNonempty :
      (generatedMissingNonlinearModes current.source).Nonempty) :
    ReflexiveQuery.run (completeScaleTimeReflexiveQuery ν) current =
      (.support current.source missingNonempty,
        completeSupportTarget current) := by
  unfold ReflexiveQuery.run completeScaleTimeReflexiveQuery
  change
    ((generatedCompleteScaleTimeRespond ν current).2.observation,
      (generatedCompleteScaleTimeRespond ν current).1) =
      (.support current.source missingNonempty,
        completeSupportTarget current)
  rw [generatedCompleteScaleTimeRespond_of_none_missing
    ν current outerStopped missingNonempty]
  rfl

theorem completeScaleTimeReflexiveQuery_run_of_none_closed
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none)
    (missingEmpty :
      generatedMissingNonlinearModes current.source = ∅) :
    ReflexiveQuery.run (completeScaleTimeReflexiveQuery ν) current =
      (.time current.source
          (generatedTimeAdvanceReceipt current.source ν.coeff),
        timeTarget ν current) := by
  unfold ReflexiveQuery.run completeScaleTimeReflexiveQuery
  change
    ((generatedCompleteScaleTimeRespond ν current).2.observation,
      (generatedCompleteScaleTimeRespond ν current).1) =
      (.time current.source
          (generatedTimeAdvanceReceipt current.source ν.coeff),
        timeTarget ν current)
  rw [generatedCompleteScaleTimeRespond_of_none_closed
    ν current outerStopped missingEmpty]
  rfl

/-! ## The support event closes its own native demand -/

theorem completeSupportTarget_generatedState
    (current : ScaleTimeCurrent) :
    generatedComplexVorticityState
        (completeSupportTarget current).source
        (generatedSupport (completeSupportTarget current).source) =
      generatedComplexVorticityState current.source
        (generatedSupport current.source) := by
  exact
    (completeOmittedPhysicalLiftSource_generatedState
      current.source).trans
      (generatedCompleteNonlinearInitialState_eq_currentPhysicalState
        current.source)

@[simp] theorem completeSupportTarget_missingNonlinearModes
    (current : ScaleTimeCurrent) :
    generatedMissingNonlinearModes
        (completeSupportTarget current).source =
      ∅ :=
  generatedMissingNonlinearModes_completeLift current.source

/--
After one generated support event, the next response cannot be another
support event.  It is natively either an old shell response or the old
positive-time response.
-/
theorem completeSupportTarget_next_is_shell_or_time
    (ν : Viscosity)
    (current : ScaleTimeCurrent) :
    (∃ response :
        Response GeneratedIntegerShellStep
          (completeSupportTarget current).source,
      ∃ generated :
          generatedIntegerShellRespond
              (completeSupportTarget current).source =
            some response,
        generatedCompleteScaleTimeRespond
            ν (completeSupportTarget current) =
          ⟨shellTarget (completeSupportTarget current) response,
            NativeStep.shell response generated⟩) ∨
    (∃ stopped :
        generatedIntegerShellRespond
            (completeSupportTarget current).source =
          none,
      generatedCompleteScaleTimeRespond
          ν (completeSupportTarget current) =
        ⟨timeTarget ν (completeSupportTarget current),
          NativeStep.time stopped
            (completeSupportTarget_missingNonlinearModes current)⟩) := by
  rcases
      Option.eq_none_or_eq_some
        (generatedIntegerShellRespond
          (completeSupportTarget current).source) with
    stopped | ⟨response, generated⟩
  · exact Or.inr
      ⟨stopped,
        generatedCompleteScaleTimeRespond_of_none_closed
          ν (completeSupportTarget current) stopped
          (completeSupportTarget_missingNonlinearModes current)⟩
  · exact Or.inl
      ⟨response, generated,
        generatedCompleteScaleTimeRespond_of_some
          ν (completeSupportTarget current) response generated⟩

/--
A support event can only be generated after the old radial responder has
stopped.  Under that exact event provenance, the conservative support target
does not manufacture a new radial shell: its authoritative next response is
the physical-time event.
-/
theorem completeSupportTarget_next_is_time
    (ν : Viscosity)
    (current : ScaleTimeCurrent)
    (outerStopped :
      generatedIntegerShellRespond current.source = none) :
    generatedCompleteScaleTimeRespond
        ν (completeSupportTarget current) =
      ⟨timeTarget ν (completeSupportTarget current),
        NativeStep.time
          (generatedIntegerShellRespond_completeLift_eq_none_of_none
            current.source outerStopped)
          (completeSupportTarget_missingNonlinearModes current)⟩ := by
  exact
    generatedCompleteScaleTimeRespond_of_none_closed
      ν (completeSupportTarget current)
      (generatedIntegerShellRespond_completeLift_eq_none_of_none
        current.source outerStopped)
      (completeSupportTarget_missingNonlinearModes current)

end

end
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedScaleTimeResponse
end NavierStokes
end SaturationMonoid
