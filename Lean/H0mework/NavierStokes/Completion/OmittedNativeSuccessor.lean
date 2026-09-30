import H0mework.NavierStokes.Completion.OmittedUnforcedReceipt

/-!
# Native closure of the complete omitted-support installation

The complete target consumer installs only coordinates genuinely absent from
the source-owned Galerkin support.  This module proves that the installation
is a conservative native successor:

* the physical coefficient state is unchanged;
* every generated vorticity coefficient is unchanged;
* the complete nonlinear coefficient table is unchanged;
* the live coefficient set is unchanged;
* the successor has no remaining genuinely missing nonlinear row.

The last statement is about support ownership, not nonlinear silence.
Dormant owned rows may still carry a nonzero tangent responsibility and are
consumed by the actual unforced receipt.  No target, branch, coverage proof,
or nonzero witness occurs in the theorem mouths.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedNativeSuccessor

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
open
  ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedUnforcedReceipt

noncomputable section

/-! ## Whole-state and coefficient conservativity -/

/--
The zero-filled installation preserves every generated Fourier coefficient,
including rows outside both supports.
-/
theorem generatedVorticityCoefficient_completeOmittedPhysicalLiftSource
    (source : RawVorticityFourierSource)
    (wave : IntegerWavevector) :
    generatedVorticityCoefficient
        (completeOmittedPhysicalLiftSource source) wave =
      generatedVorticityCoefficient source wave := by
  have stateEq :
      generatedComplexVorticityState
          (completeOmittedPhysicalLiftSource source)
          (generatedSupport
            (completeOmittedPhysicalLiftSource source))
          wave =
        generatedComplexVorticityState source
          (generatedSupport source) wave :=
    congrArg
      (fun state : ComplexVorticityHilbertState => state wave)
      ((completeOmittedPhysicalLiftSource_generatedState source).trans
        (generatedCompleteNonlinearInitialState_eq_currentPhysicalState
          source))
  by_cases oldMem : wave ∈ generatedSupport source
  · have completeMem :
        wave ∈ generatedCompleteNonlinearGalerkinModes source :=
      generatedSupport_subset_completeNonlinearGalerkinModes
        source oldMem
    have liftMem :
        wave ∈ generatedSupport
          (completeOmittedPhysicalLiftSource source) := by
      rwa [completeOmittedPhysicalLiftSource_generatedSupport]
    simpa [generatedComplexVorticityState_apply, oldMem, liftMem]
      using stateEq
  · have oldZero :
        generatedVorticityCoefficient source wave = 0 :=
      generatedVorticityCoefficient_eq_zero_of_not_mem source oldMem
    by_cases liftMem :
        wave ∈ generatedSupport
          (completeOmittedPhysicalLiftSource source)
    · simpa [generatedComplexVorticityState_apply, oldMem, liftMem,
        oldZero] using stateEq
    · rw [generatedVorticityCoefficient_eq_zero_of_not_mem
        (completeOmittedPhysicalLiftSource source) liftMem,
      oldZero]

/--
Zero-filled support ownership preserves the whole old nonlinear coefficient
table.  Additional formal pair rows contain zero amplitudes and do not alter
the physical convolution.
-/
theorem generatedVorticityNonlinearCoefficientAt_completeLift
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    generatedVorticityNonlinearCoefficientAt
        (completeOmittedPhysicalLiftSource source) output =
      generatedVorticityNonlinearCoefficientAt source output := by
  calc
    generatedVorticityNonlinearCoefficientAt
        (completeOmittedPhysicalLiftSource source) output =
      finiteStateVorticityNonlinearCoefficientAt
        (generatedSupport
          (completeOmittedPhysicalLiftSource source))
        (generatedComplexVorticityState
          (completeOmittedPhysicalLiftSource source)
          (generatedSupport
            (completeOmittedPhysicalLiftSource source)))
        output :=
      (finiteStateVorticityNonlinearCoefficientAt_generatedSource
        (completeOmittedPhysicalLiftSource source) output).symm
    _ =
      finiteStateVorticityNonlinearCoefficientAt
        (generatedCompleteNonlinearGalerkinModes source)
        (generatedCompleteNonlinearInitialState source)
        output := by
      have stateEq :
          generatedComplexVorticityState
              (completeOmittedPhysicalLiftSource source)
              (generatedCompleteNonlinearGalerkinModes source) =
            generatedCompleteNonlinearInitialState source := by
        rw [← completeOmittedPhysicalLiftSource_generatedSupport]
        exact completeOmittedPhysicalLiftSource_generatedState source
      rw [completeOmittedPhysicalLiftSource_generatedSupport, stateEq]
    _ = generatedVorticityNonlinearCoefficientAt source output := by
      change
        finiteStateVorticityNonlinearCoefficientAt
            (generatedCompleteNonlinearGalerkinModes source)
            (generatedComplexVorticityState source
              (generatedCompleteNonlinearGalerkinModes source))
            output =
          generatedVorticityNonlinearCoefficientAt source output
      exact
        finiteStateVorticityNonlinearCoefficientAt_generatedSource_of_subset
          source
          (generatedCompleteNonlinearGalerkinModes source)
          (generatedSupport_subset_completeNonlinearGalerkinModes source)
          output

/-- The zero-filled installation does not manufacture a live Fourier row. -/
theorem generatedLiveVorticityModes_completeLift
    (source : RawVorticityFourierSource) :
    generatedLiveVorticityModes
        (completeOmittedPhysicalLiftSource source) =
      generatedLiveVorticityModes source := by
  ext wave
  constructor
  · intro liftLive
    have data :=
      (mem_generatedLiveVorticityModes_iff
        (completeOmittedPhysicalLiftSource source) wave).mp
        liftLive
    have coefficientNonzero :
        generatedVorticityCoefficient source wave ≠ 0 := by
      rw [←
        generatedVorticityCoefficient_completeOmittedPhysicalLiftSource]
      exact data.2
    have oldMem : wave ∈ generatedSupport source := by
      by_contra oldNotMem
      exact coefficientNonzero
        (generatedVorticityCoefficient_eq_zero_of_not_mem
          source oldNotMem)
    exact
      (mem_generatedLiveVorticityModes_iff source wave).mpr
        ⟨oldMem, coefficientNonzero⟩
  · intro oldLive
    have data :=
      (mem_generatedLiveVorticityModes_iff source wave).mp oldLive
    have completeMem :
        wave ∈ generatedCompleteNonlinearGalerkinModes source :=
      generatedSupport_subset_completeNonlinearGalerkinModes
        source data.1
    have liftMem :
        wave ∈ generatedSupport
          (completeOmittedPhysicalLiftSource source) := by
      rwa [completeOmittedPhysicalLiftSource_generatedSupport]
    exact
      (mem_generatedLiveVorticityModes_iff
        (completeOmittedPhysicalLiftSource source) wave).mpr
        ⟨liftMem, by
          rw [
            generatedVorticityCoefficient_completeOmittedPhysicalLiftSource]
          exact data.2⟩

theorem generatedCurrentLiveMaxShellSq?_completeLift
    (source : RawVorticityFourierSource) :
    generatedCurrentLiveMaxShellSq?
        (completeOmittedPhysicalLiftSource source) =
      generatedCurrentLiveMaxShellSq? source := by
  have liveShellsEq :
      generatedLiveVorticityShells
          (completeOmittedPhysicalLiftSource source) =
        generatedLiveVorticityShells source := by
    unfold generatedLiveVorticityShells
    rw [generatedLiveVorticityModes_completeLift]
  unfold generatedCurrentLiveMaxShellSq?
  rw [liveShellsEq]

/-!
## The support write cannot manufacture a new radial shell response

The complete lift adds only zero rows.  Since it preserves the nonlinear
coefficient table, the live table, and therefore the current maximal live
shell, every active outer row after the lift was already active before it.
-/

theorem generatedActiveOuterNonlinearModes_completeLift_subset
    (source : RawVorticityFourierSource) :
    generatedActiveOuterNonlinearModes
        (completeOmittedPhysicalLiftSource source) ⊆
      generatedActiveOuterNonlinearModes source := by
  intro output liftMem
  unfold generatedActiveOuterNonlinearModes at liftMem ⊢
  rw [generatedCurrentLiveMaxShellSq?_completeLift] at liftMem
  cases currentMaxEq :
      generatedCurrentLiveMaxShellSq? source with
  | none =>
      rw [currentMaxEq] at liftMem
      simp at liftMem
  | some currentMax =>
      rw [currentMaxEq] at liftMem
      simp only [Finset.mem_filter] at liftMem ⊢
      have oldCoefficientNonzero :
          generatedVorticityNonlinearCoefficientAt source output ≠ 0 := by
        rw [←
          generatedVorticityNonlinearCoefficientAt_completeLift]
        exact liftMem.2.2.2.2
      have oldInventory :
          output ∈ generatedStretchingOutputInventory source := by
        by_contra outputNotInventory
        exact oldCoefficientNonzero
          (generatedVorticityNonlinearCoefficientAt_eq_zero_of_not_mem
            source outputNotInventory)
      have oldNotLive :
          output ∉ generatedLiveVorticityModes source := by
        rw [← generatedLiveVorticityModes_completeLift]
        exact liftMem.2.2.1
      exact
        ⟨oldInventory, liftMem.2.1, oldNotLive,
          liftMem.2.2.2.1, oldCoefficientNonzero⟩

/--
If the old radial responder was stopped, the conservative complete-support
write is followed directly by the time branch.  A support event cannot
silently reopen the shell grammar.
-/
theorem generatedIntegerShellRespond_completeLift_eq_none_of_none
    (source : RawVorticityFourierSource)
    (stopped :
      generatedIntegerShellRespond source = none) :
    generatedIntegerShellRespond
        (completeOmittedPhysicalLiftSource source) =
      none := by
  apply
    (generatedIntegerShellRespond_eq_none_iff
      (completeOmittedPhysicalLiftSource source)).mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro output liftMem
  have oldMem :
      output ∈ generatedActiveOuterNonlinearModes source :=
    generatedActiveOuterNonlinearModes_completeLift_subset
      source liftMem
  have oldEmpty :
      generatedActiveOuterNonlinearModes source = ∅ :=
    (generatedIntegerShellRespond_eq_none_iff source).mp stopped
  rw [oldEmpty] at oldMem
  simp at oldMem

/-! ## Exact support closure -/

/--
The one source-owned installation closes every genuinely missing nonlinear
coordinate at the same physical event.
-/
@[simp] theorem generatedMissingNonlinearModes_completeLift
    (source : RawVorticityFourierSource) :
    generatedMissingNonlinearModes
        (completeOmittedPhysicalLiftSource source) =
      ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro output liftMissing
  have liftData :=
    (mem_generatedMissingNonlinearModes_iff
      (completeOmittedPhysicalLiftSource source) output).mp
      liftMissing
  have liftActiveData :=
    (mem_generatedActiveNonliveNonlinearModes_iff
      (completeOmittedPhysicalLiftSource source) output).mp
      liftData.1
  have outputNotOldSupport :
      output ∉ generatedSupport source := by
    intro oldMem
    apply liftData.2
    rw [completeOmittedPhysicalLiftSource_generatedSupport]
    exact
      generatedSupport_subset_completeNonlinearGalerkinModes
        source oldMem
  have sourceCoefficientNonzero :
      generatedVorticityNonlinearCoefficientAt source output ≠ 0 := by
    rw [← generatedVorticityNonlinearCoefficientAt_completeLift]
    exact liftActiveData.2.2.2
  have sourceInventory :
      output ∈ generatedStretchingOutputInventory source := by
    by_contra outputNotInventory
    exact sourceCoefficientNonzero
      (generatedVorticityNonlinearCoefficientAt_eq_zero_of_not_mem
        source outputNotInventory)
  have sourceNotLive :
      output ∉ generatedLiveVorticityModes source := by
    rw [← generatedLiveVorticityModes_completeLift]
    exact liftActiveData.2.2.1
  have sourceActive :
      output ∈ generatedActiveNonliveNonlinearModes source :=
    (mem_generatedActiveNonliveNonlinearModes_iff
      source output).mpr
      ⟨sourceInventory, liftActiveData.2.1,
        sourceNotLive, sourceCoefficientNonzero⟩
  have sourceMissing :
      output ∈ generatedMissingNonlinearModes source :=
    (mem_generatedMissingNonlinearModes_iff
      source output).mpr
      ⟨sourceActive, outputNotOldSupport⟩
  apply liftData.2
  rw [completeOmittedPhysicalLiftSource_generatedSupport]
  exact
    generatedMissingNonlinearModes_subset_completeGalerkinModes
      source sourceMissing

/--
Narrow native-successor checkpoint: the physical state and old `q` table are
preserved while the genuinely missing support becomes empty.
-/
theorem completeOmittedNativeSuccessor_checkpoint
    (source : RawVorticityFourierSource) :
    generatedComplexVorticityState
        (completeOmittedPhysicalLiftSource source)
        (generatedSupport (completeOmittedPhysicalLiftSource source)) =
      generatedComplexVorticityState source
        (generatedSupport source) ∧
    (∀ output,
      generatedVorticityNonlinearCoefficientAt
          (completeOmittedPhysicalLiftSource source) output =
        generatedVorticityNonlinearCoefficientAt source output) ∧
    generatedMissingNonlinearModes
        (completeOmittedPhysicalLiftSource source) =
      ∅ := by
  exact
    ⟨(completeOmittedPhysicalLiftSource_generatedState source).trans
        (generatedCompleteNonlinearInitialState_eq_currentPhysicalState
          source),
      generatedVorticityNonlinearCoefficientAt_completeLift source,
      generatedMissingNonlinearModes_completeLift source⟩

end

end
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedNativeSuccessor
end NavierStokes
end SaturationMonoid
