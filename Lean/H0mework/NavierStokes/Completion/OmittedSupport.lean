import H0mework.NavierStokes.InitialData.FiniteSupportComplexTrajectory
import H0mework.NavierStokes.ShellSources.Source
import H0mework.NavierStokes.Fourier.NonlinearOutputCompiler

/-!
# Complete source-owned nonlinear responsibility support in three dimensions

The outer-shell responder is deliberately radial.  It can therefore miss a
nonzero nonlinear output on an already represented shell or in an interior
hole.  This module computes the complete responsibility inventory before any
cross-event Fourier aggregation:

```text
complete generated output fiber
→ nonzero output outside the live coefficient table
→ already owned dormant coordinate | genuinely missing coordinate.
```

The distinction between `generatedLiveVorticityModes` and
`generatedSupport` is essential.  A zero coefficient may already belong to
the Galerkin carrier.  Such a row needs no second support installation: its
actual finite-dimensional tangent can consume the generated nonlinear row
directly.  Only a row outside `generatedSupport` is installed.

No occurrence norm is introduced.  The finite sets are computed from the
actual source pair table and coefficient aggregation; callers supply neither
an output, a branch, a nonzero witness, nor a target.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingOutputCarrier
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientNonlinearOutputCompiler
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource

noncomputable section

/-! ## Complete generated responsibility inventory -/

/--
Every nonzero nonlinear output which has not yet become a nonzero physical
Fourier row.  This includes radial outer rows, interior holes, and dormant
coordinates already owned by the current Galerkin carrier.
-/
def generatedActiveNonliveNonlinearModes
    (source : RawVorticityFourierSource) :
    Finset IntegerWavevector := by
  classical
  exact
    (generatedStretchingOutputInventory source).filter fun output =>
      output ≠ 0 ∧
        output ∉ generatedLiveVorticityModes source ∧
        generatedVorticityNonlinearCoefficientAt source output ≠ 0

@[simp] theorem mem_generatedActiveNonliveNonlinearModes_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    output ∈ generatedActiveNonliveNonlinearModes source ↔
      output ∈ generatedStretchingOutputInventory source ∧
        output ≠ 0 ∧
        output ∉ generatedLiveVorticityModes source ∧
        generatedVorticityNonlinearCoefficientAt source output ≠ 0 := by
  simp [generatedActiveNonliveNonlinearModes]

@[simp] theorem
    mem_generatedActiveNonliveNonlinearModes_waveNeg_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    waveNeg output ∈ generatedActiveNonliveNonlinearModes source ↔
      output ∈ generatedActiveNonliveNonlinearModes source := by
  rw [mem_generatedActiveNonliveNonlinearModes_iff,
    mem_generatedActiveNonliveNonlinearModes_iff,
    mem_generatedStretchingOutputInventory_waveNeg_iff,
    mem_generatedLiveVorticityModes_waveNeg_iff,
    generatedVorticityNonlinearCoefficientAt_waveNeg]
  constructor
  · rintro ⟨inventory, nonzero, notLive, conjugateNonzero⟩
    have outputNonzero : output ≠ 0 := by
      simpa using nonzero
    refine ⟨inventory, outputNonzero, notLive, ?_⟩
    intro coefficientZero
    apply conjugateNonzero
    rw [coefficientZero, vectorConj_zero]
  · rintro ⟨inventory, nonzero, notLive, coefficientNonzero⟩
    have negOutputNonzero : waveNeg output ≠ 0 := by
      simpa using nonzero
    refine ⟨inventory, negOutputNonzero, notLive, ?_⟩
    intro conjugateZero
    apply coefficientNonzero
    have := congrArg vectorConj conjugateZero
    simpa using this

@[simp] theorem zero_not_mem_generatedActiveNonliveNonlinearModes
    (source : RawVorticityFourierSource) :
    0 ∉ generatedActiveNonliveNonlinearModes source := by
  simp [generatedActiveNonliveNonlinearModes]

/--
The genuinely missing part of the responsibility inventory.  These and only
these coordinates require a conservative zero-filled carrier expansion.
-/
def generatedMissingNonlinearModes
    (source : RawVorticityFourierSource) :
    Finset IntegerWavevector :=
  (generatedActiveNonliveNonlinearModes source).filter fun output =>
    output ∉ generatedSupport source

/--
The already owned dormant part.  Its coefficients vanish, but its coordinates
already belong to the current Galerkin carrier.
-/
def generatedOwnedDormantNonlinearModes
    (source : RawVorticityFourierSource) :
    Finset IntegerWavevector :=
  (generatedActiveNonliveNonlinearModes source).filter fun output =>
    output ∈ generatedSupport source

@[simp] theorem mem_generatedMissingNonlinearModes_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    output ∈ generatedMissingNonlinearModes source ↔
      output ∈ generatedActiveNonliveNonlinearModes source ∧
        output ∉ generatedSupport source := by
  simp [generatedMissingNonlinearModes]

@[simp] theorem mem_generatedOwnedDormantNonlinearModes_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    output ∈ generatedOwnedDormantNonlinearModes source ↔
      output ∈ generatedActiveNonliveNonlinearModes source ∧
        output ∈ generatedSupport source := by
  simp [generatedOwnedDormantNonlinearModes]

@[simp] theorem mem_generatedMissingNonlinearModes_waveNeg_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    waveNeg output ∈ generatedMissingNonlinearModes source ↔
      output ∈ generatedMissingNonlinearModes source := by
  rw [mem_generatedMissingNonlinearModes_iff,
    mem_generatedMissingNonlinearModes_iff,
    mem_generatedActiveNonliveNonlinearModes_waveNeg_iff,
    mem_generatedSupport_waveNeg_iff]

@[simp] theorem
    mem_generatedOwnedDormantNonlinearModes_waveNeg_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    waveNeg output ∈ generatedOwnedDormantNonlinearModes source ↔
      output ∈ generatedOwnedDormantNonlinearModes source := by
  rw [mem_generatedOwnedDormantNonlinearModes_iff,
    mem_generatedOwnedDormantNonlinearModes_iff,
    mem_generatedActiveNonliveNonlinearModes_waveNeg_iff,
    mem_generatedSupport_waveNeg_iff]

@[simp] theorem zero_not_mem_generatedMissingNonlinearModes
    (source : RawVorticityFourierSource) :
    0 ∉ generatedMissingNonlinearModes source := by
  simp [generatedMissingNonlinearModes]

@[simp] theorem zero_not_mem_generatedOwnedDormantNonlinearModes
    (source : RawVorticityFourierSource) :
    0 ∉ generatedOwnedDormantNonlinearModes source := by
  simp [generatedOwnedDormantNonlinearModes]

/-- Every active nonlive output is assigned to exactly one carrier branch. -/
theorem generatedActiveNonliveNonlinearModes_partition
    (source : RawVorticityFourierSource) :
    generatedOwnedDormantNonlinearModes source ∪
        generatedMissingNonlinearModes source =
      generatedActiveNonliveNonlinearModes source := by
  ext output
  by_cases supportMem : output ∈ generatedSupport source <;>
    simp [supportMem]

theorem generatedOwnedDormantNonlinearModes_disjoint_missing
    (source : RawVorticityFourierSource) :
    Disjoint
      (generatedOwnedDormantNonlinearModes source)
      (generatedMissingNonlinearModes source) := by
  exact Finset.disjoint_left.mpr fun output owned missing =>
    ((mem_generatedMissingNonlinearModes_iff source output).mp missing).2
      ((mem_generatedOwnedDormantNonlinearModes_iff
        source output).mp owned).2

/-- The old radial outer producer remains a literal subfamily of the complete
source-owned responsibility inventory. -/
theorem generatedActiveOuterNonlinearModes_subset_activeNonlive
    (source : RawVorticityFourierSource) :
    generatedActiveOuterNonlinearModes source ⊆
      generatedActiveNonliveNonlinearModes source := by
  intro output outputMem
  unfold generatedActiveOuterNonlinearModes at outputMem
  split at outputMem
  · simp at outputMem
  · have data := Finset.mem_filter.mp outputMem
    exact
      (mem_generatedActiveNonliveNonlinearModes_iff
        source output).mpr
        ⟨data.1, data.2.1, data.2.2.1, data.2.2.2.2⟩

/-! ## The one conservative complete carrier -/

/--
Install every genuinely missing responsibility coordinate in one finite
Galerkin carrier.  Already owned dormant rows are retained exactly once.
-/
def generatedCompleteNonlinearGalerkinModes
    (source : RawVorticityFourierSource) :
    Finset IntegerWavevector :=
  generatedSupport source ∪ generatedMissingNonlinearModes source

theorem generatedSupport_subset_completeNonlinearGalerkinModes
    (source : RawVorticityFourierSource) :
    generatedSupport source ⊆
      generatedCompleteNonlinearGalerkinModes source :=
  Finset.subset_union_left

theorem generatedMissingNonlinearModes_subset_completeGalerkinModes
    (source : RawVorticityFourierSource) :
    generatedMissingNonlinearModes source ⊆
      generatedCompleteNonlinearGalerkinModes source :=
  Finset.subset_union_right

/-- Every active responsibility is owned by the complete carrier before any
cross-event coefficient quotient is formed. -/
theorem generatedActiveNonliveNonlinearModes_subset_completeGalerkinModes
    (source : RawVorticityFourierSource) :
    generatedActiveNonliveNonlinearModes source ⊆
      generatedCompleteNonlinearGalerkinModes source := by
  intro output outputMem
  by_cases supportMem : output ∈ generatedSupport source
  · exact Finset.mem_union_left _ supportMem
  · exact Finset.mem_union_right _
      ((mem_generatedMissingNonlinearModes_iff
        source output).mpr ⟨outputMem, supportMem⟩)

@[simp] theorem mem_completeNonlinearGalerkinModes_waveNeg_iff
    (source : RawVorticityFourierSource)
    (output : IntegerWavevector) :
    waveNeg output ∈ generatedCompleteNonlinearGalerkinModes source ↔
      output ∈ generatedCompleteNonlinearGalerkinModes source := by
  rw [generatedCompleteNonlinearGalerkinModes]
  simp only [Finset.mem_union,
    mem_generatedSupport_waveNeg_iff,
    mem_generatedMissingNonlinearModes_waveNeg_iff]

@[simp] theorem zero_not_mem_completeNonlinearGalerkinModes
    (source : RawVorticityFourierSource) :
    0 ∉ generatedCompleteNonlinearGalerkinModes source := by
  simp [generatedCompleteNonlinearGalerkinModes]

/-- Ambient initial state on the complete carrier.  Newly installed rows are
zero because the source has no coefficient there. -/
def generatedCompleteNonlinearInitialState
    (source : RawVorticityFourierSource) :
    ComplexVorticityHilbertState :=
  generatedComplexVorticityState source
    (generatedCompleteNonlinearGalerkinModes source)

/-- Installing the complete missing carrier does not change the physical
initial state anywhere in the ambient Hilbert carrier. -/
theorem generatedCompleteNonlinearInitialState_eq_currentPhysicalState
    (source : RawVorticityFourierSource) :
    generatedCompleteNonlinearInitialState source =
      generatedComplexVorticityState source
        (generatedSupport source) := by
  exact
    generatedComplexVorticityState_eq_generatedSupport_of_subset
      source
      (generatedCompleteNonlinearGalerkinModes source)
      (generatedSupport_subset_completeNonlinearGalerkinModes source)

/-- Every source-generated active nonlive row begins at zero on the complete
physical carrier, whether it was dormant-owned or newly installed. -/
theorem generatedCompleteNonlinearInitialState_activeNonlive_zero
    (source : RawVorticityFourierSource)
    {output : IntegerWavevector}
    (outputMem :
      output ∈ generatedActiveNonliveNonlinearModes source) :
    generatedCompleteNonlinearInitialState source output = 0 := by
  rw [generatedCompleteNonlinearInitialState_eq_currentPhysicalState]
  have outputNotLive :
      output ∉ generatedLiveVorticityModes source :=
    ((mem_generatedActiveNonliveNonlinearModes_iff
      source output).mp outputMem).2.2.1
  rw [generatedComplexVorticityState_apply]
  by_cases supportMem : output ∈ generatedSupport source
  · rw [if_pos supportMem]
    by_contra coefficientNonzero
    exact outputNotLive
      ((mem_generatedLiveVorticityModes_iff source output).mpr
        ⟨supportMem, coefficientNonzero⟩)
  · rw [if_neg supportMem]

end

end
    ThreeDimensionalVorticityCoefficientGeneratedCompleteOmittedSupport
end NavierStokes
end SaturationMonoid
