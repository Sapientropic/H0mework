import H0mework.NavierStokes.ShellSources.Source

/-!
# Finite source-generated integer-shell paths

This module turns the source-owned integer-shell responder into a
proof-relevant finite path with quantitative shell growth.  Every successful
response retains its literal current source, dependent next source, native
step, producer equality, selected whole shell, and the exact live-mode
write-back law.

The chronological shell and receipt lists are computed by recursion on
`GeneratedIntegerShellReachable`; callers supply neither a list nor its
length.  Selected shells are pairwise strictly increasing, so the generated
path has no repeated shell.  This remains a source grammar theorem, not a
Navier--Stokes time evolution or a PDE regularity estimate.
-/

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath

open SourceGeneratedNativeResponseDisposition
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientNonlinearPairGenerator
open ThreeDimensionalVorticityCoefficientGeneratedIntegerShellSource

noncomputable section

private theorem liveModes_extendByGeneratedNonlinearShell
    (source : RawVorticityFourierSource)
    (shellSq : ℤ) :
    generatedLiveVorticityModes
        (extendByGeneratedNonlinearShell source shellSq) =
      generatedLiveVorticityModes source ∪
        generatedOuterNonlinearShellModes source shellSq := by
  classical
  ext wave
  rw [mem_generatedLiveVorticityModes_iff,
    extendByGeneratedNonlinearShell_generatedSupport,
    extendByGeneratedNonlinearShell_activeModes,
    generatedVorticityCoefficient_extendByGeneratedNonlinearShell]
  simp only [Finset.mem_union, mem_generatedLiveVorticityModes_iff]
  by_cases shellMembership :
      wave ∈ generatedOuterNonlinearShellModes source shellSq
  · have nonlinearNonzero :
        generatedVorticityNonlinearCoefficientAt source wave ≠ 0 := by
      have outerMembership :
          wave ∈ generatedActiveOuterNonlinearModes source :=
        ((mem_generatedOuterNonlinearShellModes_iff
          source shellSq wave).mp shellMembership).1
      unfold generatedActiveOuterNonlinearModes at outerMembership
      split at outerMembership
      · simp at outerMembership
      · exact
          (Finset.mem_filter.mp outerMembership).2.2.2.2
    simp [generatedNonlinearShellWriteRow, shellMembership,
      nonlinearNonzero]
  · simp [generatedNonlinearShellWriteRow, shellMembership]

private theorem liveModes_disjoint_outerNonlinearShell
    (source : RawVorticityFourierSource)
    (shellSq : ℤ) :
    Disjoint
      (generatedLiveVorticityModes source)
      (generatedOuterNonlinearShellModes source shellSq) := by
  classical
  rw [Finset.disjoint_left]
  intro wave live shellMembership
  have outerMembership :
      wave ∈ generatedActiveOuterNonlinearModes source :=
    ((mem_generatedOuterNonlinearShellModes_iff
      source shellSq wave).mp shellMembership).1
  unfold generatedActiveOuterNonlinearModes at outerMembership
  split at outerMembership
  · simp at outerMembership
  · exact
      (Finset.mem_filter.mp outerMembership).2.2.1 live

/-! ## One exact source-owned response receipt -/

/--
One literal successful response.  The dependent response fixes its next
source and native edge; `generated` proves that the current source actually
selected this response.
-/
structure GeneratedIntegerShellReceipt where
  current : RawVorticityFourierSource
  response : Response GeneratedIntegerShellStep current
  generated :
    generatedIntegerShellRespond current = some response

namespace GeneratedIntegerShellReceipt

/-- Exact next source carried by the dependent response. -/
abbrev next
    (receipt : GeneratedIntegerShellReceipt) :
    RawVorticityFourierSource :=
  receipt.response.1

/-- Exact native edge carried by the dependent response. -/
abbrev step
    (receipt : GeneratedIntegerShellReceipt) :
    GeneratedIntegerShellStep receipt.current receipt.next :=
  receipt.response.2

/-- Squared integer shell selected by this source response. -/
def selectedShellSq
    (receipt : GeneratedIntegerShellReceipt) : ℤ :=
  receipt.step.shellSq

/-- Complete source-generated output modes on the selected shell. -/
def wholeShellModes
    (receipt : GeneratedIntegerShellReceipt) :
    Finset IntegerWavevector :=
  generatedOuterNonlinearShellModes
    receipt.current receipt.selectedShellSq

/-- The receipt's native edge ends at the canonical whole-shell extension. -/
theorem next_eq_extension
    (receipt : GeneratedIntegerShellReceipt) :
    receipt.next =
      extendByGeneratedNonlinearShell
        receipt.current receipt.selectedShellSq := by
  rcases receipt with ⟨current, ⟨next, step⟩, generated⟩
  cases step
  rfl

/-- The selected shell is the literal output of the source-owned selector. -/
theorem selectedShell
    (receipt : GeneratedIntegerShellReceipt) :
    generatedNextOuterNonlinearShellSq? receipt.current =
      some receipt.selectedShellSq :=
  generatedIntegerShellRespond_selectedShell
    receipt.current receipt.response receipt.generated

/-- A successful response selects a genuinely inhabited whole output shell. -/
theorem wholeShellModes_nonempty
    (receipt : GeneratedIntegerShellReceipt) :
    receipt.wholeShellModes.Nonempty := by
  rcases
      exists_outer_mode_of_generatedNextOuterNonlinearShellSq?_eq_some
        receipt.current receipt.selectedShellSq receipt.selectedShell with
    ⟨output, outputOuter, outputShell⟩
  exact
    ⟨output,
      (mem_generatedOuterNonlinearShellModes_iff
        receipt.current receipt.selectedShellSq output).mpr
        ⟨outputOuter, outputShell⟩⟩

/-- The source current has an actual live maximum strictly below the selected
shell. -/
theorem currentMax_lt_selectedShell
    (receipt : GeneratedIntegerShellReceipt) :
    ∃ currentMax : ℤ,
      generatedCurrentLiveMaxShellSq? receipt.current =
          some currentMax ∧
        currentMax < receipt.selectedShellSq := by
  rcases
      generatedIntegerShellRespond_shellGap
        receipt.current receipt.response receipt.generated with
    ⟨currentMax, currentMax_eq, gap⟩
  refine ⟨currentMax, currentMax_eq, ?_⟩
  change currentMax < receipt.response.2.shellSq
  omega

/-- Exact live-mode write-back: no old live row disappears and the only new
live rows are the complete selected-shell rows. -/
theorem liveModes_next
    (receipt : GeneratedIntegerShellReceipt) :
    generatedLiveVorticityModes receipt.next =
      generatedLiveVorticityModes receipt.current ∪
        receipt.wholeShellModes := by
  rw [receipt.next_eq_extension]
  exact
    liveModes_extendByGeneratedNonlinearShell
      receipt.current receipt.selectedShellSq

/-- The newly selected whole shell is disjoint from the old live carrier. -/
theorem liveModes_disjoint_wholeShell
    (receipt : GeneratedIntegerShellReceipt) :
    Disjoint
      (generatedLiveVorticityModes receipt.current)
      receipt.wholeShellModes :=
  liveModes_disjoint_outerNonlinearShell
    receipt.current receipt.selectedShellSq

/-- Exact live-shell write-back for one successful response. -/
theorem liveShells_next
    (receipt : GeneratedIntegerShellReceipt) :
    generatedLiveVorticityShells receipt.next =
      generatedLiveVorticityShells receipt.current ∪
        {receipt.selectedShellSq} := by
  classical
  have shellImage :
      receipt.wholeShellModes.image integerWaveShellSq =
        {receipt.selectedShellSq} := by
    ext shellSq
    constructor
    · intro membership
      rcases Finset.mem_image.mp membership with
        ⟨wave, waveMembership, waveShell⟩
      have selected :
          integerWaveShellSq wave = receipt.selectedShellSq :=
        ((mem_generatedOuterNonlinearShellModes_iff
          receipt.current receipt.selectedShellSq wave).mp
          waveMembership).2
      rw [← waveShell, selected]
      simp
    · intro membership
      have shellEquality :
          shellSq = receipt.selectedShellSq := by
        simpa using membership
      subst shellSq
      rcases receipt.wholeShellModes_nonempty with
        ⟨wave, waveMembership⟩
      exact Finset.mem_image.mpr
        ⟨wave, waveMembership,
          ((mem_generatedOuterNonlinearShellModes_iff
            receipt.current receipt.selectedShellSq wave).mp
            waveMembership).2⟩
  unfold generatedLiveVorticityShells
  rw [receipt.liveModes_next, Finset.image_union, shellImage]

/-- After a successful response, the new live maximum is exactly the selected
shell. -/
theorem currentLiveMaxShellSq_next
    (receipt : GeneratedIntegerShellReceipt) :
    generatedCurrentLiveMaxShellSq? receipt.next =
      some receipt.selectedShellSq := by
  classical
  rcases receipt.currentMax_lt_selectedShell with
    ⟨currentMax, currentMax_eq, currentMax_lt⟩
  have oldShellsNonempty :
      (generatedLiveVorticityShells receipt.current).Nonempty := by
    by_contra shellsEmpty
    simp [generatedCurrentLiveMaxShellSq?, shellsEmpty] at currentMax_eq
  have oldMax_eq :
      (generatedLiveVorticityShells receipt.current).max'
          oldShellsNonempty =
        currentMax := by
    have optionEquality :
        some
            ((generatedLiveVorticityShells receipt.current).max'
              oldShellsNonempty) =
          some currentMax := by
      simpa [generatedCurrentLiveMaxShellSq?,
        oldShellsNonempty] using currentMax_eq
    exact Option.some.inj optionEquality
  have newShellsNonempty :
      (generatedLiveVorticityShells receipt.current ∪
        {receipt.selectedShellSq}).Nonempty := by
    simp
  unfold generatedCurrentLiveMaxShellSq?
  rw [receipt.liveShells_next]
  simp only [dif_pos newShellsNonempty, Option.some.injEq]
  apply
    (Finset.max'_eq_iff
      (generatedLiveVorticityShells receipt.current ∪
        {receipt.selectedShellSq})
      newShellsNonempty receipt.selectedShellSq).mpr
  constructor
  · simp
  · intro shellSq shellMembership
    simp only [Finset.mem_union, Finset.mem_singleton] at shellMembership
    rcases shellMembership with oldMembership | selectedEquality
    · have shell_le_currentMax :
          shellSq ≤ currentMax := by
        rw [← oldMax_eq]
        exact
          Finset.le_max'
            (generatedLiveVorticityShells receipt.current)
            shellSq oldMembership
      omega
    · omega

end GeneratedIntegerShellReceipt

/-! ## Chronological receipts generated by finite reachability -/

/-- Selected shells in chronological source order. -/
def generatedIntegerShellReachableShells
    {seed current : RawVorticityFourierSource} :
    GeneratedIntegerShellReachable seed current → List ℤ
  | .initial => []
  | @NativeReachable.step _ _ _ _ _ arrival response _ =>
      (generatedIntegerShellReachableShells arrival).concat
        response.2.shellSq

/-- Exact source-owned response receipts in chronological order. -/
def generatedIntegerShellReachableReceipts
    {seed current : RawVorticityFourierSource} :
    GeneratedIntegerShellReachable seed current →
      List GeneratedIntegerShellReceipt
  | .initial => []
  | @NativeReachable.step _ _ _ _ prior arrival response generated =>
      (generatedIntegerShellReachableReceipts arrival).concat
        ⟨prior, response, generated⟩

@[simp] theorem generatedIntegerShellReachableShells_step
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    generatedIntegerShellReachableShells
        (NativeReachable.step arrival generated) =
      (generatedIntegerShellReachableShells arrival).concat
        response.2.shellSq :=
  rfl

@[simp] theorem generatedIntegerShellReachableReceipts_step
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    (response : Response GeneratedIntegerShellStep current)
    (generated :
      generatedIntegerShellRespond current = some response) :
    generatedIntegerShellReachableReceipts
        (NativeReachable.step arrival generated) =
      (generatedIntegerShellReachableReceipts arrival).concat
        ⟨current, response, generated⟩ :=
  rfl

/-- The shell trace has exactly one entry per actual successful response. -/
@[simp] theorem generatedIntegerShellReachableShells_length
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableShells arrival).length =
      arrival.occurrence := by
  induction arrival with
  | initial =>
      rfl
  | step arrival generated inductionHypothesis =>
      simp [generatedIntegerShellReachableShells,
        NativeReachable.occurrence, inductionHypothesis]

/-- The receipt trace has exactly one row per actual successful response. -/
@[simp] theorem generatedIntegerShellReachableReceipts_length
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableReceipts arrival).length =
      arrival.occurrence := by
  induction arrival with
  | initial =>
      rfl
  | step arrival generated inductionHypothesis =>
      simp [generatedIntegerShellReachableReceipts,
        NativeReachable.occurrence, inductionHypothesis]

/-- Mapping each exact receipt to its selected shell recovers the shell trace. -/
theorem generatedIntegerShellReachableReceipts_map_selectedShellSq
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableReceipts arrival).map
        GeneratedIntegerShellReceipt.selectedShellSq =
      generatedIntegerShellReachableShells arrival := by
  induction arrival with
  | initial =>
      rfl
  | step arrival generated inductionHypothesis =>
      simp [generatedIntegerShellReachableReceipts,
        generatedIntegerShellReachableShells,
        inductionHypothesis,
        GeneratedIntegerShellReceipt.selectedShellSq,
        GeneratedIntegerShellReceipt.step]

private theorem generatedIntegerShellReachableShell_le_currentMax
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current)
    {currentMax shellSq : ℤ}
    (currentMax_eq :
      generatedCurrentLiveMaxShellSq? current = some currentMax)
    (shellMembership :
      shellSq ∈ generatedIntegerShellReachableShells arrival) :
    shellSq ≤ currentMax := by
  induction arrival generalizing currentMax shellSq with
  | initial =>
      simp [generatedIntegerShellReachableShells] at shellMembership
  | @step prior arrival response generated inductionHypothesis =>
      let receipt : GeneratedIntegerShellReceipt :=
        ⟨prior, response, generated⟩
      have nextMax :
          generatedCurrentLiveMaxShellSq? response.1 =
            some receipt.selectedShellSq :=
        receipt.currentLiveMaxShellSq_next
      have currentMax_eq_selected :
          currentMax = receipt.selectedShellSq := by
        rw [currentMax_eq] at nextMax
        exact Option.some.inj nextMax
      rw [currentMax_eq_selected]
      rw [generatedIntegerShellReachableShells_step
        arrival response generated,
        List.concat_eq_append] at shellMembership
      simp only [List.mem_append, List.mem_singleton] at shellMembership
      rcases shellMembership with priorMembership | selectedEquality
      · rcases receipt.currentMax_lt_selectedShell with
          ⟨priorMax, priorMax_eq, priorMax_lt⟩
        have shell_le_priorMax :
            shellSq ≤ priorMax :=
          inductionHypothesis priorMax_eq priorMembership
        omega
      · subst shellSq
        change response.2.shellSq ≤ response.2.shellSq
        exact le_rfl

/-- Selected response shells are strictly increasing along every actual
finite generated path. -/
theorem generatedIntegerShellReachableShells_pairwise_lt
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableShells arrival).Pairwise (· < ·) := by
  induction arrival with
  | initial =>
      exact List.Pairwise.nil
  | @step prior arrival response generated inductionHypothesis =>
      let receipt : GeneratedIntegerShellReceipt :=
        ⟨prior, response, generated⟩
      rw [generatedIntegerShellReachableShells_step,
        List.concat_eq_append, List.pairwise_append]
      refine ⟨inductionHypothesis, by simp, ?_⟩
      intro shellSq shellMembership selectedShell selectedMembership
      simp only [List.mem_singleton] at selectedMembership
      subst selectedShell
      rcases receipt.currentMax_lt_selectedShell with
        ⟨currentMax, currentMax_eq, currentMax_lt⟩
      exact lt_of_le_of_lt
        (generatedIntegerShellReachableShell_le_currentMax
          arrival currentMax_eq shellMembership)
        currentMax_lt

/-- Strict shell growth makes the generated shell trace duplicate-free. -/
theorem generatedIntegerShellReachableShells_nodup
    {seed current : RawVorticityFourierSource}
    (arrival : GeneratedIntegerShellReachable seed current) :
    (generatedIntegerShellReachableShells arrival).Nodup :=
  (generatedIntegerShellReachableShells_pairwise_lt arrival).nodup

end

end ThreeDimensionalVorticityCoefficientGeneratedIntegerShellPath
end NavierStokes
end SaturationMonoid
