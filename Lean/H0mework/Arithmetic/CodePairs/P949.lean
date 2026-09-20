import H0mework.Arithmetic.CodePairs.P948

/-!
# Proposition 949: gauge-filtered generated spectra

P948 showed that unit descent over the full raw endpoint-code space is false.
The missing producer must therefore be a SU(7) allowed-sector filter.

This file builds that interface explicitly.  A Boolean allowed predicate on
raw endpoint codes filters the generated Boolean-atomic raw branch cells before
the spectrum is formed.  Unit descent on the filtered raw code-pair sector then
forbids unit permanent holonomy in the filtered generated spectrum.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open SaturationMonoid.AffineRelaxation
open RunningSigmaBeta

set_option linter.defProp false

/-! ## Generic Boolean-atomic spectrum from a list -/

/-- Forget a Boolean-atomic raw branch-cell list to the raw branching spectrum
used by P921/P922. -/
def rawBranchingSpectrum_of_booleanAtomicCells
    {n : ℕ} (xs : List (SU7BooleanAtomicRawBranchingCell n)) :
    SU7BranchingDecompositionSpectrum n :=
  rawBranchingSpectrum_of_certifiedCells
    (certifiedRawBranchingCells_of_atomicRawBranchingCells
      (atomicRawBranchingCells_of_booleanAtomicCells xs))

/-- A Boolean-atomic generated cell appears in the spectrum forgotten from
the same Boolean-atomic list. -/
theorem booleanAtomicCell_mem_rawBranchingSpectrum_of_booleanAtomicCells
    {n : ℕ} {xs : List (SU7BooleanAtomicRawBranchingCell n)}
    {x : SU7BooleanAtomicRawBranchingCell n}
    (hx : x ∈ xs) :
    x.cell ∈ (rawBranchingSpectrum_of_booleanAtomicCells xs).cells := by
  unfold rawBranchingSpectrum_of_booleanAtomicCells
  unfold rawBranchingSpectrum_of_certifiedCells
  unfold certifiedRawBranchingCells_of_atomicRawBranchingCells
  unfold atomicRawBranchingCells_of_booleanAtomicCells
  exact
    List.mem_map.mpr
      ⟨certifiedRawBranchingCell_of_atomicRawBranchingCell
          (atomicRawBranchingCell_of_booleanAtomicCell x),
        List.mem_map.mpr
          ⟨atomicRawBranchingCell_of_booleanAtomicCell x,
            List.mem_map.mpr ⟨x, hx, rfl⟩,
            rfl⟩,
        rfl⟩

/-- Every raw cell in the spectrum forgotten from a Boolean-atomic list comes
from a Boolean-atomic source cell in that list. -/
theorem exists_booleanAtomicCell_of_mem_rawBranchingSpectrum_of_booleanAtomicCells
    {n : ℕ} (xs : List (SU7BooleanAtomicRawBranchingCell n))
    {c : SU7BranchingDecompositionCell n}
    (hmem : c ∈ (rawBranchingSpectrum_of_booleanAtomicCells xs).cells) :
    ∃ x : SU7BooleanAtomicRawBranchingCell n,
      x ∈ xs ∧ x.cell = c := by
  unfold rawBranchingSpectrum_of_booleanAtomicCells at hmem
  rcases
      exists_certifiedCell_of_mem_rawBranchingSpectrum
        (certifiedRawBranchingCells_of_atomicRawBranchingCells
          (atomicRawBranchingCells_of_booleanAtomicCells xs))
        hmem with
    ⟨cert, hcert_mem, hcert_cell⟩
  rcases
      exists_atomicCell_of_mem_certifiedAtomicList
        (atomicRawBranchingCells_of_booleanAtomicCells xs)
        hcert_mem with
    ⟨atomic, hatomic_mem, hatomic_cert⟩
  rcases exists_booleanCell_of_mem_atomicBooleanList xs hatomic_mem with
    ⟨x, hx_mem, hx_atomic⟩
  subst cert
  subst atomic
  subst c
  exact ⟨x, hx_mem, rfl⟩

/-! ## Gauge-filtered generated spectrum -/

/-- Generated Boolean-atomic raw branch cells filtered by a Boolean SU(7)
allowed-sector predicate on endpoint codes. -/
def gaugeFilteredBooleanAtomicRawBranchingCandidateList
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) :
    List (SU7BooleanAtomicRawBranchingCell n) :=
  (booleanAtomicRawBranchingCandidateList n bound).filter
    (fun x => allowed x.cell.leftWeightCode x.cell.rightWeightCode)

/-- Raw spectrum generated from the gauge-filtered Boolean-atomic cell list. -/
def gaugeFilteredRawBranchingSpectrum
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) :
    SU7BranchingDecompositionSpectrum n :=
  rawBranchingSpectrum_of_booleanAtomicCells
    (gaugeFilteredBooleanAtomicRawBranchingCandidateList n bound allowed)

/-- A filtered Boolean-atomic cell appears in the filtered generated spectrum.
-/
theorem gaugeFilteredBooleanAtomicCell_mem_spectrum
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    {x : SU7BooleanAtomicRawBranchingCell n}
    (hx :
      x ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n bound allowed) :
    x.cell ∈ (gaugeFilteredRawBranchingSpectrum n bound allowed).cells :=
  booleanAtomicCell_mem_rawBranchingSpectrum_of_booleanAtomicCells hx

/-- Every raw cell in a filtered generated spectrum comes from a filtered
Boolean-atomic source cell. -/
theorem exists_gaugeFilteredBooleanAtomicCell_of_mem_spectrum
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    {c : SU7BranchingDecompositionCell n}
    (hmem : c ∈ (gaugeFilteredRawBranchingSpectrum n bound allowed).cells) :
    ∃ x : SU7BooleanAtomicRawBranchingCell n,
      x ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n bound allowed ∧
        x.cell = c :=
  exists_booleanAtomicCell_of_mem_rawBranchingSpectrum_of_booleanAtomicCells
    (gaugeFilteredBooleanAtomicRawBranchingCandidateList n bound allowed)
    hmem

/-! ## Endpoint bounds from generated Boolean cells -/

/-- A generated Boolean-atomic cell has its left endpoint code inside the
raw-code bound used by the generator. -/
theorem booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
    {n bound : ℕ} {x : SU7BooleanAtomicRawBranchingCell n}
    (hx : x ∈ booleanAtomicRawBranchingCandidateList n bound) :
    x.cell.leftWeightCode ∈ rawCodeBoundedList bound := by
  unfold booleanAtomicRawBranchingCandidateList at hx
  unfold booleanAtomicCellOfCandidate? at hx
  unfold rawBranchingCandidateCells at hx
  simp only [List.mem_filterMap] at hx
  rcases hx with ⟨c, hc_mem, hc_some⟩
  simp [rawCodeBoundedList] at hc_mem
  rcases hc_mem with
    ⟨branch, _hbranch, incidence, _hincidence,
      left, hleft_bound, right, _hright_bound, hc_eq⟩
  split at hc_some
  · split at hc_some
    · cases hc_some
      have hleft_eq : c.leftWeightCode = left := by
        exact
          (congrArg SU7BranchingDecompositionCell.leftWeightCode
            hc_eq).symm
      change c.leftWeightCode ∈ rawCodeBoundedList bound
      simpa [rawCodeBoundedList, hleft_eq] using hleft_bound
    · contradiction
  · contradiction

/-- A generated Boolean-atomic cell has its right endpoint code inside the
raw-code bound used by the generator. -/
theorem booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
    {n bound : ℕ} {x : SU7BooleanAtomicRawBranchingCell n}
    (hx : x ∈ booleanAtomicRawBranchingCandidateList n bound) :
    x.cell.rightWeightCode ∈ rawCodeBoundedList bound := by
  unfold booleanAtomicRawBranchingCandidateList at hx
  unfold booleanAtomicCellOfCandidate? at hx
  unfold rawBranchingCandidateCells at hx
  simp only [List.mem_filterMap] at hx
  rcases hx with ⟨c, hc_mem, hc_some⟩
  simp [rawCodeBoundedList] at hc_mem
  rcases hc_mem with
    ⟨branch, _hbranch, incidence, _hincidence,
      left, _hleft_bound, right, hright_bound, hc_eq⟩
  split at hc_some
  · split at hc_some
    · cases hc_some
      have hright_eq : c.rightWeightCode = right := by
        exact
          (congrArg SU7BranchingDecompositionCell.rightWeightCode
            hc_eq).symm
      change c.rightWeightCode ∈ rawCodeBoundedList bound
      simpa [rawCodeBoundedList, hright_eq] using hright_bound
    · contradiction
  · contradiction

/-! ## Filtered unit descent -/

/-- Unit descent on the filtered generated Boolean-cell sector. -/
def GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) : Prop :=
  ∀ x : SU7BooleanAtomicRawBranchingCell n,
    x ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
      n bound allowed ->
      rawAtomCodeBranchingDecompositionResidual x.cell ≠ 0 ->
        ∃ y : SU7BooleanAtomicRawBranchingCell n,
          y ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
            n bound allowed ∧
            rawAtomCodeBranchingDecompositionResidualEnergy y.cell + 1 =
              rawAtomCodeBranchingDecompositionResidualEnergy x.cell

/-- Executable information-face closure check for unit descent on the filtered
generated Boolean-cell grammar.

Unlike the coverage checker, this checks the successor law directly: every
nonzero residual cell in the filtered generated list must have an `E - 1`
successor in the same filtered list. -/
def gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) : Bool :=
  let xs :=
    gaugeFilteredBooleanAtomicRawBranchingCandidateList
      n bound allowed
  xs.all
    (fun x =>
      if rawAtomCodeBranchingDecompositionResidual x.cell = 0 then
        true
      else
        xs.any
          (fun y =>
            decide
              (rawAtomCodeBranchingDecompositionResidualEnergy y.cell + 1 =
                rawAtomCodeBranchingDecompositionResidualEnergy x.cell)))

/-- A successful finite grammar closure check produces the Boolean-cell
successor law itself, not merely coverage.

This is the information-face source interface: the finite checker certifies
that the generated allowed-sector grammar is closed under the `E - 1` unit
successor relation. -/
theorem gaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw_of_closureCheck
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (hcheck :
      gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck
        n bound allowed = true) :
    GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw n bound allowed := by
  intro x hxmem hnonzero
  unfold gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck at hcheck
  let xs :=
    gaugeFilteredBooleanAtomicRawBranchingCandidateList
      n bound allowed
  have hxall :
      (if rawAtomCodeBranchingDecompositionResidual x.cell = 0 then
          true
        else
          xs.any
            (fun y =>
              decide
                (rawAtomCodeBranchingDecompositionResidualEnergy y.cell + 1 =
                  rawAtomCodeBranchingDecompositionResidualEnergy x.cell))) =
        true := by
    exact (List.all_eq_true.mp hcheck) x hxmem
  rw [if_neg hnonzero] at hxall
  rcases List.any_eq_true.mp hxall with ⟨y, hymem, hyenergy⟩
  exact ⟨y, hymem, decide_eq_true_eq.mp hyenergy⟩

/-- Filtered Boolean-cell descent gives the unit successor law for the
filtered generated spectrum. -/
theorem gaugeFilteredSpectrumUnitSuccessorLaw_of_booleanAtomicLaw
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw
      n bound allowed) :
    SU7RawBranchingSpectrumUnitSuccessorLaw
      (gaugeFilteredRawBranchingSpectrum n bound allowed) := by
  intro c hmem hnonzero
  rcases exists_gaugeFilteredBooleanAtomicCell_of_mem_spectrum
      (n := n) (bound := bound) (allowed := allowed) hmem with
    ⟨x, hxmem, hxcell⟩
  rcases H x hxmem (by simpa [hxcell] using hnonzero) with
    ⟨y, hymem, hyenergy⟩
  refine ⟨y.cell, gaugeFilteredBooleanAtomicCell_mem_spectrum hymem, ?_⟩
  simpa [hxcell] using hyenergy

/-- Filtered Boolean-cell descent forbids unit permanent holonomy in the
filtered generated spectrum. -/
theorem gaugeFilteredForbidsUnitPermanentHolonomy_of_booleanAtomicLaw
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw
      n bound allowed) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound allowed) :=
  (noRawUnitPermanentHolonomy_iff_unitSuccessorLaw
    (gaugeFilteredRawBranchingSpectrum n bound allowed)).mpr
      (gaugeFilteredSpectrumUnitSuccessorLaw_of_booleanAtomicLaw H)

/-! ## Canonical filtered lift from raw endpoint codes -/

/-- Boolean-atomic branch cell produced by the canonical SU(7)
branch/incidence lift of one raw code pair. -/
def booleanAtomicCellOfRawCodePair
    (n left right : ℕ)
    (hleft : natMultiplicativelyAtomicCheck left = true)
    (hright : natMultiplicativelyAtomicCheck right = true) :
    SU7BooleanAtomicRawBranchingCell n where
  cell := canonicalRawCodePairBranchingCell n left right
  left_check := by
    simpa [canonicalRawCodePairBranchingCell] using hleft
  right_check := by
    simpa [canonicalRawCodePairBranchingCell] using hright

/-- The canonical Boolean-atomic code-pair lift preserves residual energy. -/
theorem booleanAtomicCellOfRawCodePair_energy_eq
    (n left right : ℕ)
    (hleft : natMultiplicativelyAtomicCheck left = true)
    (hright : natMultiplicativelyAtomicCheck right = true) :
    rawAtomCodeBranchingDecompositionResidualEnergy
        (booleanAtomicCellOfRawCodePair n left right hleft hright).cell =
      rawCodePairResidualEnergy n left right := by
  simpa [booleanAtomicCellOfRawCodePair]
    using canonicalRawCodePairBranchingCell_energy_eq n left right

/-- The canonical Boolean-atomic code-pair lift appears in the unfiltered
generated list whenever the endpoint codes are in the bound. -/
theorem booleanAtomicCellOfRawCodePair_mem_generated
    {n bound left right : ℕ}
    (hleft_mem : left ∈ rawCodeBoundedList bound)
    (hright_mem : right ∈ rawCodeBoundedList bound)
    (hleft_check : natMultiplicativelyAtomicCheck left = true)
    (hright_check : natMultiplicativelyAtomicCheck right = true) :
    booleanAtomicCellOfRawCodePair n left right hleft_check hright_check ∈
      booleanAtomicRawBranchingCandidateList n bound := by
  let c := canonicalRawCodePairBranchingCell n left right
  unfold booleanAtomicRawBranchingCandidateList
  simp only [List.mem_filterMap]
  refine ⟨c, ?_, ?_⟩
  ·
    have hleft_le : left ≤ bound := by
      simpa [rawCodeBoundedList] using hleft_mem
    have hright_le : right ≤ bound := by
      simpa [rawCodeBoundedList] using hright_mem
    simp [rawBranchingCandidateCells, rawCodeBoundedList,
      SU3FlagSchubertCell.all, SU7BlockIncidence.all,
      c, canonicalRawCodePairBranchingCell]
    exact ⟨hleft_le, hright_le⟩
  ·
    unfold booleanAtomicCellOfCandidate?
    simp [booleanAtomicCellOfRawCodePair, c,
      canonicalRawCodePairBranchingCell, hleft_check, hright_check]

/-- The canonical Boolean-atomic code-pair lift appears in the filtered list
whenever the endpoint codes are generated and allowed. -/
theorem booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
    {n bound left right : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (hallowed : allowed left right = true)
    (hleft_mem : left ∈ rawCodeBoundedList bound)
    (hright_mem : right ∈ rawCodeBoundedList bound)
    (hleft_check : natMultiplicativelyAtomicCheck left = true)
    (hright_check : natMultiplicativelyAtomicCheck right = true) :
    booleanAtomicCellOfRawCodePair n left right hleft_check hright_check ∈
      gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n bound allowed := by
  unfold gaugeFilteredBooleanAtomicRawBranchingCandidateList
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · exact booleanAtomicCellOfRawCodePair_mem_generated
      hleft_mem hright_mem hleft_check hright_check
  · simpa [booleanAtomicCellOfRawCodePair,
      canonicalRawCodePairBranchingCell] using hallowed

/-- Unit descent stated on raw endpoint codes inside the Boolean allowed
sector. -/
def BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
    (n bound : ℕ) (allowed : ℕ -> ℕ -> Bool) : Prop :=
  ∀ left right : ℕ,
    allowed left right = true ->
      left ∈ rawCodeBoundedList bound ->
        right ∈ rawCodeBoundedList bound ->
          natMultiplicativelyAtomicCheck left = true ->
            natMultiplicativelyAtomicCheck right = true ->
              rawCodePairResidualEnergy n left right ≠ 0 ->
                ∃ left' right' : ℕ,
                  allowed left' right' = true ∧
                    left' ∈ rawCodeBoundedList bound ∧
                      right' ∈ rawCodeBoundedList bound ∧
                        natMultiplicativelyAtomicCheck left' = true ∧
                          natMultiplicativelyAtomicCheck right' = true ∧
                            rawCodePairResidualEnergy n left' right' + 1 =
                              rawCodePairResidualEnergy n left right

/-- Raw endpoint-code unit descent inside the allowed sector lifts to filtered
Boolean-cell descent through the canonical SU(7) branch/incidence lift. -/
theorem gaugeFilteredBooleanAtomicLaw_of_rawCodePairLaw
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
      n bound allowed) :
    GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw
      n bound allowed := by
  intro x hxmem hnonzero
  have hxparts :
      x ∈ booleanAtomicRawBranchingCandidateList n bound ∧
        allowed x.cell.leftWeightCode x.cell.rightWeightCode = true := by
    simpa [gaugeFilteredBooleanAtomicRawBranchingCandidateList]
      using (List.mem_filter.mp hxmem)
  have hleft_mem_x :
      x.cell.leftWeightCode ∈ rawCodeBoundedList bound :=
    booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
      hxparts.1
  have hright_mem_x :
      x.cell.rightWeightCode ∈ rawCodeBoundedList bound :=
    booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
      hxparts.1
  have hleft_check_x :
      natMultiplicativelyAtomicCheck x.cell.leftWeightCode = true :=
    x.left_check
  have hright_check_x :
      natMultiplicativelyAtomicCheck x.cell.rightWeightCode = true :=
    x.right_check
  have henergy_x :
      rawCodePairResidualEnergy n x.cell.leftWeightCode x.cell.rightWeightCode =
        rawAtomCodeBranchingDecompositionResidualEnergy x.cell := by
    exact (rawBranchingResidualEnergy_eq_codePair x.cell).symm
  have hpair_nonzero :
      rawCodePairResidualEnergy
        n x.cell.leftWeightCode x.cell.rightWeightCode ≠ 0 := by
    intro hzero
    have hxenergy_zero :
        rawAtomCodeBranchingDecompositionResidualEnergy x.cell = 0 := by
      simpa [hzero] using henergy_x.symm
    exact hnonzero
      ((rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff x.cell).mp
        hxenergy_zero)
  rcases
      H x.cell.leftWeightCode x.cell.rightWeightCode hxparts.2
        hleft_mem_x hright_mem_x hleft_check_x hright_check_x
        hpair_nonzero with
    ⟨left', right', hallowed', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, hsucc⟩
  let y :=
    booleanAtomicCellOfRawCodePair
      n left' right' hleft'_check hright'_check
  have hyfiltered :
      y ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n bound allowed :=
    booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
      hallowed' hleft'_mem hright'_mem hleft'_check hright'_check
  refine ⟨y, hyfiltered, ?_⟩
  calc
    rawAtomCodeBranchingDecompositionResidualEnergy y.cell + 1 =
        rawCodePairResidualEnergy n left' right' + 1 := by
          rw [booleanAtomicCellOfRawCodePair_energy_eq]
    _ = rawCodePairResidualEnergy
          n x.cell.leftWeightCode x.cell.rightWeightCode := hsucc
    _ = rawAtomCodeBranchingDecompositionResidualEnergy x.cell := henergy_x

/-- Filtered Boolean-cell descent reads back to raw endpoint-code unit descent
through the endpoint codes of the successor cell.

This is still a successor-law statement, not coverage: it lets information-face
finite grammar closure be consumed at the raw endpoint-code throat. -/
theorem boolGaugeFilteredRawCodePairUnitSuccessorLaw_of_booleanAtomicLaw
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw
      n bound allowed) :
    BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw n bound allowed := by
  intro left right hallowed hleft_mem hright_mem
    hleft_check hright_check hnonzero
  let x :=
    booleanAtomicCellOfRawCodePair n left right hleft_check hright_check
  have hxmem :
      x ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n bound allowed :=
    booleanAtomicCellOfRawCodePair_mem_gaugeFiltered
      hallowed hleft_mem hright_mem hleft_check hright_check
  have hxenergy :
      rawAtomCodeBranchingDecompositionResidualEnergy x.cell =
        rawCodePairResidualEnergy n left right :=
    booleanAtomicCellOfRawCodePair_energy_eq
      n left right hleft_check hright_check
  have hxnonzero :
      rawAtomCodeBranchingDecompositionResidual x.cell ≠ 0 := by
    intro hxzero
    have hxenergy_zero :
        rawAtomCodeBranchingDecompositionResidualEnergy x.cell = 0 :=
      (rawAtomCodeBranchingDecompositionResidualEnergy_eq_zero_iff
        x.cell).mpr hxzero
    exact hnonzero (by simpa [hxenergy] using hxenergy_zero)
  rcases H x hxmem hxnonzero with ⟨y, hymem, hyenergy⟩
  have hyparts :
      y ∈ booleanAtomicRawBranchingCandidateList n bound ∧
        allowed y.cell.leftWeightCode y.cell.rightWeightCode = true := by
    simpa [gaugeFilteredBooleanAtomicRawBranchingCandidateList]
      using (List.mem_filter.mp hymem)
  have hy_left_mem :
      y.cell.leftWeightCode ∈ rawCodeBoundedList bound :=
    booleanAtomicCell_left_mem_rawCodeBoundedList_of_mem_generated
      hyparts.1
  have hy_right_mem :
      y.cell.rightWeightCode ∈ rawCodeBoundedList bound :=
    booleanAtomicCell_right_mem_rawCodeBoundedList_of_mem_generated
      hyparts.1
  have hy_pair_energy :
      rawCodePairResidualEnergy
          n y.cell.leftWeightCode y.cell.rightWeightCode =
        rawAtomCodeBranchingDecompositionResidualEnergy y.cell :=
    (rawBranchingResidualEnergy_eq_codePair y.cell).symm
  refine
    ⟨y.cell.leftWeightCode, y.cell.rightWeightCode,
      hyparts.2, hy_left_mem, hy_right_mem,
      y.left_check, y.right_check, ?_⟩
  calc
    rawCodePairResidualEnergy
        n y.cell.leftWeightCode y.cell.rightWeightCode + 1 =
        rawAtomCodeBranchingDecompositionResidualEnergy y.cell + 1 := by
          rw [hy_pair_energy]
    _ = rawAtomCodeBranchingDecompositionResidualEnergy x.cell := hyenergy
    _ = rawCodePairResidualEnergy n left right := hxenergy

/-- The full Boolean-atomic finite grammar cannot satisfy raw endpoint-code
unit successor closure in the P948 boundary fiber. -/
theorem not_boolGaugeFilteredRawCodePairUnitSuccessorLaw_six_three_of_allowed_three_three
    {allowed : ℕ -> ℕ -> Bool}
    (hallowed33 : allowed 3 3 = true) :
    ¬ BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw 6 3 allowed := by
  intro H
  have hnonzero :
      rawCodePairResidualEnergy 6 3 3 ≠ 0 := by
    norm_num [rawCodePairResidualEnergy, rawCodePairResidual]
  rcases
      H 3 3 hallowed33
        three_mem_rawCodeBoundedList_three
        three_mem_rawCodeBoundedList_three
        natMultiplicativelyAtomicCheck_three
        natMultiplicativelyAtomicCheck_three
        hnonzero with
    ⟨left', right', _hallowed, hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, hsucc⟩
  have henergy5 :
      rawCodePairResidualEnergy 6 left' right' = 5 := by
    have hpair : rawCodePairResidualEnergy 6 3 3 = 6 :=
      rawCodePairResidualEnergy_six_three_three
    omega
  exact no_rawCodePairResidualEnergy_five_six_bound_three
    ⟨left', right', hleft'_mem, hright'_mem,
      hleft'_check, hright'_check, henergy5⟩

/-- Any information-face raw unit successor law on the P948 boundary fiber must
exclude the `(3,3)` boundary cell from its allowed sector.

This is a source-closure constraint, not a coverage/no-gap equivalence: a
successor-closed generated sector at `(n,bound) = (6,3)` cannot keep the broad
generated boundary cell. -/
theorem boolGaugeFilteredRawCodePairUnitSuccessorLaw_six_three_excludes_three_three
    {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw 6 3 allowed) :
    allowed 3 3 ≠ true := by
  intro hallowed33
  exact
    not_boolGaugeFilteredRawCodePairUnitSuccessorLaw_six_three_of_allowed_three_three
      hallowed33 H

/-- The full Boolean-atomic finite grammar cannot satisfy raw endpoint-code
unit successor closure in the P948 boundary fiber. -/
theorem not_boolGaugeFilteredRawCodePairUnitSuccessorLaw_true_six_three :
    ¬ BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
      6 3 (fun _ _ => true) :=
  not_boolGaugeFilteredRawCodePairUnitSuccessorLaw_six_three_of_allowed_three_three
    rfl

/-- Consequently, the full Boolean-cell generated grammar cannot satisfy the
unit successor law in the P948 boundary fiber. -/
theorem not_gaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw_true_six_three :
    ¬ GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw
      6 3 (fun _ _ => true) := by
  intro H
  exact not_boolGaugeFilteredRawCodePairUnitSuccessorLaw_true_six_three
    (boolGaugeFilteredRawCodePairUnitSuccessorLaw_of_booleanAtomicLaw H)

/-- Any successful finite Boolean-cell successor checker on the P948 boundary
fiber must exclude the `(3,3)` boundary cell from the allowed sector. -/
theorem gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck_six_three_excludes_three_three
    {allowed : ℕ -> ℕ -> Bool}
    (hcheck :
      gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck
        6 3 allowed = true) :
    allowed 3 3 ≠ true := by
  intro hallowed33
  exact
    not_boolGaugeFilteredRawCodePairUnitSuccessorLaw_six_three_of_allowed_three_three
      hallowed33
      (boolGaugeFilteredRawCodePairUnitSuccessorLaw_of_booleanAtomicLaw
        (gaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw_of_closureCheck
          hcheck))

/-- Any allowed sector that keeps the `(3,3)` boundary cell fails the
information-face Boolean-cell successor checker in the P948 boundary fiber. -/
theorem not_gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck_six_three_of_allowed_three_three
    {allowed : ℕ -> ℕ -> Bool}
    (hallowed33 : allowed 3 3 = true) :
    gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck
      6 3 allowed ≠ true := by
  intro hcheck
  exact
    gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck_six_three_excludes_three_three
      hcheck hallowed33

/-- The information-face successor checker also fails on the full
Boolean-atomic grammar in the P948 boundary fiber.

This pins down the red line: the finite checker is useful only when it checks a
genuinely refined/generated allowed sector, not the full bounded Boolean-atomic
space. -/
theorem not_gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck_true_six_three :
    gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck
      6 3 (fun _ _ => true) ≠ true := by
  exact
    not_gaugeFilteredGeneratedBooleanAtomicUnitSuccessorCheck_six_three_of_allowed_three_three
      rfl

/-- Raw endpoint-code unit descent inside the allowed sector forbids unit
permanent holonomy in the filtered generated spectrum. -/
theorem gaugeFilteredForbidsUnitPermanentHolonomy_of_rawCodePairLaw
    {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
    (H : BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw
      n bound allowed) :
    SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
      (gaugeFilteredRawBranchingSpectrum n bound allowed) :=
  gaugeFilteredForbidsUnitPermanentHolonomy_of_booleanAtomicLaw
    (gaugeFilteredBooleanAtomicLaw_of_rawCodePairLaw H)

/-! ## Certificate -/

/-- P949 certificate: a Boolean SU(7) allowed-sector filter builds a filtered
generated spectrum, and raw unit descent inside that selected sector forbids
unit permanent holonomy in the filtered spectrum. -/
structure SU7GaugeFilteredGeneratedSpectrumProducerCertificate where
  filtered_spectrum :
    ∀ n _bound : ℕ, (ℕ -> ℕ -> Bool) ->
      SU7BranchingDecompositionSpectrum n
  filtered_cell_mem :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
      {x : SU7BooleanAtomicRawBranchingCell n},
      x ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
        n bound allowed ->
        x.cell ∈ (gaugeFilteredRawBranchingSpectrum n bound allowed).cells
  spectrum_mem_to_filtered_cell :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool}
      {c : SU7BranchingDecompositionCell n},
      c ∈ (gaugeFilteredRawBranchingSpectrum n bound allowed).cells ->
        ∃ x : SU7BooleanAtomicRawBranchingCell n,
          x ∈ gaugeFilteredBooleanAtomicRawBranchingCandidateList
            n bound allowed ∧ x.cell = c
  raw_code_pair_law_to_boolean_law :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool},
      BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw n bound allowed ->
        GaugeFilteredGeneratedBooleanAtomicUnitSuccessorLaw n bound allowed
  raw_code_pair_law_to_no_unit_holonomy :
    ∀ {n bound : ℕ} {allowed : ℕ -> ℕ -> Bool},
      BoolGaugeFilteredRawCodePairEnergyUnitSuccessorLaw n bound allowed ->
        SU7RawBranchingSpectrumForbidsUnitPermanentHolonomy
          (gaugeFilteredRawBranchingSpectrum n bound allowed)

/-- Canonical P949 gauge-filtered generated-spectrum certificate. -/
def su7GaugeFilteredGeneratedSpectrumProducerCertificate :
    SU7GaugeFilteredGeneratedSpectrumProducerCertificate where
  filtered_spectrum :=
    gaugeFilteredRawBranchingSpectrum
  filtered_cell_mem :=
    gaugeFilteredBooleanAtomicCell_mem_spectrum
  spectrum_mem_to_filtered_cell :=
    exists_gaugeFilteredBooleanAtomicCell_of_mem_spectrum
  raw_code_pair_law_to_boolean_law :=
    gaugeFilteredBooleanAtomicLaw_of_rawCodePairLaw
  raw_code_pair_law_to_no_unit_holonomy :=
    gaugeFilteredForbidsUnitPermanentHolonomy_of_rawCodePairLaw


end
end StandardModelConstraint
end SaturationMonoid
