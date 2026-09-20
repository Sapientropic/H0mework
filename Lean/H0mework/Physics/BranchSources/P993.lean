import H0mework.Physics.BranchSources.P990

/-!
# Proposition 993: incidence normalizers produce full-orbit zero residual

This returns to the P990 main line.  The producer is now purely on the full
SU(7) incidence orbit:

```text
full SU(7) incidence orbit
-> incidence normalizer
-> charged incidence descends to an exact incidence
-> exact incidence is fixed
-> finite-list quantized minimum
-> terminal point cannot be charged
-> zero generated color residual
```

No endpoint code, no no-prime branch cell, and no raw shell appears in this
file.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

noncomputable section

open RunningSigmaBeta

set_option linter.defProp false

/-! ## Finite-list quantized minimum -/

/-- A nonempty finite list has an element of minimal `Nat` energy. -/
theorem finiteList_exists_min_energy
    {X : Type*} (E : X -> ℕ) :
    ∀ xs : List X,
      xs ≠ [] ->
        ∃ x : X, x ∈ xs ∧ ∀ y : X, y ∈ xs -> E x ≤ E y
  | [], hne => False.elim (hne rfl)
  | x :: xs, _hne => by
      by_cases htail : xs = []
      · subst xs
        refine ⟨x, by simp, ?_⟩
        intro y hy
        simp at hy
        subst y
        exact Nat.le_refl _
      · rcases finiteList_exists_min_energy E xs htail with
          ⟨z, hzmem, hzmin⟩
        by_cases hxle : E x ≤ E z
        · refine ⟨x, by simp, ?_⟩
          intro y hy
          rw [List.mem_cons] at hy
          rcases hy with hy | hytail
          · subst y
            exact Nat.le_refl _
          · exact Nat.le_trans hxle (hzmin y hytail)
        · have hzlex : E z ≤ E x :=
            Nat.le_of_lt (Nat.lt_of_not_ge hxle)
          refine ⟨z, by simp [hzmem], ?_⟩
          intro y hy
          rw [List.mem_cons] at hy
          rcases hy with hy | hytail
          · subst y
            exact hzlex
          · exact hzmin y hytail

/-- A nonempty finite list supplies the P980 quantized minimum on its
membership orbit. -/
theorem finiteList_quantizedMinimum
    {X : Type*} (xs : List X) (E : X -> ℕ)
    (hne : xs ≠ []) :
    QuantizedMinimum {x : X | x ∈ xs} E := by
  intro _horbit_nonempty
  rcases finiteList_exists_min_energy E xs hne with
    ⟨x, hxmem, hxmin⟩
  exact ⟨x, hxmem, hxmin⟩

/-! ## Incidence normalizer -/

/-- Incidence-level confinement normalizer.

Color-charged incidences are transported to the color-neutral singlet
incidence.  Exact incidences are fixed. -/
def incidenceNormalizer : SU7BlockIncidence -> SU7BlockIncidence
  | .colorWeak => .positiveNegativeSinglet
  | .colorPositiveSinglet => .positiveNegativeSinglet
  | .colorNegativeSinglet => .positiveNegativeSinglet
  | .weakPositiveSinglet => .weakPositiveSinglet
  | .weakNegativeSinglet => .weakNegativeSinglet
  | .positiveNegativeSinglet => .positiveNegativeSinglet

/-- Exact incidences are fixed by the incidence normalizer. -/
theorem incidenceNormalizer_fixed_of_exact
    {incidence : SU7BlockIncidence}
    (hmem : incidence ∈ su7ColorExactIncidences) :
    incidenceNormalizer incidence = incidence := by
  cases incidence <;>
    simp [incidenceNormalizer, su7ColorExactIncidences] at hmem ⊢

/-- Normalized incidences are still among the six generated SU(7) incidences.
-/
theorem incidenceNormalizer_mem_all
    (incidence : SU7BlockIncidence) :
    incidenceNormalizer incidence ∈ SU7BlockIncidence.all := by
  cases incidence <;>
    simp [incidenceNormalizer, SU7BlockIncidence.all]

/-- A charged incidence strictly descends to a lower generated color residual.
-/
theorem incidenceNormalizer_strictly_decreases_charged
    (n : ℕ) (branch : SU3FlagSchubertCell)
    {incidence : SU7BlockIncidence}
    (hmem : incidence ∈ su7ColorChargedIncidences) :
    generatedTerminalColorResidual
        (generatedTerminalColorCellOfRepresentationSlot n branch
          (incidenceNormalizer incidence)) <
      generatedTerminalColorResidual
        (generatedTerminalColorCellOfRepresentationSlot n branch
          incidence) := by
  cases incidence <;>
    simp [su7ColorChargedIncidences, incidenceNormalizer,
      generatedTerminalColorResidual,
      generatedTerminalColorCellOfRepresentationSlot,
      terminalColorLoopOfIncidence] at hmem ⊢

/-- If an incidence-generated slot is exact, the normalizer fixes the
generated slot. -/
theorem generatedSlot_incidenceNormalizer_fixed_of_exact
    (n : ℕ) (branch : SU3FlagSchubertCell)
    {incidence : SU7BlockIncidence}
    (hmem : incidence ∈ su7ColorExactIncidences) :
    generatedTerminalColorCellOfRepresentationSlot n branch
        (incidenceNormalizer incidence) =
      generatedTerminalColorCellOfRepresentationSlot n branch incidence := by
  rw [incidenceNormalizer_fixed_of_exact hmem]

/-- The incidence normalizer preserves the full generated incidence orbit. -/
theorem incidenceNormalizer_preserves_full_generated_orbit
    {n : ℕ} {branch : SU3FlagSchubertCell}
    (hbranch : branch ∈ SU3FlagSchubertCell.all)
    (incidence : SU7BlockIncidence) :
    generatedTerminalColorCellOfRepresentationSlot n branch
        (incidenceNormalizer incidence) ∈
      su7RepresentationFullTerminalCells n := by
  unfold su7RepresentationFullTerminalCells
  exact List.mem_flatMap.mpr
    ⟨branch, hbranch,
      List.mem_map.mpr
        ⟨incidenceNormalizer incidence,
          incidenceNormalizer_mem_all incidence,
          rfl⟩⟩

/-! ## Full-orbit descent from the incidence normalizer -/

/-- Every full-orbit permanent-holonomy cell has a lower-residual full-orbit
normal form selected by the incidence normalizer. -/
theorem fullGeneratedColor_incidenceNormalizer_descent
    {n : ℕ}
    (cell : SU7GeneratedTerminalColorCell n)
    (hmem : cell ∈ su7RepresentationFullTerminalColorOrbit n)
    (hhol : generatedTerminalColorPermanentHolonomy cell) :
    ∃ y : SU7GeneratedTerminalColorCell n,
      y ∈ su7RepresentationFullTerminalColorOrbit n ∧
        generatedTerminalColorResidual y <
          generatedTerminalColorResidual cell := by
  unfold su7RepresentationFullTerminalColorOrbit
    su7RepresentationFullTerminalCells at hmem
  rcases List.mem_flatMap.mp hmem with
    ⟨branch, hbranch, hmap⟩
  rcases List.mem_map.mp hmap with
    ⟨incidence, hincidence, rfl⟩
  refine
    ⟨generatedTerminalColorCellOfRepresentationSlot n branch
        (incidenceNormalizer incidence),
      ?_, ?_⟩
  · exact incidenceNormalizer_preserves_full_generated_orbit
      hbranch incidence
  · rcases su7Incidence_exact_or_charged incidence with hExact | hCharged
    · have hzero :
        generatedTerminalColorResidual
            (generatedTerminalColorCellOfRepresentationSlot
              n branch incidence) = 0 :=
        generatedRepresentationExactIncidence_residual_zero
          n branch hExact
      exact False.elim (hhol hzero)
    · exact incidenceNormalizer_strictly_decreases_charged
        n branch hCharged

/-- The full generated incidence list is nonempty. -/
theorem su7RepresentationFullTerminalCells_ne_nil
    (n : ℕ) :
    su7RepresentationFullTerminalCells n ≠ [] := by
  intro hnil
  have hmem := su7RepresentationFullGround_mem n
  rw [hnil] at hmem
  simp at hmem

/-- The full generated incidence orbit gets its quantized minimum from the
finite list itself. -/
theorem quantizedMinimum_of_su7RepresentationFullTerminalCells
    (n : ℕ) :
    QuantizedMinimum
      (su7RepresentationFullTerminalColorOrbit n)
      generatedTerminalColorResidual := by
  simpa [su7RepresentationFullTerminalColorOrbit] using
    finiteList_quantizedMinimum
      (su7RepresentationFullTerminalCells n)
      generatedTerminalColorResidual
      (su7RepresentationFullTerminalCells_ne_nil n)

/-- Full SU(7) incidence-normalizer producer: the full incidence orbit itself
contains a zero generated color residual. -/
theorem zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer
    (n : ℕ) :
    ∃ cell : SU7GeneratedTerminalColorCell n,
      cell ∈ su7RepresentationFullTerminalColorOrbit n ∧
        generatedTerminalColorResidual cell = 0 :=
  terminalConfinement_zeroResidual_of_holonomy_descent
    (su7RepresentationFullTerminalColorOrbit_nonempty n)
    (quantizedMinimum_of_su7RepresentationFullTerminalCells n)
    (fun _cell _hterminal hnonzero => hnonzero)
    (fun cell hmem hhol =>
      fullGeneratedColor_incidenceNormalizer_descent cell hmem hhol)

/-- Main no-prefilter producer theorem: P993 replaces the older exact-sector
route by producing zero residual directly from the full generated incidence
orbit. -/
theorem fullOrbitProducer_no_exactPrefilter
    (n : ℕ) :
    ∃ cell : SU7GeneratedTerminalColorCell n,
      cell ∈ su7RepresentationFullTerminalColorOrbit n ∧
        generatedTerminalColorResidual cell = 0 :=
  zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer n

/-- The P993 full-orbit incidence-normalizer producer projects to the
physical terminal cell residual without passing through endpoint/raw-code
adapters. -/
theorem zeroTerminalPhysicalResidual_of_fullOrbitIncidenceNormalizer
    (n : ℕ) :
    ∃ cell : SU7TerminalPhysicalBranchCell n,
      terminalPhysicalResidual cell = 0 := by
  rcases zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer n with
    ⟨cell, _hmem, hzero⟩
  exact
    ⟨terminalPhysicalCellOfGeneratedColorCell cell,
      by simp [hzero]⟩

/-! ## Certificate -/

/-- P993 certificate: full SU(7) incidence orbit zero residual is produced by
finite-list minimization plus the incidence normalizer. -/
structure FullOrbitIncidenceNormalizerCertificate where
  finite_list_minimum :
    ∀ {X : Type*} (xs : List X) (E : X -> ℕ),
      xs ≠ [] -> QuantizedMinimum {x : X | x ∈ xs} E
  incidence_normalizer :
    SU7BlockIncidence -> SU7BlockIncidence
  exact_fixed :
    ∀ {incidence : SU7BlockIncidence},
      incidence ∈ su7ColorExactIncidences ->
        incidenceNormalizer incidence = incidence
  charged_descends :
    ∀ (n : ℕ) (branch : SU3FlagSchubertCell)
      {incidence : SU7BlockIncidence},
      incidence ∈ su7ColorChargedIncidences ->
        generatedTerminalColorResidual
            (generatedTerminalColorCellOfRepresentationSlot n branch
              (incidenceNormalizer incidence)) <
          generatedTerminalColorResidual
            (generatedTerminalColorCellOfRepresentationSlot n branch
              incidence)
  preserves_full_orbit :
    ∀ {n : ℕ} {branch : SU3FlagSchubertCell},
      branch ∈ SU3FlagSchubertCell.all ->
        ∀ incidence : SU7BlockIncidence,
          generatedTerminalColorCellOfRepresentationSlot n branch
              (incidenceNormalizer incidence) ∈
            su7RepresentationFullTerminalCells n
  full_orbit_zero :
    ∀ n : ℕ,
      ∃ cell : SU7GeneratedTerminalColorCell n,
        cell ∈ su7RepresentationFullTerminalColorOrbit n ∧
          generatedTerminalColorResidual cell = 0

/-- Canonical P993 full-orbit incidence-normalizer certificate. -/
def fullOrbitIncidenceNormalizerCertificate :
    FullOrbitIncidenceNormalizerCertificate where
  finite_list_minimum := by
    intro X xs E hne
    exact finiteList_quantizedMinimum xs E hne
  incidence_normalizer := incidenceNormalizer
  exact_fixed := incidenceNormalizer_fixed_of_exact
  charged_descends := incidenceNormalizer_strictly_decreases_charged
  preserves_full_orbit := by
    intro n branch hbranch incidence
    exact incidenceNormalizer_preserves_full_generated_orbit
      hbranch incidence
  full_orbit_zero := zeroGeneratedColorResidual_of_fullOrbitIncidenceNormalizer


end
end StandardModelConstraint
end SaturationMonoid
