import H0mework.Versions.R2.Physics.MotherProgrammesFormationProgrammes.Programme

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFiniteLaws

open MotherFamilyOccurrence StageEightDiscreteFormation MotherCoordinateCompletion
open RationalSourceFormation Stage9C.Revision

noncomputable section

@[ext] structure Term (n m : ℕ) where
  exponent : Fin n → ℕ
  coefficient : Fin m → ℚ

/-- The full entry keeps its original two parents; this is only its law-data readout. -/
def readEntry (n m : ℕ) (entry : MotherProgrammes.Entry) : Term n m where
  exponent := unpack n (codeOf entry.discreteVisit)
  coefficient := rationalAt m entry.coordinateVisit

def termAt (n m : ℕ) (visit : MotherVisit) : Term n m :=
  readEntry n m (MotherProgrammes.entryAt visit)

def terms (n m : ℕ) (visit : MotherVisit) : List (Term n m) :=
  (MotherProgrammes.programmeAt visit).map (readEntry n m)

theorem rational_same_code (count : ℕ) (first last : MotherVisit)
    (same : codeOf first = codeOf last) : rationalAt count first = rationalAt count last := by
  funext slot
  unfold rationalAt sourceAtVisit
  rw [MotherCoordinateCompletion.sample_code, MotherCoordinateCompletion.sample_code, same]

theorem term_same_code (n m : ℕ) (first last : MotherVisit)
    (same : codeOf first = codeOf last) : termAt n m first = termAt n m last := by
  apply Term.ext
  · change unpack n (codeOf (MotherProgrammes.entryAt first).discreteVisit) =
      unpack n (codeOf (MotherProgrammes.entryAt last).discreteVisit)
    rw [MotherProgrammes.entry_discrete_code, MotherProgrammes.entry_discrete_code, same]
  · apply rational_same_code
    rw [MotherProgrammes.entry_coordinate_code, MotherProgrammes.entry_coordinate_code, same]

theorem every_term {n m : ℕ} (target : Term n m) :
    ∃ code, termAt n m (SpinPair.visit (10 + code)) = target := by
  obtain ⟨coefficientCode, coefficients⟩ := every_rational_vector m target.coefficient
  refine ⟨Nat.pair (pack target.exponent) coefficientCode, ?_⟩
  apply Term.ext
  · change unpack n (codeOf (MotherProgrammes.entryAt _).discreteVisit) = target.exponent
    rw [MotherProgrammes.entry_discrete_code, code_at, Nat.unpair_pair, unpack_pack]
  · change rationalAt m (MotherProgrammes.entryAt _).coordinateVisit = target.coefficient
    exact (rational_same_code m _ (SpinPair.visit (10 + coefficientCode)) (by
      rw [MotherProgrammes.entry_coordinate_code, code_at, Nat.unpair_pair, code_at])).trans coefficients

theorem terms_packed (n m : ℕ) {count : ℕ} (codes : Fin count → ℕ) :
    terms n m (SpinPair.visit (10 + Nat.pair count (pack codes))) =
      List.ofFn (fun slot => termAt n m (SpinPair.visit (10 + codes slot))) := by
  unfold terms
  rw [MotherProgrammes.programmeAt, code_at, Nat.unpair_pair]
  change (List.ofFn (fun slot : Fin count => MotherProgrammes.entryAt
    (pastVisit (SpinPair.visit (10 + Nat.pair count (pack codes)))
      (unpack count (pack codes) slot)))).map (readEntry n m) = _
  rw [List.map_ofFn, unpack_pack]
  apply congrArg List.ofFn
  funext slot
  apply term_same_code
  have inner : codes slot ≤ pack codes := by
    simpa only [unpack_pack] using unpack_le count (pack codes) slot
  rw [past_code _ _ (by simpa only [code_at] using inner.trans (Nat.right_le_pair count (pack codes))), code_at]

/-- Every finite law expression is formed from one current mother's existing past. -/
theorem every_terms {n m : ℕ} (target : List (Term n m)) :
    ∃ code, terms n m (SpinPair.visit (10 + code)) = target := by
  have each : ∀ slot : Fin target.length, ∃ code,
      termAt n m (SpinPair.visit (10 + code)) = target.get slot :=
    fun slot => every_term (target.get slot)
  choose codes generated using each
  refine ⟨Nat.pair target.length (pack codes), ?_⟩
  rw [terms_packed]
  rw [show (fun slot => termAt n m (SpinPair.visit (10 + codes slot))) = target.get from funext generated]
  exact List.ofFn_get target

theorem entry_origins (m : ℕ) (visit : MotherVisit) (entry : MotherProgrammes.Entry)
    (member : entry ∈ MotherProgrammes.programmeAt visit) :
    temporalDepth entry.discreteVisit.history ≤ temporalDepth visit.history ∧
    temporalDepth entry.coordinateVisit.history ≤ temporalDepth visit.history ∧
    ∀ slot : Fin m,
      temporalDepth (sample m entry.coordinateVisit slot).history ≤ temporalDepth visit.history := by
  have parent := MotherProgrammes.programme_prefixes visit entry member
  exact ⟨parent.1, parent.2.1, fun slot => (sample_is_past m entry.coordinateVisit slot).trans parent.2.1⟩

theorem coefficient_actual (n m : ℕ) (entry : MotherProgrammes.Entry) (slot : Fin m) :
    ((readEntry n m entry).coefficient slot : ℝ) =
      sourceTrace (sourceAtVisit (sample m entry.coordinateVisit slot)) :=
  actual_trace m entry.coordinateVisit slot

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherFiniteLaws
