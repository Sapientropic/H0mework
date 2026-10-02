import H0mework.Versions.R2.Physics.MotherProgrammesFormationCoordinates.WholeConsumer

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammes

open Stage9C.Revision MotherFamilyOccurrence StageEightDiscreteFormation MotherCoordinateCompletion

noncomputable section

structure Entry where
  discreteVisit : MotherVisit
  coordinateVisit : MotherVisit

abbrev Datum := Material × (Fin (65 * 4) → ℚ)

namespace Entry

def word (entry : Entry) : List Instruction := programAt (codeOf entry.discreteVisit)
def data (entry : Entry) : Datum :=
  (readMaterial (sourceAtVisit entry.discreteVisit), rationalAt (65 * 4) entry.coordinateVisit)
def carrier (entry : Entry) : WholePointFormation.Carrier :=
  (fromVisit (65 * 4) entry.coordinateVisit : WholePointFormation.Carrier)
def source (entry : Entry) := WholePointFormation.source entry.discreteVisit entry.carrier

theorem word_generates (entry : Entry) : run entry.word = entry.data.1 := by
  change run (programAt (codeOf entry.discreteVisit)) =
    readMaterial (toSource (materialAt (codeOf entry.discreteVisit)))
  rw [full_material_recovered, materialAt]
  exact (execute_from_mother _).symm

theorem carrier_coordinates (entry : Entry) :
    coordinates (65 * 4) entry.carrier = fun slot => (entry.data.2 slot : ℝ) := by
  rw [carrier, coordinates_coe]
  rfl

theorem source_material (entry : Entry) : readMaterial entry.source = entry.data.1 :=
  PotentialSourceFormation.discrete_retained _ _

end Entry

/-- Both complete inputs are prefixes of this one current mother occurrence. -/
def entryAt (visit : MotherVisit) : Entry :=
  ⟨RationalSourceFormation.pastVisit visit (codeOf visit).unpair.1,
    RationalSourceFormation.pastVisit visit (codeOf visit).unpair.2⟩

theorem entry_discrete_code (visit : MotherVisit) :
    codeOf (entryAt visit).discreteVisit = (codeOf visit).unpair.1 :=
  RationalSourceFormation.past_code _ _ (Nat.unpair_left_le _)

theorem entry_coordinate_code (visit : MotherVisit) :
    codeOf (entryAt visit).coordinateVisit = (codeOf visit).unpair.2 :=
  RationalSourceFormation.past_code _ _ (Nat.unpair_right_le _)

theorem entry_prefixes (visit : MotherVisit) :
    temporalDepth (entryAt visit).discreteVisit.history ≤ temporalDepth visit.history ∧
      temporalDepth (entryAt visit).coordinateVisit.history ≤ temporalDepth visit.history ∧
      ∀ slot : Fin (65 * 4),
        temporalDepth (sample (65 * 4) (entryAt visit).coordinateVisit slot).history ≤
          temporalDepth visit.history :=
  ⟨RationalSourceFormation.past_depth_le _ _, RationalSourceFormation.past_depth_le _ _,
    fun slot => (sample_is_past _ _ slot).trans (RationalSourceFormation.past_depth_le _ _)⟩

theorem rational_same_code (first last : MotherVisit) (same : codeOf first = codeOf last) :
    rationalAt (65 * 4) first = rationalAt (65 * 4) last := by
  funext slot
  unfold rationalAt sourceAtVisit
  rw [sample_code, sample_code, same]

theorem entry_data_same_code (first last : MotherVisit) (same : codeOf first = codeOf last) :
    (entryAt first).data = (entryAt last).data := by
  apply Prod.ext
  · change readMaterial (toSource (materialAt (codeOf (entryAt first).discreteVisit))) =
      readMaterial (toSource (materialAt (codeOf (entryAt last).discreteVisit)))
    rw [entry_discrete_code, entry_discrete_code, same]
  · exact rational_same_code _ _ (by rw [entry_coordinate_code, entry_coordinate_code, same])

theorem every_entry (target : Datum) :
    ∃ code, (entryAt (SpinPair.visit (10 + code))).data = target := by
  obtain ⟨materialCode, material⟩ := every_material_at_code target.1
  obtain ⟨coordinateCode, coordinate⟩ := every_rational_vector (65 * 4) target.2
  refine ⟨Nat.pair materialCode coordinateCode, Prod.ext ?_ ?_⟩
  · change readMaterial (toSource (materialAt
      (codeOf (entryAt (SpinPair.visit (10 + Nat.pair materialCode coordinateCode))).discreteVisit))) = _
    rw [full_material_recovered, entry_discrete_code, code_at, Nat.unpair_pair, material]
  · change rationalAt (65 * 4)
      (entryAt (SpinPair.visit (10 + Nat.pair materialCode coordinateCode))).coordinateVisit = _
    exact (rational_same_code _ (SpinPair.visit (10 + coordinateCode)) (by
      rw [entry_coordinate_code, code_at, Nat.unpair_pair, code_at])).trans coordinate

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherProgrammes
