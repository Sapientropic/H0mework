import H0mework.Physics.MotherProgrammesFormationCoordinates.Stream

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial

open MotherStreamFormation MotherCoordinateCompletion MotherFamilyOccurrence
open StageEightDiscreteFormation RationalSourceFormation Stage9C.Revision

noncomputable section

def sourceLength (visit : MotherVisit) : ℕ := (codeOf visit).unpair.1
def sourcePrefix (visit : MotherVisit) : MotherVisit := pastVisit visit (codeOf visit).unpair.2

/-- The finite layout and all sample addresses are read from this same current's past. -/
def rawAt (visit : MotherVisit) : Raw :=
  ⟨finiteNative (sourceLength visit, sourcePrefix visit),
    (sourceLength visit, sourcePrefix visit), rfl⟩

theorem samples_are_past (visit : MotherVisit) (slot : Fin (sourceLength visit)) :
    temporalDepth (sample (sourceLength visit) (sourcePrefix visit) slot).history ≤
      temporalDepth visit.history :=
  (sample_is_past _ _ slot).trans (past_depth_le visit _)

theorem rationalAt_same_code (count : ℕ) (first second : MotherVisit)
    (same : codeOf first = codeOf second) : rationalAt count first = rationalAt count second := by
  funext slot
  simp only [rationalAt, sourceAtVisit, MotherCoordinateCompletion.sample_code, same]

theorem rawAt_surjective : Function.Surjective rawAt := by
  rintro ⟨_, ⟨⟨count, visit⟩, rfl⟩⟩
  obtain ⟨code, generated⟩ := every_rational_vector count (rationalAt count visit)
  let sourceVisit := SpinPair.visit (10 + Nat.pair count code)
  have prefixCode : codeOf (pastVisit sourceVisit code) = code :=
    past_code sourceVisit code (by simpa only [sourceVisit, code_at] using Nat.right_le_pair count code)
  have samples : rationalAt count (pastVisit sourceVisit code) = rationalAt count visit := by
    rw [rationalAt_same_code count _ (SpinPair.visit (10 + code)) (by rw [prefixCode, code_at])]
    exact generated
  refine ⟨sourceVisit, Subtype.ext ?_⟩
  change finiteNative (sourceLength sourceVisit, sourcePrefix sourceVisit) = finiteNative (count, visit)
  have length_eq : sourceLength sourceVisit = count := by
    simp only [sourceLength, sourceVisit, code_at, Nat.unpair_pair]
  have prefix_eq : sourcePrefix sourceVisit = pastVisit sourceVisit code := by
    simp only [sourcePrefix, sourceVisit, code_at, Nat.unpair_pair]
  rw [length_eq, prefix_eq]
  unfold finiteNative
  exact congrArg (pad count) samples

theorem rawAt_read (visit : MotherVisit) :
    read (rawAt visit : Carrier) = finiteNative (sourceLength visit, sourcePrefix visit) :=
  read_coe _

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.CurrentMaterial
