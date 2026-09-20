import H0mework.Physics.MotherDeclarationsNative.PhysicalQueryProgramme
import H0mework.Physics.MotherDeclarationsJoint.CarrierFormationCoverage

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery

open MotherTypeFormation MotherFamilyOccurrence MotherJointCarrier

noncomputable section

theorem integer_parent (original : MotherVisit) :
    integerAt (parent (StageEightDiscreteFormation.codeOf original)) = integerAt original := by
  simp only [integerAt, StageEightDiscreteFormation.sourceAtVisit, parent_code]

theorem readTerms_encoded (law : Law) (terms : List TermMaterial) :
    readTerms law (terms.map (expandTerm ∘ encodeTerm)) = readTerms law terms := by
  induction terms with
  | nil => rfl
  | cons term rest induction =>
    simp only [List.map_cons, readTerms]
    rw [induction]
    simp only [Function.comp_def, expandTerm, encodeTerm, integer_parent]

theorem word_consumed (law : Law) (word : WordMaterial) :
    formWord law (expandWord (encodeWord word)) = formWord law word := by
  unfold formWord
  rw [expandWord_terms, encodeWord, List.map_map]
  exact readTerms_encoded law _

theorem term_formed (law : Law) (term : OrbitMaterial) :
    formTerm law (expandOrbit (encodeOrbit term)) = formTerm law term := by
  simp only [formTerm, expandOrbit, encodeOrbit, word_consumed, parent_code]

theorem term_acted (typeLaw actionLaw : Law) (term : OrbitMaterial) :
    actTerm typeLaw actionLaw (expandOrbit (encodeOrbit term)) = actTerm typeLaw actionLaw term := by
  simp only [actTerm, expandOrbit, encodeOrbit, word_consumed, parent_code]

theorem formation_consumed (typeLaw : Law) (material : MotherJointCarrier.Material) :
    MotherJointCarrier.form typeLaw (expand (encode material)) = MotherJointCarrier.form typeLaw material := by
  unfold MotherJointCarrier.form
  rw [expand_items, encode, List.map_map, List.map_map]
  apply congrArg sumOptions
  apply List.map_congr_left
  intro term _
  exact term_formed typeLaw term

theorem action_consumed (typeLaw actionLaw : Law) (material : MotherJointCarrier.Material) :
    MotherJointCarrier.act typeLaw actionLaw (expand (encode material)) = MotherJointCarrier.act typeLaw actionLaw material := by
  unfold MotherJointCarrier.act
  rw [expand_items, encode, List.map_map, List.map_map]
  apply congrArg sumOptions
  apply List.map_congr_left
  intro term _
  exact term_acted typeLaw actionLaw term

abbrev Answer := Query × Option Joint × Option Joint

def answer (typeLaw actionLaw : Law) (query : Query) : Answer :=
  (query, MotherJointCarrier.form typeLaw (expand query), MotherJointCarrier.act typeLaw actionLaw (expand query))

/-- Both mother laws precede all members of the original whole carrier. The programme stays in the answer. -/
theorem whole_physics_formed : ∃ typeLaw actionLaw : Law, ∀ value : Joint, ∃ query : Query,
    answer typeLaw actionLaw query = (query, some value, some (ActualFormation.Transition.nativeLift value)) := by
  obtain ⟨typeLaw, actionLaw, formed⟩ := whole_carrier_formed
  refine ⟨typeLaw, actionLaw, fun value => ?_⟩
  obtain ⟨material, before, after⟩ := formed value
  refine ⟨encode material, Prod.ext rfl ?_⟩
  exact Prod.ext ((formation_consumed typeLaw material).trans before)
    ((action_consumed typeLaw actionLaw material).trans after)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherNativePhysicalQuery
