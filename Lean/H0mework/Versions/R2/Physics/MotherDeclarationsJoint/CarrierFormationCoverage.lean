import H0mework.Versions.R2.Physics.MotherDeclarationsJoint.CarrierFormationSemantics

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 8000000

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedIntegralCoherentJointAction
open MotherTypeFormation MotherSourceTypeOrigin MotherFamilyOccurrence Stage9C.Revision

noncomputable section

private theorem every_items (values : List OrbitMaterial) :
    ∃ material : Material, items material = values := by
  let parent := SpinPair.visit (10 + values.length)
  have lengthEq : StageEightDiscreteFormation.codeOf parent = values.length :=
    StageEightDiscreteFormation.code_at values.length
  let entries : Fin (StageEightDiscreteFormation.codeOf parent) → OrbitMaterial :=
    fun index => values.get (Fin.cast lengthEq index)
  refine ⟨⟨parent, entries⟩, ?_⟩
  apply List.ext_get
  · simp [items, entries, lengthEq]
  · intro index firstBound lastBound
    simp [items, entries]

private theorem every_terms (typeLaw actionLaw : Law)
    (formedWords : ∀ target : ActualFormation.IntegralCarrier,
      ∃ material : WordMaterial, ∃ word : Carrier typeLaw,
        formWord typeLaw material = some word ∧ readWord typeLaw word = target)
    (acts : ∀ word : Carrier typeLaw, ∃ after : Carrier typeLaw,
      wordAction typeLaw actionLaw word = some after ∧
      readWord typeLaw after = ActualFormation.nativeAction (readWord typeLaw word))
    (terms : List (ℕ × ActualFormation.IntegralCarrier)) :
    ∃ materials : List OrbitMaterial,
      sumOptions (materials.map (formTerm typeLaw)) =
        some (MotherOrbitWords.total ActualFormation.jointInput terms) ∧
      sumOptions (materials.map (actTerm typeLaw actionLaw)) =
        some (ActualFormation.Transition.nativeLift (MotherOrbitWords.total ActualFormation.jointInput terms)) := by
  induction terms with
  | nil =>
      refine ⟨[], rfl, ?_⟩
      exact congrArg some (map_zero ActualFormation.Transition.nativeLift).symm
  | cons index rest ih =>
      let parent := SpinPair.visit (10 + index.1)
      obtain ⟨wordMaterial, termFormed, termActed⟩ := every_term typeLaw actionLaw formedWords acts parent index.2
      let material : OrbitMaterial := (parent, wordMaterial)
      have orbitEq : orbitValue (StageEightDiscreteFormation.codeOf parent) index.2 =
          orbitValue index.1 index.2 :=
        congrArg (fun stage => orbitValue stage index.2) (StageEightDiscreteFormation.code_at index.1)
      have oneFormed : formTerm typeLaw material = some (orbitValue index.1 index.2) :=
        termFormed.trans (congrArg some orbitEq)
      have oneActed : actTerm typeLaw actionLaw material =
          some (ActualFormation.Transition.nativeLift (orbitValue index.1 index.2)) :=
        termActed.trans (congrArg some (congrArg ActualFormation.Transition.nativeLift orbitEq))
      obtain ⟨materials, restFormed, restActed⟩ := ih
      refine ⟨material :: materials, ?_, ?_⟩
      · exact congrArg₂ (fun first tail : Option Joint =>
          first.bind fun value => tail.map (value + ·)) oneFormed restFormed
      · have combined : sumOptions ((material :: materials).map (actTerm typeLaw actionLaw)) =
            some (ActualFormation.Transition.nativeLift (orbitValue index.1 index.2) +
              ActualFormation.Transition.nativeLift (MotherOrbitWords.total ActualFormation.jointInput rest)) :=
          congrArg₂ (fun first tail : Option Joint => first.bind fun value => tail.map (value + ·)) oneActed restActed
        exact combined.trans (congrArg some
          (map_add ActualFormation.Transition.nativeLift (orbitValue index.1 index.2)
            (MotherOrbitWords.total ActualFormation.jointInput rest)).symm)

/-- Every member of the original whole orbit carrier is formed and acted on from the same material. -/
theorem whole_carrier_formed :
    ∃ typeLaw actionLaw : Law, ∀ value : Joint, ∃ material : Material,
      form typeLaw material = some value ∧
      act typeLaw actionLaw material = some (ActualFormation.Transition.nativeLift value) := by
  obtain ⟨typeLaw, actionLaw, formedWords, acts⟩ := native_word_laws
  refine ⟨typeLaw, actionLaw, ?_⟩
  intro value
  obtain ⟨terms, termsEq⟩ := MotherOrbitWords.every_value ActualFormation.jointInput value
  obtain ⟨materials, formed, acted⟩ := every_terms typeLaw actionLaw formedWords acts terms
  obtain ⟨material, packed⟩ := every_items materials
  refine ⟨material, ?_, ?_⟩
  · exact (congrArg (fun list => sumOptions (list.map (formTerm typeLaw))) packed).trans
      (formed.trans (congrArg some termsEq))
  · exact (congrArg (fun list => sumOptions (list.map (actTerm typeLaw actionLaw))) packed).trans
      (acted.trans (congrArg some (congrArg ActualFormation.Transition.nativeLift termsEq)))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier
