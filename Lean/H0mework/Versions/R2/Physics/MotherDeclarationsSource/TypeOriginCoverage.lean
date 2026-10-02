import H0mework.Versions.R2.Physics.MotherDeclarationsSource.TypeOriginNative
import H0mework.Versions.R2.Physics.MotherDeclarationsSource.TypeOriginAction
import H0mework.Versions.R2.Physics.MotherProgrammesFormationActual.Joint

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourceTypeOrigin

open MotherTypeFormation

noncomputable section

/-- Both laws precede all complete native generators and all finite integer words. -/
theorem native_type_value_action_formed :
    ∃ typeLaw actionLaw : Law,
    ∃ corresponding : Generator typeLaw ≃ ActualFormation.Generator,
      (∀ generator : ActualFormation.Generator,
        ∃ material : MemberMaterial,
          formMember typeLaw material = some (corresponding.symm generator)) ∧
      (∀ generator : ActualFormation.Generator,
        generatorAction typeLaw actionLaw (corresponding.symm generator) =
          some (corresponding.symm (ActualFormation.nextGenerator generator))) ∧
      ∀ word : ActualFormation.IntegralCarrier,
        ∃ material : WordMaterial,
          formWord typeLaw material = some ((Finsupp.domCongr corresponding).symm word) ∧
          wordAction typeLaw actionLaw ((Finsupp.domCongr corresponding).symm word) =
            some ((Finsupp.domCongr corresponding).symm (ActualFormation.nativeAction word)) := by
  obtain ⟨typeLaw, typeExact, _⟩ := every_family sourceFiber
  let corresponding := sourceEquiv typeLaw typeExact
  obtain ⟨actionLaw, values, _⟩ := MotherPhysicalLaws.every_law
    (Function.extend sourceInput
      (fun generator => sourceSamples (ActualFormation.nextGenerator generator)) (fun _ => 0))
  have valueAt (generator : ActualFormation.Generator) :
      MotherPhysicalLaws.eval actionLaw (sourceInput generator) =
        sourceSamples (ActualFormation.nextGenerator generator) :=
    (values _).trans (sourceInput_injective.extend_apply _ _ generator)
  have generatorAt (generator : ActualFormation.Generator) :
      generatorAction typeLaw actionLaw (corresponding.symm generator) =
        some (corresponding.symm (ActualFormation.nextGenerator generator)) := by
    apply generatorAction_eq
    · rfl
    · exact valueAt generator
  let next := fun generator : Generator typeLaw =>
    corresponding.symm (ActualFormation.nextGenerator (corresponding generator))
  have nextAt (generator : Generator typeLaw) :
      generatorAction typeLaw actionLaw generator = some (next generator) := by
    simpa only [Equiv.symm_apply_apply] using generatorAt (corresponding generator)
  have wordAt (word : ActualFormation.IntegralCarrier) :
      wordAction typeLaw actionLaw (Finsupp.mapDomain corresponding.symm word) =
        some (Finsupp.mapDomain corresponding.symm (ActualFormation.nativeAction word)) := by
    change wordAction typeLaw actionLaw (Finsupp.mapDomain corresponding.symm word) =
      some (Finsupp.mapDomain corresponding.symm (Finsupp.mapDomain ActualFormation.nextGenerator word))
    rw [wordAction_eq_mapDomain typeLaw actionLaw next nextAt,
      ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    apply congrArg some
    apply congrArg (fun operation => Finsupp.mapDomain operation word)
    funext generator
    exact congrArg corresponding.symm
      (congrArg ActualFormation.nextGenerator (corresponding.apply_symm_apply generator))
  refine ⟨typeLaw, actionLaw, corresponding,
    every_native_generator typeLaw typeExact, generatorAt, ?_⟩
  intro word
  obtain ⟨material, formed⟩ := every_word typeLaw ((Finsupp.domCongr corresponding).symm word)
  refine ⟨material, formed, ?_⟩
  simpa only [Finsupp.domCongr_symm, Finsupp.domCongr_apply,
    Finsupp.equivMapDomain_eq_mapDomain] using wordAt word

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourceTypeOrigin
