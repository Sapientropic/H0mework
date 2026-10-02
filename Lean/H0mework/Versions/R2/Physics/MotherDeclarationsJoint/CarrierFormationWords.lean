import H0mework.Versions.R2.Physics.MotherDeclarationsSource.TypeOriginCoverage

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier

open MotherTypeFormation MotherSourceTypeOrigin

noncomputable section

/-- Fixed original-source recovery after the mother word has been formed. -/
def readWord (typeLaw : Law) (word : Carrier typeLaw) : ActualFormation.IntegralCarrier :=
  Finsupp.mapDomain (fun generator => sourceRead generator.2.val) word

def iterateWord (typeLaw actionLaw : Law) : ℕ → Carrier typeLaw → Option (Carrier typeLaw)
  | 0, word => some word
  | stage + 1, word => (iterateWord typeLaw actionLaw stage word).bind (wordAction typeLaw actionLaw)

theorem native_word_laws :
    ∃ typeLaw actionLaw : Law,
      (∀ target : ActualFormation.IntegralCarrier,
        ∃ material : WordMaterial, ∃ word : Carrier typeLaw,
          formWord typeLaw material = some word ∧ readWord typeLaw word = target) ∧
      ∀ word : Carrier typeLaw, ∃ after : Carrier typeLaw,
        wordAction typeLaw actionLaw word = some after ∧
        readWord typeLaw after = ActualFormation.nativeAction (readWord typeLaw word) := by
  obtain ⟨typeLaw, typeExact, _⟩ := every_family sourceFiber
  let corresponding := sourceEquiv typeLaw typeExact
  have read_eq (word : Carrier typeLaw) :
      readWord typeLaw word = (Finsupp.domCongr corresponding) word :=
    (Finsupp.equivMapDomain_eq_mapDomain corresponding word).symm
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
  refine ⟨typeLaw, actionLaw, ?_, ?_⟩
  · intro target
    let word := (Finsupp.domCongr corresponding).symm target
    obtain ⟨material, formed⟩ := every_word typeLaw word
    exact ⟨material, word, formed,
      (read_eq word).trans ((Finsupp.domCongr corresponding).apply_symm_apply target)⟩
  · intro word
    refine ⟨Finsupp.mapDomain next word, wordAction_eq_mapDomain typeLaw actionLaw next nextAt word, ?_⟩
    rw [read_eq, read_eq]
    simp only [Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain]
    change Finsupp.mapDomain corresponding (Finsupp.mapDomain next word) =
      Finsupp.mapDomain ActualFormation.nextGenerator (Finsupp.mapDomain corresponding word)
    rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
    apply congrArg (fun operation => Finsupp.mapDomain operation word)
    funext generator
    exact corresponding.apply_symm_apply _

theorem iterateWord_native (typeLaw actionLaw : Law)
    (acts : ∀ word : Carrier typeLaw, ∃ after : Carrier typeLaw,
      wordAction typeLaw actionLaw word = some after ∧
      readWord typeLaw after = ActualFormation.nativeAction (readWord typeLaw word))
    (stage : ℕ) (word : Carrier typeLaw) :
    ∃ after : Carrier typeLaw,
      iterateWord typeLaw actionLaw stage word = some after ∧
      readWord typeLaw after = (ActualFormation.nativeAction ^ stage) (readWord typeLaw word) := by
  induction stage with
  | zero => exact ⟨word, rfl, rfl⟩
  | succ stage ih =>
      obtain ⟨middle, generated, reads⟩ := ih
      obtain ⟨after, formed, nextRead⟩ := acts middle
      refine ⟨after, ?_, ?_⟩
      · simp only [iterateWord, generated, Option.bind_some, formed]
      · simpa only [pow_succ', Module.End.mul_apply] using
          nextRead.trans (congrArg ActualFormation.nativeAction reads)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier
