import H0mework.Versions.R2.Physics.MotherDeclarationsType.FormationWords

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourceTypeOrigin

open MotherTypeFormation

noncomputable section

/-- The operation evaluates its mother law, then checks the formed fibre itself. -/
def generatorAction (typeLaw actionLaw : Law) (generator : Generator typeLaw) :
    Option (Generator typeLaw) := by
  classical
  let output := MotherPhysicalLaws.eval actionLaw (generator.1, generator.2.val)
  exact if member : MotherPhysicalLaws.eval typeLaw (generator.1, output) 0 = 0 then
    some ⟨generator.1, output, member⟩ else none

/-- Full coefficients add when several input generators have the same actual image. -/
def wordAction (typeLaw actionLaw : Law) (word : Carrier typeLaw) : Option (Carrier typeLaw) := by
  classical
  exact if ∀ generator ∈ word.support, (generatorAction typeLaw actionLaw generator).isSome then
    some (word.sum fun generator coefficient =>
      match generatorAction typeLaw actionLaw generator with
      | none => 0
      | some result => Finsupp.single result coefficient)
  else none

theorem generatorAction_eq (typeLaw actionLaw : Law)
    (before after : Generator typeLaw) (sameCurrent : before.1 = after.1)
    (evaluates : MotherPhysicalLaws.eval actionLaw (before.1, before.2.val) = after.2.val) :
    generatorAction typeLaw actionLaw before = some after := by
  rcases before with ⟨current, value, member⟩
  rcases after with ⟨afterCurrent, afterValue, afterMember⟩
  dsimp only at sameCurrent evaluates
  subst afterCurrent
  dsimp only [generatorAction]
  rw [evaluates]
  exact dif_pos afterMember

theorem wordAction_eq_mapDomain (typeLaw actionLaw : Law)
    (next : Generator typeLaw → Generator typeLaw)
    (generated : ∀ generator, generatorAction typeLaw actionLaw generator = some (next generator))
    (word : Carrier typeLaw) :
    wordAction typeLaw actionLaw word = some (Finsupp.mapDomain next word) := by
  simp [wordAction, generated, Finsupp.mapDomain]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourceTypeOrigin
