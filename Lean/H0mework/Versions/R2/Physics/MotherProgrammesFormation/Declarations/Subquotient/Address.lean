import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Subquotient.Section

/-! Source coordinates of already formed dependent quotient values.
Recovery uses the actual member factory; these addresses are not a decoder
or a type-formation condition supplied by an original target process. -/

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotient

noncomputable section

def address (material : Material) (index : Base) (value : Fiber material index) : Base :=
  (every_member material index value).choose

theorem address_recovers (material : Material) (index : Base) (value : Fiber material index) :
    formMember material index (address material index value) = some value :=
  (every_member material index value).choose_spec

theorem address_injective (material : Material) (index : Base) :
    Function.Injective (address material index) := by
  intro first last same
  apply Option.some.inj
  exact (address_recovers material index first).symm.trans
    ((congrArg (formMember material index) same).trans (address_recovers material index last))

def totalAddress (material : Material) (value : Total material) : Base :=
  MotherHigherLawFamily.pair (value.1, address material value.1 value.2)

theorem totalAddress_recovers (material : Material) (value : Total material) :
    formTotal material (MotherHigherLawFamily.unpair (totalAddress material value)).1
      (MotherHigherLawFamily.unpair (totalAddress material value)).2 = some value := by
  rcases value with ⟨index, value⟩
  unfold totalAddress
  rw [MotherHigherLawFamily.unpair_pair]
  exact congrArg (Option.map (Sigma.mk index)) (address_recovers material index value)

theorem totalAddress_injective (material : Material) : Function.Injective (totalAddress material) := by
  intro first last same
  apply Option.some.inj
  exact (totalAddress_recovers material first).symm.trans
    ((congrArg (fun code => formTotal material (MotherHigherLawFamily.unpair code).1
      (MotherHigherLawFamily.unpair code).2) same).trans (totalAddress_recovers material last))

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSubquotient
