import H0mework.Physics.MotherDeclarationsType.FormationFibre
import H0mework.Physics.MotherDeclarationsPhysical.EventsDuration

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTypeFormation

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open MotherStreamLaws

noncomputable section

abbrev Generator (law : Law) := Σ current : Current, Fiber law current
abbrev MemberMaterial := MotherPointwiseLaws.Law × MotherStreamFormation.Carrier

def memberInput (material : MemberMaterial) : MotherPhysicalLaws.Input :=
  (MotherRawCurrent.readCurrent material.1, MotherStreamFormation.read material.2)

/-- Membership is produced by this law's evaluation, never supplied by a caller. -/
def formMember (law : Law) (material : MemberMaterial) : Option (Generator law) := by
  classical
  exact if member : MotherPhysicalLaws.eval law (memberInput material) 0 = 0 then
    some ⟨(memberInput material).1, (memberInput material).2, member⟩
  else none

theorem every_generator (law : Law) (generator : Generator law) :
    ∃ material : MemberMaterial, formMember law material = some generator := by
  classical
  rcases generator with ⟨current, value, member⟩
  obtain ⟨currentMaterial, _, currentRead⟩ := MotherRawCurrent.every_current current
  obtain ⟨valueMaterial, valueRead⟩ := MotherStreamFormation.read_surjective value
  refine ⟨(currentMaterial, valueMaterial), ?_⟩
  subst current value
  dsimp only [formMember, memberInput]
  exact dif_pos member

theorem formed_member_retains_input (law : Law) (material : MemberMaterial)
    (generator : Generator law) (formed : formMember law material = some generator) :
    memberInput material = (generator.1, generator.2.val) := by
  classical
  unfold formMember at formed
  split at formed
  · cases Option.some.inj formed
    rfl
  · cases formed

abbrev source := MotherDurationExposure.ledgerSource
abbrev OccurrenceAt (current : Current) := MotherDurationExposure.OccurrenceAt current

/-- Projection ranges over the whole dependent total space, including later fibres. -/
def projectionLaw (law : Law) : SourceNativeProjectionLaw source := by
  classical
  exact
    { Projection := Generator law
      ActiveAt := fun projection {current} _ => PLift (projection.1 = current)
      InactiveAt := fun projection {current} _ => PLift (projection.1 ≠ current)
      classify := fun projection {current} _ =>
        if same : projection.1 = current then .inl ⟨same⟩ else .inr ⟨same⟩
      PayloadAt := fun _ {current} _ _ => Fiber law current
      project := fun projection {_current} _ active => active.down ▸ projection.2 }

theorem every_current_projection (law : Law) (generator : Generator law)
    (occurrence : OccurrenceAt generator.1) :
    (projectionLaw law).outcomeAt generator occurrence =
      .inl ⟨⟨rfl⟩, generator.2⟩ := by
  simp [SourceNativeProjectionLaw.outcomeAt, projectionLaw]

theorem all_members_consumed (law : Law) (generator : Generator law)
    (occurrence : OccurrenceAt generator.1) :
    ∃ material : MemberMaterial,
      formMember law material = some generator ∧
      (projectionLaw law).outcomeAt generator occurrence =
        .inl ⟨⟨rfl⟩, generator.2⟩ := by
  obtain ⟨material, formed⟩ := every_generator law generator
  exact ⟨material, formed, every_current_projection law generator occurrence⟩

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherTypeFormation
