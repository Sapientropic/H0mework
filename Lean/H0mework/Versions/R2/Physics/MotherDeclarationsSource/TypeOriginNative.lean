import H0mework.Versions.R2.Physics.MotherDeclarationsType.FormationSource
import H0mework.Versions.R2.Physics.MotherProgrammesFormationActual.History
import H0mework.Versions.R2.Physics.MotherProgrammesFormationCurrent.SpacetimeRecovery

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourceTypeOrigin

open MotherStreamLaws StageNineCanonicalCauchyState

noncomputable section

/-- The original full-field source generator, including its original counter. -/
def sourceSamples (generator : ActualFormation.Generator) : Stream
  | 0 => generator.1
  | index + 1 => WholeSpacetimeMaterial.samples generator.2 index

def sourceRead (samples : Stream) : ActualFormation.Generator :=
  (Nat.floor (samples 0), WholeSpacetimeMaterial.decodeSamples (fun index => samples (index + 1)))

theorem sourceRead_sourceSamples (generator : ActualFormation.Generator) :
    sourceRead (sourceSamples generator) = generator := by
  rcases generator with ⟨index, current⟩
  simp [sourceRead, sourceSamples, WholeSpacetimeMaterial.decodeSamples_samples]

/-- This fixed base is a representation coordinate, not an occurrence anchor. -/
def baseCurrent : MotherPhysicalLaws.Current := (PhysicalCoverage.originalInitial, 0)

def sourceInput (generator : ActualFormation.Generator) : MotherPhysicalLaws.Input :=
  (baseCurrent, sourceSamples generator)

theorem sourceInput_injective : Function.Injective sourceInput := by
  intro left right same
  exact (sourceRead_sourceSamples left).symm.trans
    ((congrArg (fun input : MotherPhysicalLaws.Input => sourceRead input.2) same).trans
      (sourceRead_sourceSamples right))

def sourceFiber (current : MotherTypeFormation.Current) (samples : Stream) : Prop :=
  sourceInput (sourceRead samples) = (current, samples)

theorem sourceFiber_sourceInput (generator : ActualFormation.Generator) :
    sourceFiber (sourceInput generator).1 (sourceInput generator).2 := by
  change sourceInput (sourceRead (sourceSamples generator)) = sourceInput generator
  rw [sourceRead_sourceSamples]

variable (typeLaw : MotherTypeFormation.Law)
variable (typeExact : ∀ current samples,
  MotherPhysicalLaws.eval typeLaw (current, samples) 0 = 0 ↔ sourceFiber current samples)

/-- This equivalence is proved after type formation, not supplied to its factory. -/
def sourceEquiv : MotherTypeFormation.Generator typeLaw ≃ ActualFormation.Generator where
  toFun := fun generated => sourceRead generated.2.val
  invFun := fun generator =>
    ⟨(sourceInput generator).1, (sourceInput generator).2,
      (typeExact _ _).mpr (sourceFiber_sourceInput generator)⟩
  left_inv := by
    rintro ⟨current, samples, member⟩
    have exactInput := (typeExact current samples).mp member
    have currentEq : baseCurrent = current := congrArg Prod.fst exactInput
    subst current
    refine Sigma.ext ?_ ?_
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact congrArg Prod.snd exactInput
  right_inv := sourceRead_sourceSamples

theorem every_native_generator (generator : ActualFormation.Generator) :
    ∃ material : MotherTypeFormation.MemberMaterial,
      MotherTypeFormation.formMember typeLaw material = some ((sourceEquiv typeLaw typeExact).symm generator) :=
  MotherTypeFormation.every_generator typeLaw ((sourceEquiv typeLaw typeExact).symm generator)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherSourceTypeOrigin
