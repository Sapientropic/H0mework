import H0mework.Physics.MotherDeclarationsPhysical.LawsCompletion
import H0mework.Physics.MotherProgrammesFormation.Declarations.UnitSource.Factory
import H0mework.Physics.MotherDeclarationsPhysical.EventsDuration

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource

open MotherStreamLaws MotherClosedRestrictions

noncomputable section

abbrev Current := PhysicalCoverage.Current
abbrev Duration := PhysicalCoverage.Duration
abbrev ledgerSource := MotherDurationExposure.ledgerSource
abbrev OccurrenceAt (current : Current) := MotherDurationExposure.OccurrenceAt current
abbrev Body := ℕ ⊕ MotherUnitSource.Body
abbrev Input := Current × Duration × Body

def bodySamples : Body → Stream :=
  MotherUnitSource.tagged (fun node => fun _ => (node : ℝ)) MotherUnitSource.bodySamples

theorem bodySamples_injective : Function.Injective bodySamples := by
  apply MotherUnitSource.tagged_injective
  · intro first last same
    exact Nat.cast_injective (congrFun same 0)
  · exact MotherUnitSource.bodySamples_injective

def sideSamples (input : Duration × Body) : Stream :=
  pairStream (fun _ => input.1.val) (bodySamples input.2)

theorem sideSamples_injective : Function.Injective sideSamples := by
  intro first last same
  have durations := congrFun (congrArg firstStream same) 0
  have bodies := congrArg lastStream same
  apply Prod.ext
  · apply Subtype.ext
    simpa only [sideSamples, first_pair] using durations
  · apply bodySamples_injective
    simpa only [sideSamples, last_pair] using bodies

/-- The complete raw current remains the original first component. -/
def inputAt (input : Input) : MotherPhysicalLaws.Input := (input.1, sideSamples input.2)

theorem inputAt_injective : Function.Injective inputAt := by
  intro first last same
  have currents : first.1 = last.1 := congrArg (fun input : MotherPhysicalLaws.Input => input.1) same
  have sides : sideSamples first.2 = sideSamples last.2 :=
    congrArg (fun input : MotherPhysicalLaws.Input => input.2) same
  exact Prod.ext currents (sideSamples_injective sides)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherPhysicalSource
