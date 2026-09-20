import H0mework.Physics.MotherLaws.StreamCompletion
import H0mework.Physics.MotherProgrammesFormationCoordinates.Stream
import H0mework.Realization.SourceComparison.RawConsumption

set_option autoImplicit false

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawInterpreter

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot

noncomputable section

/-- The fixed mother executor takes only a formed law and a formed initial
material. Emit and event update retain their original distinct roles. -/
def dynamics (law : MotherStreamLaws.Law) (initial : MotherStreamFormation.Carrier) :
    RawGeneratedRoot.Dynamics where
  State := MotherStreamLaws.Stream
  EventAt := fun _ => MotherStreamLaws.Stream
  initial := MotherStreamFormation.read initial
  emit := MotherStreamLaws.eval law
  update := fun event => MotherStreamLaws.eval law event

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherLawInterpreter
