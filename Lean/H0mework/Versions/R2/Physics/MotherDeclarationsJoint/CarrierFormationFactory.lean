import H0mework.Physics.MotherDeclarationsJoint.CarrierFormationOrbit
import H0mework.Versions.R2.Physics.MotherDeclarationsJoint.CarrierFormationWords

set_option autoImplicit false
set_option synthInstance.maxSize 4096

namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier

open ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open SourceGeneratedIntegralCoherentJointAction
open MotherTypeFormation MotherSourceTypeOrigin MotherFamilyOccurrence

noncomputable section

abbrev Joint := ActualFormation.jointInput.Carrier

def seedValue : ActualFormation.IntegralCarrier → Joint := ActualFormation.jointInput.seedLift

def orbitValue (stage : ℕ) (word : ActualFormation.IntegralCarrier) : Joint :=
  MotherOrbitWords.orbit ActualFormation.jointInput (stage, word)

abbrev OrbitMaterial := MotherVisit × WordMaterial
abbrev Material := Σ parent : MotherVisit,
  Fin (StageEightDiscreteFormation.codeOf parent) → OrbitMaterial

def items (material : Material) : List OrbitMaterial := List.ofFn material.2

def formTerm (typeLaw : Law) (material : OrbitMaterial) : Option Joint :=
  (formWord typeLaw material.2).map fun word =>
    orbitValue (StageEightDiscreteFormation.codeOf material.1) (readWord typeLaw word)

/-- Integral and next are computed from the same finite word by actual mother-law evaluation. -/
def actTerm (typeLaw actionLaw : Law) (material : OrbitMaterial) : Option Joint :=
  (formWord typeLaw material.2).bind fun word =>
    (iterateWord typeLaw actionLaw (StageEightDiscreteFormation.codeOf material.1) word).bind fun current =>
      (wordAction typeLaw actionLaw current).map fun after =>
        seedValue (readWord typeLaw after) +
          (orbitValue (StageEightDiscreteFormation.codeOf material.1) (readWord typeLaw word) -
            seedValue (readWord typeLaw current))

def sumOptions {Value : Type*} [Zero Value] [Add Value] : List (Option Value) → Option Value
  | [] => some 0
  | first :: rest => first.bind fun value => (sumOptions rest).map (value + ·)

def form (typeLaw : Law) (material : Material) : Option Joint :=
  sumOptions ((items material).map (formTerm typeLaw))

def act (typeLaw actionLaw : Law) (material : Material) : Option Joint :=
  sumOptions ((items material).map (actTerm typeLaw actionLaw))

theorem formTerm_eq (typeLaw : Law) (material : OrbitMaterial) (word : Carrier typeLaw)
    (formed : formWord typeLaw material.2 = some word) :
    formTerm typeLaw material =
      some (orbitValue (StageEightDiscreteFormation.codeOf material.1) (readWord typeLaw word)) :=
  congrArg (Option.map fun word =>
    orbitValue (StageEightDiscreteFormation.codeOf material.1) (readWord typeLaw word)) formed

theorem actTerm_eq (typeLaw actionLaw : Law) (material : OrbitMaterial)
    (word current after : Carrier typeLaw)
    (formed : formWord typeLaw material.2 = some word)
    (iterated : iterateWord typeLaw actionLaw (StageEightDiscreteFormation.codeOf material.1) word = some current)
    (acted : wordAction typeLaw actionLaw current = some after) :
    actTerm typeLaw actionLaw material =
      some (seedValue (readWord typeLaw after) +
        (orbitValue (StageEightDiscreteFormation.codeOf material.1) (readWord typeLaw word) -
          seedValue (readWord typeLaw current))) := by
  simp only [actTerm, formed, Option.bind_some, iterated, acted, Option.map_some]

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherJointCarrier
