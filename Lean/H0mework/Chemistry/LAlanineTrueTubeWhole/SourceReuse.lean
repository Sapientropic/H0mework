import H0mework.Chemistry.LAlanineTrueTubeWhole.SourceData

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeWholeSource

open TrueTubeSource SourceSignedEvaluator
noncomputable section

def prepaidCall (i : Fin 4) : Call := ![0,32,1,33] i
def prepaidField (i : Fin 4) : Field := ![0,0,1,2] i

theorem prepaid_box (i : Fin 4) : callBox (prepaidCall i) = box (prepaidField i) := by
  funext axis
  fin_cases i <;> fin_cases axis <;> rfl

theorem prepaid_field (i : Fin 4) : recordedCallField (prepaidCall i) = recordedField (prepaidField i) := by
  fin_cases i <;> rfl

end
end LAlanine40K2025.BasinRefinement.TrueTubeWholeSource
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
