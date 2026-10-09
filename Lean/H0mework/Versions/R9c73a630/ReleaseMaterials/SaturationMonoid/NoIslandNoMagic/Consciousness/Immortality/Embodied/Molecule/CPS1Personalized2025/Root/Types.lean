import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Producer.Closure

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root
inductive Current | registeredSource | generatedProgram | independentResponse deriving DecidableEq, Repr
def nextCurrent : Current → Current
  | .registeredSource => .generatedProgram | .generatedProgram => .independentResponse | .independentResponse => .independentResponse
def OperationAt : Current → Prop
  | .registeredSource => type_of% Molecules.complete_original_chemical_words ∧ type_of% Assay.complete_original_table
  | .generatedProgram => OriginalProgramClosure
  | .independentResponse => type_of% Consumer.complete_program_and_response_consumed ∧ type_of% Consumer.every_consumer_factors
theorem sourceOperation (current : Current) : OperationAt current := by
  cases current with
  | registeredSource => exact ⟨Molecules.complete_original_chemical_words,Assay.complete_original_table⟩
  | generatedProgram => exact sourceGeneratedOriginalProgram
  | independentResponse => exact ⟨Consumer.complete_program_and_response_consumed,Consumer.every_consumer_factors⟩
inductive Responsibility | originalProgramResponse deriving DecidableEq, Repr
inductive Claim | registeredCPS1ProgramAndClinicalResponse deriving DecidableEq, Repr
def captureKey : String := Reifier.packetSha256
def incidenceKey : String := "Musunuru2025/modified-RNA/GRCh38-Q335X/TableS3/single-patient-two-infusions"
def comparisonLineage : String := "Musunuru2025/original-program-independent-assay-and-recorded-clinical-response"
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Root
