import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1LiveEditing.Event
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1InitiationTermination.UnifiedBoundary
import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1Recycling.Source

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1LiveEditing
noncomputable section
open CPS1ResourceExecution CPS1Deamination
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025
variable {frame : CPS1Recycling.Frame}

inductive RawSupply
  | aminoAcid (aa : AA)
  | trna (aa : AA)
  | actor (factor : Actor)
  | atp | gtp | water | initiatorTrna | subunit40 | subunit60 | ribosome
  deriving DecidableEq

def RawSupply.species : RawSupply → CPS1ResourceExecution.Species
  | .aminoAcid aa => .freeAA aa
  | .trna aa => .tRNA aa
  | .actor factor => .actor factor
  | .atp => .atp
  | .gtp => .gtp
  | .water => .water
  | .initiatorTrna => .initiatorTRNA
  | .subunit40 => .subunit40
  | .subunit60 => .subunit60
  | .ribosome => .ribosome80

inductive TranslationFailure
  | missingCoding
  | codingHasNoPeptide
  | nonMethionineStart

structure TranslationEvent (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply) where
  genomic : VerifiedResume current water
  coding : Bases
  codingSource : genomic.event.coding = some coding
  peptide : Peptide
  peptideSource : genomic.event.peptide = some peptide
  initiator : peptide.1 = .M
  program : List Reaction
  programSource : program = CPS1InitiationTermination.UnifiedBoundary.compile peptide.2
  available : Stock
  availableSource : available = genomic.event.result.stock ++ raw.map RawSupply.species
  native : Execution
  actual : native = execute program available
  generatedFrame : CPS1Recycling.Frame
  frameSource : generatedFrame = ⟨coding,peptide,program,native⟩
  whole : (available ++ credit native.fired).Perm (native.stock ++ debit native.fired)

private def makeTranslation (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply)
    (genomic : VerifiedResume current water) (coding : Bases) (codingSource : genomic.event.coding = some coding)
    (peptide : Peptide) (peptideSource : genomic.event.peptide = some peptide) (initiator : peptide.1 = .M) :
    TranslationEvent current water raw :=
  let program := CPS1InitiationTermination.UnifiedBoundary.compile peptide.2
  let available := genomic.event.result.stock ++ raw.map RawSupply.species
  let native := execute program available
  ⟨genomic,coding,codingSource,peptide,peptideSource,initiator,program,rfl,available,rfl,native,rfl,
    ⟨coding,peptide,program,native⟩,rfl,native_execution_whole program available⟩

inductive TranslationDisposition (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply)
  | genomicRejected (original : GenomicDisposition current water)
  | decodingRejected (genomic : VerifiedResume current water) (unspent : Stock)
      (unspentSource : unspent = genomic.event.result.stock ++ raw.map RawSupply.species)
      (failure : TranslationFailure)
  | translated (event : TranslationEvent current water raw)

def translateLive (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply) :
    TranslationDisposition current water raw :=
  match genomicUpdate current water with
  | GenomicDisposition.rejected slice available availableSource saved savedSource failure =>
    .genomicRejected (.rejected slice available availableSource saved savedSource failure)
  | GenomicDisposition.updated genomic =>
    match codingSource : genomic.event.coding with
    | none => .decodingRejected genomic (genomic.event.result.stock ++ raw.map RawSupply.species) rfl .missingCoding
    | some coding =>
      match peptideSource : genomic.event.peptide with
      | none => .decodingRejected genomic (genomic.event.result.stock ++ raw.map RawSupply.species) rfl .codingHasNoPeptide
      | some peptide =>
        if initiator : peptide.1 = .M then
          .translated (makeTranslation current water raw genomic coding codingSource peptide peptideSource initiator)
        else .decodingRejected genomic (genomic.event.result.stock ++ raw.map RawSupply.species) rfl .nonMethionineStart

theorem translation_actual (current : CPS1ReactiveField.Occurrence frame) (water : Nat) (raw : List RawSupply) :
    match translateLive current water raw with
    | .genomicRejected _ => True
    | .decodingRejected genomic unspent _ _ => unspent = genomic.event.result.stock ++ raw.map RawSupply.species
    | .translated event =>
      event.native = execute event.program event.available ∧
      event.generatedFrame.messageTemplate = event.coding ∧ event.generatedFrame.peptide = event.peptide ∧
      event.generatedFrame.native = event.native ∧
      (event.available ++ credit event.native.fired).Perm (event.native.stock ++ debit event.native.fired) := by
  cases translateLive current water raw with
  | genomicRejected original => exact True.intro
  | decodingRejected genomic unspent source failure => exact source
  | translated event =>
    dsimp only
    rw [event.frameSource]
    exact ⟨event.actual,rfl,rfl,rfl,event.whole⟩

end
end CPS1LiveEditing
