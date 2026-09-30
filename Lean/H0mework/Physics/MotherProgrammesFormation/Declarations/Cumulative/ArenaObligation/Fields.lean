import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaObligation.Coordinates
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Obligation.Fields

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
open MotherArenaNetwork MotherFullCompiler MotherSourcePrograms MotherExactPrograms MotherArenaPrograms
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
open MotherObligationOrigin
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

variable {N : WorldRelationNetwork.{0}} {V : ConstructiveRoot.Vocabulary.{0}}
    (source : SourceNativeSource N V) (R : RestructuringVocabulary.{0})

def domainAddress (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (world : WorldCoordinates (rank := rank) N) (vocabulary : VocabularyCoordinates (rank := rank) R) :
    ∀ index, Domain source R index ↪ B
  | 0 => coordinates.occurrence
  | 1 => productEmbedding coordinates.occurrence (sigmaEmbedding world.support world.entry)
  | 2 => vocabulary.obligation
  | 3 => vocabulary.observation
  | 4 => vocabulary.incidence
  | 5 => vocabulary.lineage

def codomainAddress (world : WorldCoordinates (rank := rank) N) (vocabulary : VocabularyCoordinates (rank := rank) R) :
    ∀ index, Codomain (N := N) R index ↪ B
  | 0 => vocabulary.event
  | 1 => vocabulary.obligation
  | 2 => world.responsibility
  | 3 => world.anchor
  | 4 => world.incidence
  | 5 => world.lineage

variable {source R}

variable (coordinates : MotherArenaCompiler.Coordinates (rank := rank) source) (world : WorldCoordinates (rank := rank) N) (vocabulary : VocabularyCoordinates (rank := rank) R)

def FieldCheck (material : M) : Prop :=
  ∀ (index : Fin 6) (input : Domain source R index), ∃! output : Codomain (N := N) R index,
    r2 material index.val (domainAddress source R coordinates world vocabulary index input)
      (codomainAddress R world vocabulary index output)

def generatedFields (material : M) (checked : FieldCheck coordinates world vocabulary material) : Fields source R :=
  fun index input => Classical.choose (checked index input)

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaObligation
