import H0mework.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaRestructuringVocabulary.Families
import H0mework.Physics.MotherProgrammesFormation.Declarations.NativeSourceOrigin.Restructuring.Vocabulary.Consumer

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
open MotherArenaNetwork MotherRestructuringOrigin ResponsibilityLifecycle
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev Field (base : M) (index : Fin 12) := formedSorts base index
abbrev Obstruction (base families : M) (source : Field base 0) := formedFamilies base families 0 (source, PUnit.unit)
abbrev AnchorBody (base : M) := Field base 8 × Field base 5 × Field base 6

structure DataCheck (base families material : M) : Prop where
  null : ∃! value : Field base 8, bit material 0 value.val
  complement : ∀ value : Field base 8, ∃! next : Field base 8, r2 material 1 value.val next.val
  anchor : ∀ source : Field base 0, ∃! body : AnchorBody base,
    r4 material 2 source.val body.1.val body.2.1.val body.2.2.val
  incidence : ∀ source : Field base 0, ∃! value : Field base 7, r2 material 3 source.val value.val
  demandContent : ∀ (source : Field base 0) (obstruction : Obstruction base families source),
    ∃! content : Field base 1, r3 material 4 source.val obstruction.val content.val
  demandResidual : ∀ (source : Field base 0) (obstruction : Obstruction base families source),
    ∃! residual : Field base 2, r3 material 5 source.val obstruction.val residual.val

namespace DataCheck
variable {base families material : MotherArenaHigher.Material rank} (checked : DataCheck base families material)
def nullValue : Field base 8 := Classical.choose checked.null
def complementValue (value : Field base 8) : Field base 8 := Classical.choose (checked.complement value)
def anchorValue (source : Field base 0) : AnchorBody base := Classical.choose (checked.anchor source)
def incidenceValue (source : Field base 0) : Field base 7 := Classical.choose (checked.incidence source)
def contentValue (source : Field base 0) (obstruction : Obstruction base families source) : Field base 1 :=
  Classical.choose (checked.demandContent source obstruction)
def residualValue (source : Field base 0) (obstruction : Obstruction base families source) : Field base 2 :=
  Classical.choose (checked.demandResidual source obstruction)
end DataCheck

structure Laws {base families material : MotherArenaHigher.Material rank} (checked : DataCheck base families material) : Prop where
  involutive : Function.Involutive checked.complementValue
  nontrivial : checked.nullValue ≠ checked.complementValue checked.nullValue
  registered : ∀ source, (checked.anchorValue source).1 ≠ checked.complementValue (checked.anchorValue source).1

def operations {base families material : MotherArenaHigher.Material rank} (checked : DataCheck base families material) (laws : Laws checked) :
    Operations (formedSorts base) (formedFamilies base families) where
  null := checked.nullValue
  complement := checked.complementValue
  involutive := laws.involutive
  nontrivial := laws.nontrivial
  anchorIdentity := fun source => (checked.anchorValue source).1
  anchorScope := fun source => (checked.anchorValue source).2.1
  anchorLineage := fun source => (checked.anchorValue source).2.2
  anchorRegistered := laws.registered
  incidence := checked.incidenceValue
  demandContent := checked.contentValue _
  demandResidual := checked.residualValue _

/-- All original vocabulary fields are formed before source registration
maps and actual split/merge certifications consume this vocabulary. -/
def formVocabularyParts (base families material : M) : Option RestructuringVocabulary :=
  if checked : DataCheck base families material then
    if laws : Laws checked then some (restructuring (formedSorts base) (formedFamilies base families) (operations checked laws)) else none
  else none

def formVocabulary (material : M) : Option RestructuringVocabulary :=
  let first := (MotherArenaHigher.split rank) material
  let second := (MotherArenaHigher.split rank) first.2
  formVocabularyParts first.1 second.1 second.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaRestructuringVocabulary
