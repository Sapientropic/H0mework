import H0mework.Versions.R2.Physics.MotherProgrammesFormation.Declarations.Cumulative.ArenaTheory.Coordinates

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
open MotherArenaNetwork MotherInventoryAdmission
open ResponsibilityLifecycle LivingLawEvolution ConstructiveRoot
open scoped Classical
noncomputable section
variable {rank : Ordinal.{0}}
local notation "B" => MotherArenaHigher.Base rank
local notation "M" => MotherArenaHigher.Material rank

abbrev Version (material : M) := {code : B // bit material 0 code}
abbrev Law (material : M) := {code : B // bit material 1 code}

variable {N : WorldRelationNetwork.{0}} (coordinates : Coordinates (rank := rank) N)
    (material : MotherArenaHigher.Material rank)

abbrev Expression (support : N.Support) := {code : B // r2 material 2 (coordinates.support support) code}
abbrev Realization (support : N.Support) (obstruction : N.ObstructionAt support) :=
  {code : B // r3 material 3 (coordinates.support support) (coordinates.obstruction support obstruction) code}
abbrev RealizationWithout (law : Law material) (support : N.Support) (obstruction : N.ObstructionAt support) :=
  {code : B // r4 material 4 law.val (coordinates.support support) (coordinates.obstruction support obstruction) code}
abbrev TheoremMember (support : N.Support) (expression : Expression coordinates material support) :=
  {code : B // r3 material 5 (coordinates.support support) expression.val code}

structure DataCheck : Prop where
  version : ∃! version : Version material, bit material 6 version.val
  denotes : ∀ support (expression : Expression coordinates material support),
    ∃! claim : N.Claim, r3 material 7 (coordinates.support support) expression.val (coordinates.claim claim)

def denotes (checked : DataCheck coordinates material) {support : N.Support}
    (expression : Expression coordinates material support) : N.Claim :=
  Classical.choose (checked.denotes support expression)

abbrev ExpressionPoint := Σ support : N.Support, Expression coordinates material support

def expressionAddress : ExpressionPoint coordinates material ↪ B :=
  MotherArenaObligation.sigmaEmbedding coordinates.support (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)

abbrev TheoremPresentations (checked : DataCheck coordinates material) :=
  (point : ExpressionPoint coordinates material) →
    ConstructivePresentation (TheoremMember coordinates material point.1 point.2)
      (N.HoldsAt point.1 (denotes coordinates material checked point.2))

def formTheoremPresentations (checked : DataCheck coordinates material) (programme : M) :
    Option (TheoremPresentations coordinates material checked) :=
  MotherArenaAdmission.formPresentationSection (expressionAddress coordinates material)
    (fun _ => ⟨Subtype.val, fun _ _ same => Subtype.ext same⟩)
    (fun point => coordinates.holds point.1 (denotes coordinates material checked point.2)) programme

def theory (checked : DataCheck coordinates material)
    (presentations : TheoremPresentations coordinates material checked) : TheoryState N where
  inventory := {
    Version := Version material
    version := Classical.choose checked.version
    Law := Law material
    RealizationAt := fun {support} obstruction => Realization coordinates material support obstruction
    RealizationWithoutAt := fun law {support} obstruction => RealizationWithout coordinates material law support obstruction }
  ExpressionAt := Expression coordinates material
  denotes := denotes coordinates material checked
  TheoremAt := fun {support} expression => TheoremMember coordinates material support expression
  theoremPresentation := fun {support} expression => presentations ⟨support, expression⟩

def formTheoryAt (programme : M) : Option (TheoryState N) :=
  if checked : DataCheck coordinates material then
    (formTheoremPresentations coordinates material checked programme).map (theory coordinates material checked)
  else none

def formTheoryParts (parent material programme : M) :
    Option (Σ declaration : (Σ value : SourcePair, PresentationData value), TheoryState declaration.1.1.1.1.1.1) :=
  (MotherArenaAdmission.formDeclarationData parent).pbind (fun ⟨value, data⟩ formed =>
    (formTheoryAt (coordinatesOfData parent value data formed) material programme).map
      (fun lawSurface => ⟨⟨value, data⟩, lawSurface⟩))

/-- The exact original law-surface declaration follows the complete sources
and admission programmes. No replacement by rootSemantic is performed. -/
def formTheory (material : M) :=
  let parts := MotherArenaHigher.split rank material
  let tail := MotherArenaHigher.split rank parts.2
  formTheoryParts parts.1 tail.1 tail.2

end
end SaturationMonoid.PhysicsCore.Stage10.SourceUniqueness.MotherArenaTheory
