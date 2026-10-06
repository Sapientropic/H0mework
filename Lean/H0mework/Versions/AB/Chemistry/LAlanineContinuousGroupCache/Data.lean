import H0mework.Versions.AB.Chemistry.LAlanineContinuousSource.SourceIncidence

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGroupCache

open Lean Elab Term Command SourceRectangle SourceSignedEvaluator SourceGaussianModel
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

structure RawCache where
  relative : Array (Int × Int)
  radial : Int × Int
  exponential : Int × Int
  polynomial : Array (Array (Array (Int × Int)))
  deriving Inhabited, ToExpr

def sourceText : String := include_str "../../../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/source/field0-group-cache.json"

private def intervalRead (value : Json) : TermElabM (Int × Int) := do
  let row ← decode (Array Int) value
  unless row.size == 2 && row[0]! ≤ row[1]! do throwError "source cache interval"
  return (row[0]!, row[1]!)

private def declare (suffix : Name) (value : Expr) : TermElabM Name := do
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)
  return name

elab "generateSourceGroupCache" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash sourceText == "69c46abe167ac4d85158ff580fa049575de9a39e56f8c4a1ce80576b9690d53a" do
    throwError "source execution cache changed"
  let packet ← parse sourceText
  unless (← decode String (← field packet "source_sha256")) == hash SourceFiniteData.sourceText &&
      (← decode String (← field packet "rectangle_sha256")) == hash SourceRectangle.rectangleText &&
      (← decode Nat (← field packet "field")) == 0 &&
      (← decode Nat (← field packet "scale_bits")) == 160 do throwError "same source rectangle cache"
  let original ← parse SourceRectangle.rectangleText
  let sourceGroups ← decode (Array Json) (← field original "gaussian_groups")
  let groups ← decode (Array Json) (← field packet "groups")
  unless groups.size == 94 do throwError "complete source group census"
  let mut refs : List Expr := []
  for g in [:94] do
    let row := groups[g]!
    let members ← decode (Array Json) (← field sourceGroups[g]! "term_members")
    unless (← decode Nat (← field row "group")) == g &&
        (← field row "source_member") == members[0]! do throwError "source representative incidence"
    let relative ← decode (Array Json) (← field row "relative")
    unless relative.size == 3 do throwError "source axis census"
    let rawPolynomial ← decode (Array (Array (Array Json))) (← field row "polynomial")
    unless rawPolynomial.size == 3 && rawPolynomial.all (fun row => row.size == 3 && row.all (fun orders => orders.size == 4)) do
      throwError "source polynomial axis/power/order census"
    let polynomial ← rawPolynomial.mapM fun axes => axes.mapM fun powers => powers.mapM intervalRead
    let value : RawCache := ⟨← relative.mapM intervalRead, ← intervalRead (← field row "radial"),
      ← intervalRead (← field row "exponential"), polynomial⟩
    let name ← declare (Name.mkSimple s!"row{g}") (toExpr value)
    refs := refs ++ [Lean.mkConst name]
  let rows ← Meta.mkArrayLit (Lean.mkConst ``RawCache) refs
  discard <| declare `rows rows

generateSourceGroupCache

noncomputable section

def cachedRelative (g : Group) (axis : Fin 3) : Pair :=
  integerInterval ((rows[g.val]!).relative[axis.val]!)
def cachedRadial (g : Group) : Pair := integerInterval (rows[g.val]!).radial
def cachedExp (g : Group) : Pair := integerInterval (rows[g.val]!).exponential
def cachedPoly (g : Group) (axis power : Fin 3) (order : Fin 4) : Pair :=
  integerInterval ((((rows[g.val]!).polynomial[axis.val]!)[power.val]!)[order.val]!)

def sourceRelative (g : Group) (axis : Fin 3) : Pair := relative (groupTerm g) (actualBox 0) axis
def sourceRadial (g : Group) : Pair := radialPair (groupTerm g) (actualBox 0)
def sourceExpFromRadial (g : Group) : Pair :=
  exponential (cachedRadial g) (groupSteps 0 g).1 (groupSteps 0 g).2
def sourcePolyFromRelative (g : Group) (axis power : Fin 3) (order : Fin 4) : Pair :=
  jetHorner (groupExponent g) power.val order.val (cachedRelative g axis)

end
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceGroupCache
