import H0mework.Versions.R9c73a630.Chemistry.LAlanineContinuousChecks.AOCalculatedData
import H0mework.Chemistry.LAlanineSignedEvaluator.Contraction

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix

open Lean Elab Term Command SourceRectangle SourceSignedEvaluator SourceFiniteData
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Inertia.SourceParsing

def sourceMatrixText : String := include_str "../../../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/continuous/source/field0-signed-matrix.json"

elab "generateSignedMatrixCache" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash sourceMatrixText == "04dad9752f5f99a6d500ec4317120587c6a990c576323536292c17b1ba0f4cf8" do
    throwError "signed matrix source changed"
  let packet ← parse sourceMatrixText
  unless (← decode String (← field packet "ao_source_sha256")) ==
      "c90a34819cd8854b8fc4f7ab22ab19b493683b2e9523b154627bf2684fb743fd" &&
      (← decode String (← field packet "gaussian_source_sha256")) == hash SourceFiniteData.sourceText do
    throwError "matrix must use the actual source AO and original D3"
  for (familyName, key, width) in [("first", "first_matrix", 98), ("bilinear", "bilinear_matrix", 20)] do
    let rows ← decode (Array Json) (← field packet key)
    unless rows.size == 20 do throwError "signed matrix derivative census"
    for left in [:20] do
      let row ← decode (Array (Array Int)) rows[left]!
      unless row.size == width && row.all (fun entry => entry.size == 2 && entry[0]! ≤ entry[1]!) do
        throwError "signed matrix interval row"
      let data := row.map fun entry => (entry[0]!, entry[1]!)
      let name := (← getCurrNamespace) ++ Name.mkSimple (familyName ++ toString left)
      let value := toExpr data
      let type ← Meta.inferType value
      addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })

generateSignedMatrixCache

noncomputable def calculatedFirst (left : SourceRectangle.Jet) (right : Basis) : Pair :=
  integerInterval ((![first0, first1, first2, first3, first4, first5, first6, first7, first8, first9,
    first10, first11, first12, first13, first14, first15, first16, first17, first18, first19] left)[right.val]!)

noncomputable def calculatedBilinear (left right : SourceRectangle.Jet) : Pair :=
  integerInterval ((![bilinear0, bilinear1, bilinear2, bilinear3, bilinear4, bilinear5, bilinear6,
    bilinear7, bilinear8, bilinear9, bilinear10, bilinear11, bilinear12, bilinear13, bilinear14,
    bilinear15, bilinear16, bilinear17, bilinear18, bilinear19] left)[right.val]!)

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceSignedMatrix
