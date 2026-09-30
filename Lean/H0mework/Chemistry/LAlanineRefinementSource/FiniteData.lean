import H0mework.Chemistry.LAlanineRefinementDensity.GaussianModel
import H0mework.Chemistry.LAlanineBasinPartition.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFiniteData

open Lean Elab Term Command
open SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025
open Inertia.SourceParsing SourceGaussianModel

abbrev Basis := Fin 98
abbrev JetIndex := Fin 35

structure RawTerm where
  atom : Nat
  weight : Int × Nat
  exponent : Int × Nat
  powers : Array Nat
  levels : Array Nat
  deriving Inhabited, ToExpr

def ratRead (p : Int × Nat) : ℚ := (p.1 : ℚ) / p.2

def centreRead (points : Array (Array (Int × Nat))) (atom : Nat) : Fin 3 → ℚ :=
  fun axis => ratRead ((points[atom]!)[axis.val]!)

def termRead (points : Array (Array (Int × Nat))) (raw : RawTerm) : SourceGaussianModel.Term where
  weight := ratRead raw.weight
  exponent := ratRead raw.exponent
  centre := centreRead points raw.atom
  powers := fun axis => raw.powers[axis.val]!

def orbitalRead (points : Array (Array (Int × Nat))) (rows : Array (Array RawTerm)) :
    Basis → List SourceGaussianModel.Term := fun basis => (rows[basis.val]!).toList.map (termRead points)

def matrixRead (rows : Array (Array (Int × Nat))) : Basis → Basis → ℚ :=
  fun i j => ratRead ((rows[i.val]!)[j.val]!)

def jetRead (rows : Array (Array Nat)) : JetIndex → MultiIndex :=
  fun jet axis => (rows[jet.val]!)[axis.val]!

def boundRead (rows : Array (Array Nat)) : JetIndex → Basis → ℚ :=
  fun jet basis => (((rows[jet.val]!)[basis.val]! : Nat) : ℚ) / 10 ^ 9

def matrixBoundRead (rows : Array (Array Nat)) : Basis → Basis → ℚ :=
  fun i j => (((rows[i.val]!)[j.val]! : Nat) : ℚ) / 10 ^ 12

def derivativeBoundRead (rows : Array Nat) : JetIndex → ℚ :=
  fun jet => (rows[jet.val]! : ℚ)

def integerOrbitalRead (rows : Array (Array Nat)) : JetIndex → Basis → Nat :=
  fun jet basis => (rows[jet.val]!)[basis.val]!

def integerMatrixRead (rows : Array (Array Nat)) : Basis → Basis → Nat :=
  fun i j => (rows[i.val]!)[j.val]!

def sourceText : String := include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/inertia/basin_refinement/source/gaussian-jets.json"

private def declareReadout (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

private def readPair (value : Json) : TermElabM (Int × Nat) := do
  let xs ← decode (Array Json) value
  unless xs.size == 2 do throwError "Gaussian source rational shape"
  let n ← decode Int xs[0]!
  let d ← decode Nat xs[1]!
  unless d > 0 do throwError "Gaussian source denominator"
  return (n, d)

private def readPairs (value : Json) (width : Nat) : TermElabM (Array (Int × Nat)) := do
  let row ← decode (Array Json) value
  unless row.size == width do throwError "Gaussian source width"
  row.mapM readPair

elab "generateSourceGaussianFiniteData" : command => liftTermElabM do
  unless SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex sourceText ==
      "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" do
    throwError "Gaussian source packet changed"
  let packet ← parse sourceText
  let join ← field packet "source"
  unless (← decode String (← field join "basin_packet_sha256")) == BasinPartition.SourceParsing.sourceArtifactSha256 do
    throwError "Gaussian source must be this installed basin current"
  let source ← field packet "gaussian_source"
  let points ← (← decode (Array Json) (← field source "centres")).mapM (readPairs · 3)
  unless points.size == 13 do throwError "Gaussian source atom census"
  let rawRows ← decode (Array Json) (← field source "terms")
  unless rawRows.size == 98 do throwError "Gaussian source AO census"
  let rows ← rawRows.mapM fun row => do
    let raw ← decode (Array Json) row
    raw.mapM fun term => do
      let atom ← decode Nat (← field term "atom")
      let powers ← decode (Array Nat) (← field term "powers")
      let levels ← decode (Array Nat) (← field term "decay_levels")
      unless atom < 13 && powers.size == 3 && levels.size == 3 do throwError "Gaussian primitive incidence"
      return RawTerm.mk atom (← readPair (← field term "weight"))
        (← readPair (← field term "exponent")) powers levels
  declareReadout `rawTerms (toExpr rows)
  declareReadout `sourceTerms (← Meta.mkAppM ``orbitalRead #[toExpr points, toExpr rows])
  let dm ← (← decode (Array Json) (← field source "density_matrix")).mapM (readPairs · 98)
  unless dm.size == 98 do throwError "Gaussian source density census"
  declareReadout `densityMatrix (← Meta.mkAppM ``matrixRead #[toExpr dm])
  let geometry ← field packet "geometry"
  let centre ← readPairs (← field geometry "centre") 3
  declareReadout `boxCentre (← Meta.mkAppM ``centreRead #[toExpr #[centre], toExpr (0 : Nat)])
  declareReadout `boxRadius (← Meta.mkAppM ``ratRead #[toExpr (← readPair (← field geometry "radius"))])
  let bound ← field packet "generated_bounds"
  for (name, key, height, width, readout) in
      [(`jetMulti, "multiindices", 35, 3, ``jetRead),
       (`orbitalBound, "orbital_integer_bounds", 35, 98, ``boundRead),
       (`densityMatrixBound, "density_matrix_absolute_integer_bounds", 98, 98, ``matrixBoundRead)] do
    let rows ← decode (Array (Array Nat)) (← field bound key)
    unless rows.size == height && rows.all (fun row => row.size == width) do throwError "Gaussian bound census"
    declareReadout name (← Meta.mkAppM readout #[toExpr rows])
    if name == `orbitalBound then
      declareReadout `orbitalIntegerBound (← Meta.mkAppM ``integerOrbitalRead #[toExpr rows])
    if name == `densityMatrixBound then
      declareReadout `densityMatrixIntegerBound (← Meta.mkAppM ``integerMatrixRead #[toExpr rows])
  let densityBounds ← decode (Array Nat) (← field bound "density_derivative_bounds")
  unless densityBounds.size == 35 do throwError "Gaussian density derivative census"
  declareReadout `densityBound (← Meta.mkAppM ``derivativeBoundRead #[toExpr densityBounds])

set_option maxRecDepth 4096 in
generateSourceGaussianFiniteData

theorem orbitalBound_integer (d : JetIndex) (j : Basis) :
    orbitalBound d j = (orbitalIntegerBound d j : ℚ) / 10 ^ 9 := rfl

theorem densityMatrixBound_integer (i j : Basis) :
    densityMatrixBound i j = (densityMatrixIntegerBound i j : ℚ) / 10 ^ 12 := rfl

end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.SourceFiniteData
