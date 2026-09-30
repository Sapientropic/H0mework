import H0mework.Chemistry.LAlanineTrueTube.SourceData
import H0mework.Chemistry.LAlanineContinuousGroupCache.Data

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.TrueTubeCache

open Lean Elab Term Command SourceGaussianModel SourceSignedEvaluator SourceExponential
open SourceRectangle SourceRectangleChecks SourceFiniteData
open Inertia.SourceParsing

private def rational (value : Json) : TermElabM ℚ := do
  let a ← decode (Array Json) value
  unless a.size == 2 do throwError "source rational pair"
  let n ← decode Int a[0]!
  let d ← decode Nat a[1]!
  unless d > 0 do throwError "source rational denominator"
  return (n : ℚ) / (d : ℚ)

private def integers (a : Pair) : Int × Int := (⌊scale*a.1⌋, ⌈scale*a.2⌉)
private def grid (a : Int × Int) : Pair := ((a.1 : ℚ)/scale, (a.2 : ℚ)/scale)
private def zeroTerm : SourceGaussianModel.Term := ⟨0, 0, fun _ => 0, fun _ => 0⟩

private def declare (suffix : Name) (value : Expr) : TermElabM Name := do
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)
  return name

/-- Same original signed arithmetic; new field input is only its rectangle and reductions. -/
elab "generateTrueTubeFieldCache " index:num : command => liftTermElabM do
  let f := index.getNat
  unless 0 < f && f < 3 do throwError "registered new whole-cell field"
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash SourceFiniteData.sourceText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" &&
      hash SourceRectangle.fieldText == "a366023f2256f1e53c045b6fe9ae951b78876fca4679d7b3ead3e7ca9167c011" do
    throwError "same original Gaussian and group-incidence sources"
  let gaussian ← parse SourceFiniteData.sourceText
  let original ← parse SourceRectangle.fieldText
  let packet ← TrueTubeSource.verifiedPacket
  let source ← field gaussian "gaussian_source"
  let centres ← (← decode (Array (Array Json)) (← field source "centres")).mapM (·.mapM rational)
  let rawTerms ← decode (Array (Array Json)) (← field source "terms")
  unless centres.size == 13 && rawTerms.size == 98 do throwError "source AO and atom census"
  let terms ← rawTerms.mapM fun row => row.mapM fun value => do
    let atom ← decode Nat (← field value "atom")
    let powers ← decode (Array Nat) (← field value "powers")
    unless atom < 13 && powers.size == 3 do throwError "source term coordinates"
    let weight ← rational (← field value "weight")
    let exponent ← rational (← field value "exponent")
    return SourceGaussianModel.Term.mk weight exponent (fun axis => (centres[atom]!)[axis.val]!)
      (fun axis => powers[axis.val]!)
  let fields ← WholeCellSource.sourceArray (← field packet "fields") 3
  let current := fields[f]!
  let coordinates ← (← WholeCellSource.sourceArray (← field current "coordinate_integer_box") 3).mapM
    WholeCellSource.sourceInterval
  let box : Rectangle := fun axis => grid coordinates[axis.val]!
  let reductions ← (← WholeCellSource.sourceArray (← field current "range_reduction_by_group") 94).mapM
    WholeCellSource.sourceReduction
  let groups ← decode (Array Json) (← field original "gaussian_groups")
  unless groups.size == 94 do throwError "source group census"
  let mut computed : Array SourceGroupCache.RawCache := #[]
  let mut groupIndex := terms.map (fun row => Array.replicate row.size 94)
  let mut refs : List Expr := []
  for g in [:94] do
    let members ← decode (Array (Array Nat)) (← field groups[g]! "term_members")
    unless members.size > 0 do throwError "source group representative"
    for address in members do
      unless address.size == 2 && address[0]! < 98 && address[1]! < (terms[address[0]!]!).size do
        throwError "source group member address"
      groupIndex := groupIndex.modify address[0]! (fun row => row.set! address[1]! g)
    let first := members[0]!
    let term := ((terms[first[0]!]!)[first[1]!]?).getD zeroTerm
    let kl := reductions[g]!.1
    let kh := reductions[g]!.2
    let relativeRows := (List.finRange 3).toArray.map (fun axis => integers (relative term box axis))
    let radial := radialPair term box
    let exp := exponential radial kl kh
    let polynomial := (List.finRange 3).toArray.map fun axis =>
      (List.finRange 3).toArray.map fun power =>
        (List.finRange 3).toArray.map fun order =>
          integers (jetHorner term.exponent power.val order.val (relative term box axis))
    let cache : SourceGroupCache.RawCache := ⟨relativeRows, integers radial, integers exp, polynomial⟩
    computed := computed.push cache
    let name ← declare (Name.mkSimple s!"groupRow{g}") (toExpr cache)
    refs := refs ++ [Lean.mkConst name]
  discard <| declare `groupRows (← Meta.mkArrayLit (Lean.mkConst ``SourceGroupCache.RawCache) refs)
  unless groupIndex.all (fun row => row.all (fun g => g < 94)) do
    throwError "complete source term/group registration"
  let jets ← decode (Array (Array Nat)) (← field (← field gaussian "generated_bounds") "multiindices")
  let fieldJets ← decode (Array (Array Nat)) (← field (← field packet "arithmetic") "multiindices")
  unless jets.size == 35 && fieldJets == jets.extract 0 10 do throwError "source low-jet incidence"
  let mut aoRefs : List Expr := []
  for b in [:98] do
    let row := terms[b]!
    let values := (List.range 10).toArray.map fun j =>
      let d := jets[j]!
      let contributions := (List.range row.size).map fun t =>
        let term := (row[t]?).getD zeroTerm
        let cache := computed[(groupIndex[b]!)[t]!]!
        cachedTerm term.weight (grid cache.exponential)
          (fun axis => grid (((cache.polynomial[axis.val]!)[term.powers axis]!)[d[axis.val]!]!))
      integers (contributions.foldr add (point 0))
    let name ← declare (Name.mkSimple s!"aoRow{b}") (toExpr values)
    aoRefs := aoRefs ++ [Lean.mkConst name]
  let pairType := mkApp2 (Lean.mkConst ``Prod [.zero,.zero]) (Lean.mkConst ``Int) (Lean.mkConst ``Int)
  discard <| declare `aoRows (← Meta.mkArrayLit (mkApp (Lean.mkConst ``Array [.zero]) pairType) aoRefs)

end LAlanine40K2025.BasinRefinement.TrueTubeCache
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
