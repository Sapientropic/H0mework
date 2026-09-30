import H0mework.Chemistry.LAlanineBandCache.Check
import H0mework.Chemistry.LAlanineBandCache.SaturationCell2

/-! Fixed call128 cache proposal from original coefficients and registered inputs.
The 36 already generated intervals are literal outputs; Check consumes their Root62 proof.
Other exponentials and every polynomial/AO coordinate are calculated from their own inputs. -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandCell2.CacheReification

open Lean Elab Term Command SourceGaussianModel SourceSignedEvaluator SourceExponential
open SourceRectangle SourceRectangleChecks SourceFiniteData Inertia.SourceParsing
open WholeBandCache WholeBandSaturation

def finExpr (value bound : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit bound))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit bound) (mkNatLit value) proof

/-- Read the source-declared group map; there is no independent selection table. -/
def saturatedGroups : TermElabM (Array Nat) := do
  (Array.range 36).mapM fun i => do
    let group := mkApp (Lean.mkConst ``groupAt) (← finExpr i 36)
    let value ← Meta.mkAppM ``Fin.val #[group]
    let some n ← Meta.getNatValue? (← Meta.whnf value) | throwError "source group numeral"
    unless n < 94 do throwError "source group range"
    pure n

/-- Only the original coefficient registration's member addresses are read. -/
def groupMembers : TermElabM (Array (Array (Nat × Nat))) := do
  let some (.defnInfo info) := (← getEnv).find? ``SourceRectangle.rawGroups |
    throwError "original coefficient groups missing"
  unless info.safety == .safe do throwError "unsafe coefficient registration"
  let some rows ← Meta.getArrayLit? info.value | throwError "literal coefficient groups"
  unless rows.size == 94 do throwError "original group census"
  rows.mapM fun row => do
    unless row.isAppOfArity ``SourceRectangle.GroupData.mk 4 do
      throwError "original group record"
    let some members ← Meta.getArrayLit? row.getAppArgs[3]! |
      throwError "literal group members"
    unless members.size > 0 do throwError "empty coefficient group"
    members.mapM fun member => do
      unless member.isAppOfArity ``Prod.mk 4 do throwError "coefficient address pair"
      let some basis ← Meta.getNatValue? member.getAppArgs[2]! | throwError "basis address"
      let some term ← Meta.getNatValue? member.getAppArgs[3]! | throwError "term address"
      return (basis, term)

private def rational (value : Json) : TermElabM ℚ := do
  let pair ← WholeCellSource.sourceRational value
  return (pair.1 : ℚ) / pair.2

private def integers (a : Pair) : Int × Int := (⌊scale*a.1⌋, ⌈scale*a.2⌉)
private def grid (a : Int × Int) : Pair := ((a.1 : ℚ)/scale, (a.2 : ℚ)/scale)
private def zeroTerm : SourceGaussianModel.Term := ⟨0, 0, fun _ => 0, fun _ => 0⟩
private def declare (suffix : Name) (value : Expr) : TermElabM Name := do
  WholeCellSource.declareSource suffix value
  return (← getCurrNamespace) ++ suffix

elab "generateRoot62Call128Cache" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash SourceFiniteData.sourceText ==
      "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" do
    throwError "original Gaussian coefficients changed"
  let gaussian ← parse SourceFiniteData.sourceText
  let source ← field gaussian "gaussian_source"
  let centres ← (← decode (Array (Array Json)) (← field source "centres")).mapM (·.mapM rational)
  let rawTerms ← decode (Array (Array Json)) (← field source "terms")
  unless centres.size == 13 && rawTerms.size == 98 do throwError "source atom/AO census"
  let terms ← rawTerms.mapM fun row => row.mapM fun value => do
    let atom ← decode Nat (← field value "atom")
    let powers ← decode (Array Nat) (← field value "powers")
    unless atom < 13 && powers.size == 3 do throwError "source term coordinates"
    let weight ← rational (← field value "weight")
    let exponent ← rational (← field value "exponent")
    return SourceGaussianModel.Term.mk weight exponent (fun axis => (centres[atom]!)[axis.val]!)
      (fun axis => powers[axis.val]!)
  let coordinates ← WholeBandSource.coordinateLiterals 128
  let box : Rectangle := fun axis => grid coordinates[axis.val]!
  let reductions ← WholeBandSource.reductionLiterals 128
  let members ← groupMembers
  let saturated ← saturatedGroups
  discard <| declare `rawBox (toExpr coordinates)
  discard <| declare `rawReductions (toExpr reductions)
  let mut computed : Array SourceGroupCache.RawCache := #[]
  let mut groupIndex := terms.map (fun row => Array.replicate row.size 94)
  let mut refs : List Expr := []
  for g in [:94] do
    for address in members[g]! do
      unless address.1 < 98 && address.2 < (terms[address.1]!).size do
        throwError "original coefficient address range"
      groupIndex := groupIndex.modify address.1 (fun row => row.set! address.2 g)
    let first := (members[g]!)[0]!
    let term := ((terms[first.1]!)[first.2]?).getD zeroTerm
    let relativeRows := (List.finRange 3).toArray.map (fun axis => integers (relative term box axis))
    let radial := radialPair term box
    let exp := if saturated.contains g then ((0 : ℚ), 1/scale)
      else exponential radial reductions[g]!.1 reductions[g]!.2
    let polynomial := (List.finRange 3).toArray.map fun axis =>
      (List.finRange 3).toArray.map fun power =>
        (List.finRange 3).toArray.map fun order =>
          integers (jetHorner term.exponent power.val order.val (relative term box axis))
    let cache : SourceGroupCache.RawCache := ⟨relativeRows, integers radial, integers exp, polynomial⟩
    computed := computed.push cache
    refs := refs ++ [Lean.mkConst (← declare (Name.mkSimple s!"groupRow{g}") (toExpr cache))]
  discard <| declare `groupRows (← Meta.mkArrayLit (Lean.mkConst ``SourceGroupCache.RawCache) refs)
  unless groupIndex.all (fun row => row.all (fun g => g < 94)) do
    throwError "complete original term/group registration"
  let jets ← decode (Array (Array Nat)) (← field (← field gaussian "generated_bounds") "multiindices")
  unless jets.size == 35 do throwError "source jet census"
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
    aoRefs := aoRefs ++ [Lean.mkConst (← declare (Name.mkSimple s!"aoRow{b}") (toExpr values))]
  let pairType := mkApp2 (Lean.mkConst ``Prod [.zero,.zero]) (Lean.mkConst ``Int) (Lean.mkConst ``Int)
  discard <| declare `aoRows (← Meta.mkArrayLit (mkApp (Lean.mkConst ``Array [.zero]) pairType) aoRefs)

end LAlanine40K2025.BasinRefinement.WholeBandCell2.CacheReification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
