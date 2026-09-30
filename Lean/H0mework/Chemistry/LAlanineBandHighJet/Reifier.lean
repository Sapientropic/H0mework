import H0mework.Chemistry.LAlanineBandHighJet.ProgramRecognition
import H0mework.Chemistry.LAlanineBandHighJet.Density

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Reification
open Lean Elab Term Command SourceGaussianModel SourceSignedEvaluator SourceExponential
open SourceRectangle SourceRectangleChecks SourceFiniteData Inertia.SourceParsing
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.BasinRefinement.WholeBandGenerated.Calculation

private def rational (j : Json) : TermElabM ℚ := do
  let value ← WholeCellSource.sourceRational j
  pure ((value.1 : ℚ)/value.2)
private def gridPair (a : Int × Int) : Pair := ((a.1 : ℚ)/scale,(a.2 : ℚ)/scale)
private def zeroTerm : SourceGaussianModel.Term := ⟨0,0,fun _ => 0,fun _ => 0⟩
private def declare (name : Name) (value : Expr) : TermElabM Name := do
  WholeCellSource.declareSource name value
  pure ((← getCurrNamespace) ++ name)
private def reduction (value : ℚ) : Nat := (Int.natAbs (⌊scale*|value|⌋)).log2+2-160
private def fin3 (n : Nat) : Fin 3 := ⟨n%3,Nat.mod_lt _ (by decide)⟩
private def fin5 (n : Nat) : Fin 5 := ⟨n%5,Nat.mod_lt _ (by decide)⟩

/-- Only original source inputs determine the tile, evaluation order and Gaussian material. -/
elab "generateHighJetCache " tile:num mode:num : command => liftTermElabM do
  let t := tile.getNat
  let phase := mode.getNat
  unless t < 64 && phase < 2 do throwError "fixed tile/scope census"
  let n := if phase == 0 then 20 else 35
  let ids := (Array.range 32).map fun i =>
    64*(8*(t/16)+i/4)+32*((t/8)%2)+2*(2*(t%8)+(i/2)%2)+i%2
  let boxes ← ids.mapM WholeBandSource.coordinateLiterals
  let hull := boxes.foldl (fun acc row => (Array.range 3).map fun a =>
    (min (acc[a]!).1 (row[a]!).1,max (acc[a]!).2 (row[a]!).2)) boxes[0]!
  let center := hull.map fun p => (p.1+p.2)/2
  let coordinates := if phase == 0 then center.map (fun c => (c,c)) else hull
  let box : Rectangle := fun a => gridPair coordinates[a.val]!
  discard <| declare `rawTile (toExpr t)
  discard <| declare `rawScope (toExpr phase)
  discard <| declare `rawJetCount (toExpr n)
  discard <| declare `rawBox (toExpr coordinates)
  discard <| declare `rawHull (toExpr hull)
  discard <| declare `rawCenter (toExpr center)
  let gaussian ← parse SourceFiniteData.sourceText
  let source ← field gaussian "gaussian_source"
  let centres ← (← decode (Array (Array Json)) (← field source "centres")).mapM (·.mapM rational)
  let rawTerms ← decode (Array (Array Json)) (← field source "terms")
  unless centres.size == 13 && rawTerms.size == 98 do throwError "original atom/AO census"
  let terms ← rawTerms.mapM fun row => row.mapM fun term => do
    let atom ← decode Nat (← field term "atom")
    let powers ← decode (Array Nat) (← field term "powers")
    unless atom < 13 && powers.size == 3 && powers.all (· < 3) do throwError "source Gaussian term"
    let weight ← rational (← field term "weight")
    let exponent ← rational (← field term "exponent")
    pure (SourceGaussianModel.Term.mk weight exponent (fun a => (centres[atom]!)[a.val]!)
      (fun a => powers[a.val]!))
  let members ← CacheReification.groupMembers
  let mut groupIndex := terms.map fun row => Array.replicate row.size 94
  let mut caches : Array SourceGroupCache.RawCache := #[]
  let mut reductions : Array (Nat × Nat) := #[]
  let mut saturation : Array Bool := #[]
  let mut refs : List Expr := []
  for g in [:94] do
    for (b,k) in members[g]! do groupIndex := groupIndex.modify b (fun row => row.set! k g)
    let address := (members[g]!)[0]!
    let term := ((terms[address.1]!)[address.2]?).getD zeroTerm
    let relativeRows := (List.finRange 3).toArray.map fun a => encode (relative term box a)
    let radial := radialPair term box
    let r := (reduction radial.1,reduction radial.2)
    let saturated := decide (
      (|reducedArgument radial.1 r.1| ≤ 1/2 ∧ |reducedArgument radial.2 r.2| ≤ 1/2) ∧
      ((r.1=8 ∧ reducedArgument radial.1 r.1 ≤ -7/16) ∨ (9≤r.1 ∧ reducedArgument radial.1 r.1 ≤ -7/32)) ∧
      ((r.2=8 ∧ reducedArgument radial.2 r.2 ≤ -7/16) ∨ (9≤r.2 ∧ reducedArgument radial.2 r.2 ≤ -7/32)))
    let exp := if saturated then (0,1/scale) else exponential radial r.1 r.2
    let polynomial := (List.finRange 3).toArray.map fun a =>
      (List.finRange 3).toArray.map fun p =>
        (List.finRange 5).toArray.map fun d => encode (jetHorner term.exponent p.val d.val (relative term box a))
    let cache : SourceGroupCache.RawCache := ⟨relativeRows,encode radial,encode exp,polynomial⟩
    caches := caches.push cache
    reductions := reductions.push r
    saturation := saturation.push saturated
    refs := refs ++ [Lean.mkConst (← declare (Name.mkSimple s!"groupRow{g}") (toExpr cache))]
  discard <| declare `groupRows (← Meta.mkArrayLit (Lean.mkConst ``SourceGroupCache.RawCache) refs)
  discard <| declare `rawReductions (toExpr reductions)
  discard <| declare `rawSaturation (toExpr saturation)
  let jets ← decode (Array (Array Nat)) (← field (← field gaussian "generated_bounds") "multiindices")
  unless jets.size == 35 && groupIndex.all (fun row => row.all (· < 94)) do throwError "complete source program"
  let mut aoRefs : List Expr := []
  for b in [:98] do
    let row := terms[b]!
    let codes := (Array.range row.size).toList.map fun k =>
      let term := (row[k]?).getD zeroTerm
      let g := (groupIndex[b]!)[k]!
      (TermCode.mk (encode (point term.weight)) ⟨g%94,Nat.mod_lt _ (by decide)⟩
        (fin3 (term.powers 0),fin3 (term.powers 1),fin3 (term.powers 2)))
    let values := (Array.range n).map fun j =>
      evalProgram codes (fun g => (caches[g.val]!).exponential)
        (fun g a p d => ((((caches[g.val]!).polynomial[a.val]!)[p.val]!)[d.val]!))
        (fun a => fin5 ((jets[j]!)[a.val]!))
    aoRefs := aoRefs ++ [Lean.mkConst (← declare (Name.mkSimple s!"aoRow{b}") (toExpr values))]
  let pairType := mkApp2 (Lean.mkConst ``Prod [.zero,.zero]) (Lean.mkConst ``Int) (Lean.mkConst ``Int)
  discard <| declare `aoRows (← Meta.mkArrayLit (mkApp (Lean.mkConst ``Array [.zero]) pairType) aoRefs)

end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet.Reification
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
