import H0mework.Chemistry.LAlanineBandHighJet.Program
import H0mework.Chemistry.LAlanineBandCalculation.Reifier

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
open Lean Elab Term Command SourceFiniteData SourceSignedEvaluator
open Inertia.SourceParsing

elab "generateOriginalHighJetPrograms" : command => liftTermElabM do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash SourceFiniteData.sourceText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" do
    throwError "original Gaussian source"
  let data ← parse SourceFiniteData.sourceText
  let terms ← decode (Array (Array Json)) (← field (← field data "gaussian_source") "terms")
  let members ← CacheReification.groupMembers
  let mut membership := terms.map fun row => Array.replicate row.size 94
  for g in [:94] do
    for (b,t) in members[g]! do membership := membership.modify b (fun row => row.set! t g)
  unless terms.size == 98 && membership.all (fun row => row.all (· < 94)) do throwError "complete original AO code"
  let mut programs : List Expr := []
  for b in [:98] do
    let mut codes : List Expr := []
    let sourceRow := terms[b]!
    for t in [:sourceRow.size] do
      let termJson := sourceRow[t]!
      let weightJson ← field termJson "weight"
      let weightRational ← WholeCellSource.sourceRational weightJson
      let q : ℚ := (weightRational.1 : ℚ)/weightRational.2
      let weight := Calculation.encode (point q)
      let powers ← decode (Array Nat) (← field termJson "powers")
      unless powers.size == 3 && powers.all (· < 3) do throwError "source Gaussian powers"
      let p0 ← CacheReification.finExpr powers[0]! 3
      let p1 ← CacheReification.finExpr powers[1]! 3
      let p2 ← CacheReification.finExpr powers[2]! 3
      let tail ← Meta.mkAppM ``Prod.mk #[p1,p2]
      let powers ← Meta.mkAppM ``Prod.mk #[p0,tail]
      codes := codes ++ [← Meta.mkAppM ``TermCode.mk #[toExpr weight,
        ← CacheReification.finExpr (membership[b]!)[t]! 94,powers]]
    let name := Name.mkSimple s!"program{b}"
    WholeCellSource.declareSource name (← Meta.mkListLit (Lean.mkConst ``TermCode) codes)
    programs := programs ++ [Lean.mkConst ((← getCurrNamespace) ++ name)]
  WholeCellSource.declareSource `rawPrograms
    (← Meta.mkListLit (mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``TermCode)) programs)

generateOriginalHighJetPrograms

noncomputable def registeredProgram (b : Basis) : List TermCode := rawPrograms[b.val]!


end LAlanine40K2025.BasinRefinement.WholeBandGenerated.HighJet
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
