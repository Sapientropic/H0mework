import H0mework.Versions.AB.Arithmetic.PrimeShadow.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Unified.Orbitals.Rows
import H0mework.Versions.AB.Chemistry.LAlanineBandCache.Reifier

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.UnifiedOrbitals.SourceReifier
open Lean Elab Term Command
open BasinRefinement SourceGaussianModel SourceFiniteData SourceSignedEvaluator SourceExponential
open Inertia.SourceParsing

def rational (value : Json) : TermElabM ℚ := do
  let pair ← WholeCellSource.sourceRational value
  return (pair.1 : ℚ) / (pair.2 : ℚ)

def originalTerms : TermElabM (Array (Array SourceGaussianModel.Term)) := do
  let hash := SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest.Sha256.hex
  unless hash SourceFiniteData.sourceText == "704198fc5fb94e27e32ff770d5b1c1e41918fb5aa1fc27a4d8035dba3f499451" do
    throwError "original AO source"
  let source ← field (← parse SourceFiniteData.sourceText) "gaussian_source"
  let centres ← (← decode (Array (Array Json)) (← field source "centres")).mapM (·.mapM rational)
  let rows ← decode (Array (Array Json)) (← field source "terms")
  unless centres.size == 13 && rows.size == 98 do throwError "original atom and AO census"
  rows.mapM fun row => row.mapM fun value => do
    let atom ← decode Nat (← field value "atom")
    let powers ← decode (Array Nat) (← field value "powers")
    unless atom < 13 && powers.size == 3 do throwError "original primitive coordinates"
    let weight ← rational (← field value "weight")
    let exponent ← rational (← field value "exponent")
    return ⟨weight,exponent,(fun a => (centres[atom]!)[a.val]!),(fun a => powers[a.val]!)⟩

structure Inputs where
  gammas : Array ℚ
  penalties : Array ℚ
  radial : Array (ℚ × ℚ)
  incidence : Array (Nat × Nat)

def inputs (rows : Array (Array SourceGaussianModel.Term)) : Inputs := Id.run do
  let mut groups : Array SourceGaussianModel.Term := #[]
  for row in rows do
    for term in row do
      unless groups.any (fun other => term.exponent == other.exponent &&
          (List.finRange 3).all (fun a => term.centre a == other.centre a)) do
        groups := groups.push term
  let mut out : Inputs := ⟨#[],#[],#[],#[]⟩
  let mut gammaIndex : Std.HashMap (Int × Nat) Nat := {}
  let mut penaltyIndex : Std.HashMap (Int × Nat) Nat := {}
  let mut radialSeen : Std.HashSet ((Int × Nat) × (Int × Nat)) := {}
  for first in groups do
    for second in groups do
      let gamma := pairExponent first second
      let penalty := pairPenalty first second
      let gk := (gamma.num,gamma.den)
      let ek := (penalty.num,penalty.den)
      unless radialSeen.contains (gk,ek) do
        let si := (gammaIndex[gk]?).getD out.gammas.size
        let ei := (penaltyIndex[ek]?).getD out.penalties.size
        if si == out.gammas.size then out := {out with gammas := out.gammas.push gamma}
        if ei == out.penalties.size then out := {out with penalties := out.penalties.push penalty}
        gammaIndex := gammaIndex.insert gk si
        penaltyIndex := penaltyIndex.insert ek ei
        radialSeen := radialSeen.insert (gk,ek)
        out := {out with radial := out.radial.push (gamma,penalty), incidence := out.incidence.push (si,ei)}
  return out

def declare (suffix : Name) (value : Expr) : TermElabM Name := do
  WholeCellSource.declareSource suffix value
  return (← getCurrNamespace) ++ suffix

def exactComputation (type : Expr) : TermElabM Expr := do
  let type ← Meta.whnf type
  if type.isAppOfArity ``Eq 3 then return ← Meta.mkEqRefl type.getAppArgs[2]!
  let decider ← Meta.synthInstance (mkApp (Lean.mkConst ``Decidable) type)
  return mkApp3 (Lean.mkConst ``of_decide_eq_true) type decider
    (← Meta.mkEqRefl (Lean.mkConst ``Bool.true))

def proveStructure (name : Name) (type : Expr) (constructor : Name) : TermElabM Unit := do
  let goal ← Meta.mkFreshExprMVar type
  let fields ← goal.mvarId!.apply (Lean.mkConst constructor)
  for field in fields do field.assign (← exactComputation (← field.getType))
  addDecl (.thmDecl {name,levelParams := [],type,value := ← instantiateMVars goal})

elab "generateOriginalMetricInputs" : command => liftTermElabM do
  let data := inputs (← originalTerms)
  unless data.gammas.size == 630 && data.radial.size == 3859 do throwError "original shared integral census"
  discard <| declare `gammas (toExpr data.gammas)
  discard <| declare `penalties (toExpr data.penalties)
  discard <| declare `radialInputs (toExpr data.radial)
  discard <| declare `radialIncidence (toExpr data.incidence)
  let firstType := mkApp (Lean.mkConst ``Fin) (mkNatLit 630)
  let secondType := mkApp (Lean.mkConst ``Fin) (mkNatLit 3654)
  let pairType := mkApp2 (Lean.mkConst ``Prod [.zero,.zero]) firstType secondType
  let mut bounded : List Expr := []
  for (i,j) in data.incidence do
    let hi ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit i) (mkNatLit 630))
    let hj ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit j) (mkNatLit 3654))
    let left := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 630) (mkNatLit i) hi
    let right := mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit 3654) (mkNatLit j) hj
    bounded := mkApp4 (Lean.mkConst ``Prod.mk [.zero,.zero]) firstType secondType left right :: bounded
  discard <| declare `radialIncidenceBounded (← Meta.mkArrayLit pairType bounded.reverse)
  logInfo m!"original radial inputs: {data.gammas.size} square roots, {data.penalties.size} exponentials, {data.radial.size} combined kernels"

end LAlanine40K2025.UnifiedOrbitals.SourceReifier
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
