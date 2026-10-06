import H0mework.Versions.AB.Chemistry.LAlanineBondReadout.RuntimeParent
import H0mework.Versions.AB.Chemistry.LAlanineReentry.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout

structure BondSearchReadout where
  heavyAtomCount : Nat
  heavyPairCount : Nat
  registeredSeedCount : Nat
  candidateCount : Nat
  admittedSeedCount : Nat
  notAdmittedSeedCount : Nat
  positiveBCPCount : Nat
  sameDensityEnergyNanohartree : Int
  electronCountMicro : Nat
  independentAtomElectronCountMicro : Nat
  maxGradientDerivativeErrorTrillion : Nat
  maxHessianDerivativeErrorTrillion : Nat
  deriving DecidableEq, Repr

namespace SourceReification

open Lean Elab Term Inertia.SourceParsing LAlanine40K2025.Interface

private def atomLabel (atom : Expr) : TermElabM String := do
  let atom ← Meta.whnf atom
  match atom.constName! with
  | .str _ label => pure (String.ofList (label.toList.map Char.toUpper))
  | _ => throwError "Invalid registered heavy-atom constructor"

def registeredAddress (ctor : Name) : TermElabM (Array String) := do
  let endpoints ← Meta.whnf (← Meta.mkAppM ``pairEndpoints #[mkConst ctor])
  let args := endpoints.getAppArgs
  unless args.size == 4 do throwError "Invalid registered pair endpoints"
  return #[← atomLabel args[2]!, ← atomLabel args[3]!]

def endpointStability (bcp : Json) (address : Array String) : TermElabM Bool := do
  let traces ← decode (Array Json) (← field bcp "endpoint_traces")
  if traces.size != 2 then return false
  for trace in traces do
    let endpoints ← decode (Array Json) (← field trace "endpoints")
    if endpoints.size != 2 then return false
    let mut labels : Array String := #[]
    for endpoint in endpoints do
      if (← decode String (← field endpoint "terminal")) != "nucleus" then return false
      labels := labels.push (← decode String (← field endpoint "label"))
    if labels.qsort (· < ·) != address then return false
  pure true

def pairExpr (row : Json) : TermElabM Expr := do
  let midpoint ← field row "midpoint"
  let count ← decode Nat (← field row "bcp_count")
  let bcps ← decode (Array Json) (← field row "bcps")
  unless count == bcps.size && count ≤ 1 do throwError "PairPhysicalReadout needs this occurrence's single-BCP fibre"
  let found := count == 1
  let mut tail : Array Expr := #[toExpr (0 : Nat), toExpr (0 : Int), toExpr (0 : Int),
    toExpr (0 : Int), toExpr (0 : Nat), toExpr false]
  if found then
    let bcp := bcps[0]!
    unless (← field row "bcp") == bcp do throwError "Single-BCP read differs from recorded fibre"
    tail := #[toExpr (← decode Nat (← field bcp "density_nano")),
      toExpr (← decode Int (← field bcp "laplacian_nano")),
      toExpr (← decode Int (← field (← field bcp "deformation_at_bcp") "density_delta_nano")),
      toExpr (← decode Int (← field (← field bcp "straight_line_deformation") "integral_density_delta_nano_angstrom")),
      toExpr (← decode Nat (← field bcp "perpendicular_distance_microangstrom")),
      toExpr (← endpointStability bcp (← decode (Array String) (← field row "address")))]
  Meta.mkAppM ``PairPhysicalReadout.mk
    (#[toExpr (← decode Nat (← field row "distance_microangstrom")), toExpr found,
      toExpr (← decode Nat (← field midpoint "gradient_norm_nano")),
      toExpr (← decode Int (← field (← field midpoint "deformation") "density_delta_nano"))] ++ tail)

def registeredReadExpr (output : Expr) (read : Json → TermElabM Expr) (rows : Array Json) : TermElabM Expr := do
  let ctors := (← getConstInfoInduct ``ASUHeavyPair).ctors
  unless rows.size == ctors.length do throwError "Registered pair census changed"
  let mut reads : Array Expr := #[]
  for ctor in ctors do
    let address ← registeredAddress ctor
    let matching ← rows.filterM fun row => return (← decode (Array String) (← field row "address")) == address
    unless matching.size == 1 do throwError "Missing or duplicated pair incidence: {address}"
    reads := reads.push (← read matching[0]!)
  Meta.withLocalDeclD `pair (mkConst ``ASUHeavyPair) fun pair => do
    let motive ← Meta.mkLambdaFVars #[pair] output
    let body ← Meta.mkAppOptM ``ASUHeavyPair.rec
      (#[some motive] ++ reads.map some ++ #[some pair])
    Meta.mkLambdaFVars #[pair] body

def pairReadoutExpr := registeredReadExpr (mkConst ``PairPhysicalReadout) pairExpr

def pairReceiptExpr := registeredReadExpr (mkConst ``String) (fun row => pure (toExpr row.compress))

def topologyExpr (addresses : Array (Array String)) : TermElabM Expr := do
  let ctors := (← getConstInfoInduct ``ASUHeavyPair).ctors
  let mut reads : Array Expr := #[]
  for ctor in ctors do
    reads := reads.push (toExpr (addresses.contains (← registeredAddress ctor)))
  Meta.withLocalDeclD `pair (mkConst ``ASUHeavyPair) fun pair => do
    let motive ← Meta.mkLambdaFVars #[pair] (mkConst ``Bool)
    let body ← Meta.mkAppOptM ``ASUHeavyPair.rec
      (#[some motive] ++ reads.map some ++ #[some pair])
    Meta.mkLambdaFVars #[pair] body

def calculationExpr (value : Json) : TermElabM Expr := do
  let policy ← field value "registered_search"
  let search ← field value "finite_search_disposition"
  let method ← field value "method"
  let derivative ← field value "derivative_check"
  let natField (source : Json) (key : String) : TermElabM Expr :=
    return toExpr (← decode Nat (← field source key))
  Meta.mkAppM ``BondSearchReadout.mk
    #[← natField policy "heavy_atom_count", ← natField policy "heavy_pair_count",
      ← natField policy "seed_count", ← natField search "candidate_count",
      ← natField search "admitted_seed_count", ← natField search "not_admitted_seed_count",
      ← natField value "positive_bcp_count",
      toExpr (← decode Int (← field method "same_density_energy_nanohartree")),
      ← natField method "electron_count_micro", ← natField method "independent_atom_electron_count_micro",
      ← natField derivative "max_gradient_error_trillion", ← natField derivative "max_hessian_error_trillion"]

end SourceReification
end LAlanine40K2025.BondReadout
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
