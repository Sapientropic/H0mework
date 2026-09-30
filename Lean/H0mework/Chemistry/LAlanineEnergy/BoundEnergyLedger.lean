import Lean.Elab.Term
import Lean.Meta.AppBuilder
import Lean.ToExpr
import Lean.Data.Json
import H0mework.Cognition.Empirical.Sha256
import H0mework.Chemistry.LAlanineEnergy.NativeEnergyLedger
import H0mework.Chemistry.LAlanineSource.BoundDiffraction

/-! # Whole-row binding of the same-SCF molecular energy occurrence -/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Energy.Source

open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Energy.Interface
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest

def sourceArtifactSha256 : String :=
  "b9b3973bc908f5a14d3deadbd687223c7cb03097b4936ac9e2f039aa70844d35"

private def sourceText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/energy/source/lalanine40k-same-computation-energy.json"

private def originalDensityText : String :=
  include_str "../../../../evidence/biomedical/calculations/lalanine40k-target-erased-quantum-bond-density/source/lalanine40k-source-only-quantum-bond-density.json"

private def field (value : Lean.Json) (key : String) : Lean.Elab.TermElabM Lean.Json :=
  match value.getObjVal? key with
  | .ok result => pure result
  | .error error => throwError "L-alanine energy source field {key}: {error}"

private def decode (α : Type) [Lean.FromJson α] (value : Lean.Json) : Lean.Elab.TermElabM α :=
  match Lean.fromJson? value with
  | .ok result => pure result
  | .error error => throwError "L-alanine energy source decoder: {error}"

private def parse (text : String) : Lean.Elab.TermElabM Lean.Json :=
  match Lean.Json.parse text with
  | .ok value => pure value
  | .error error => throwError "L-alanine energy source JSON: {error}"

private def sourceLedger : Lean.Elab.TermElabM Lean.Json := do
  unless Sha256.hex sourceText == sourceArtifactSha256 do
    throwError "L-alanine energy source artifact SHA-256 changed"
  let value ← parse sourceText
  unless Sha256.hex originalDensityText ==
      "7b042ae4fb66516165dcbc77fa66dd19e9fa6ea0160a4b99147f7862e2a8ba09" do
    throwError "Original L-alanine density occurrence changed"
  let density ← field value "density_projection"
  unless density == (← parse originalDensityText) do
    throwError "Energy and original density are not the same source projection"
  field value "energy_ledger"

private def blockedRows (rows : Array (Array Int)) :
    Lean.Elab.TermElabM Lean.Expr := do
  let blocks := (List.range ((rows.size + 63) / 64)).map fun index =>
    rows.extract (index * 64) ((index + 1) * 64)
  pure (Lean.toExpr blocks.toArray)

private def checkedRows (ledger : Lean.Json) (key : String)
    (rowCount width : Nat) : Lean.Elab.TermElabM (Array (Array Int)) := do
  let rows ← decode (Array (Array Int)) (← field ledger key)
  unless rows.size == rowCount && rows.all (fun row => row.size == width) do
    throwError "L-alanine energy row inventory {key} changed"
  pure rows

def integralAt (rows : Array ComponentIntegral) (component : EnergyComponent) :
    ComponentIntegral :=
  rows[match component with
    | .kinetic => 0
    | .electronNuclear => 1
    | .coulomb => 2
    | .b88Exchange => 3
    | .lypCorrelation => 4
    | .nuclearRepulsion => 5]!

/-- Pure row reification; authority belongs to the source that calls it. -/
def reifyMolecularEnergyLedger (ledger : Lean.Json) : Lean.Elab.TermElabM Lean.Expr := do
  let ao ← checkedRows ledger "ao_pair_rows" 4851 13
  let nuclear ← checkedRows ledger "nuclear_pair_rows" 78 5
  let atom ← checkedRows ledger "electron_nuclear_atom_rows" 13 3
  let xc ← checkedRows ledger "xc_grid_blocks" 229 5
  let mut offset := 0
  for left in [:98] do
    for right in [left:98] do
      let row := ao[offset]!
      unless row[0]! == (left : Int) && row[1]! == (right : Int) &&
          row[2]! == (if left == right then 1 else 2) do
        throwError "L-alanine exact AO-pair incidence changed"
      offset := offset + 1
  let components ← field ledger "components"
  let names := ["kinetic", "electron_nuclear", "coulomb",
    "b88_exchange", "lyp_correlation", "nuclear_repulsion"]
  let mut integralExpressions := #[]
  for name in names do
    let component ← field components name
    let integral ← decode Int (← field component "integral_nanohartree")
    let residual ← decode Int (← field component "quantization_residual_nanohartree")
    integralExpressions := integralExpressions.push (← Lean.Meta.mkAppM ``ComponentIntegral.mk
      #[Lean.toExpr integral, Lean.toExpr residual])
  let integrals ← Lean.Meta.mkArrayLit (Lean.mkConst ``ComponentIntegral)
    integralExpressions.toList
  let operator ← field ledger "operator_readout"
  let expectation ← decode Int (← field operator "effective_operator_expectation_nanohartree")
  let electronic ← decode Int (← field operator "electronic_energy_nanohartree")
  let correction ← decode Int (← field operator "double_counting_correction_nanohartree")
  let xcExpectation ← decode Int (← field operator "xc_potential_expectation_nanohartree")
  let xcEnergy ← decode Int (← field operator "xc_energy_nanohartree")
  let effective ← Lean.Meta.mkAppM ``EffectiveOperatorReadout.mk
    #[Lean.toExpr expectation, Lean.toExpr electronic, Lean.toExpr correction,
      Lean.toExpr xcExpectation, Lean.toExpr xcEnergy]
  let closure ← field ledger "closure"
  let reported ← decode Int (← field closure "reported_scf_nanohartree")
  let componentResidual ← decode Int (← field closure "component_rounding_residual_nanohartree")
  let scfResidual ← decode Int (← field closure "scf_recomputation_residual_nanohartree")
  let electrons ← field ledger "electron_balance"
  let overlap ← decode Int (← field electrons "overlap_trace_nano")
  let overlapResidual ← decode Int (← field electrons "overlap_rounding_residual_nano")
  let integralFunction ← Lean.Meta.mkAppM
    ``integralAt #[integrals]
  Lean.Meta.mkAppM ``MolecularEnergyLedger.mk
    #[← blockedRows ao, Lean.toExpr nuclear, Lean.toExpr xc, Lean.toExpr atom,
      integralFunction, effective, Lean.toExpr reported, Lean.toExpr overlap,
      Lean.toExpr overlapResidual, Lean.toExpr componentResidual, Lean.toExpr scfResidual]

elab "lalanineEnergyLedger%" : term => do
  reifyMolecularEnergyLedger (← sourceLedger)

set_option maxRecDepth 2048 in
noncomputable def energyLedger : MolecularEnergyLedger := lalanineEnergyLedger%

end LAlanine40K2025.Energy.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
