import H0mework.Chemistry.LAlanineBondReadout.SourceParsing

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BondReadout.Source

open Lean Elab Term Command Inertia.SourceParsing

private def declareReadout (suffix : Name) (value : Expr) : TermElabM Unit := do
  let value ← instantiateMVars value
  let type ← Meta.inferType value
  let name := (← getCurrNamespace) ++ suffix
  addDecl (.defnDecl { name, levelParams := [], type, value, hints := .regular 0, safety := .safe })
  modifyEnv (addNoncomputable · name)

elab "generateBondReadouts" : command => liftTermElabM do
  let packet ← SourceParsing.verifiedPacket
  let calculation ← field packet "calculation"
  let rows ← decode (Array Json) (← field calculation "pair_rows")
  declareReadout `pairReadoutAt (← SourceReification.pairReadoutExpr rows)
  declareReadout `pairReceiptText (← SourceReification.pairReceiptExpr rows)
  declareReadout `calculation (← SourceReification.calculationExpr calculation)
  let comparisons ← field calculation "target_erased_hostiles"
  declareReadout `independentAtomTopologyAt (← SourceReification.topologyExpr
    (← decode (Array (Array String)) (← field comparisons "promolecule_positive_bcp_addresses")))
  let physical ← field packet "physical"
  declareReadout `physicalFrame (← frame (← field physical "frame"))
  declareReadout `physicalTime (← rationalExpr (← field physical "generated_target_time"))
  declareReadout `physicalElapsedTime (← rationalExpr (← field physical "physical_elapsed_time"))

set_option maxRecDepth 4096 in
generateBondReadouts

def sourcePacketText : String := SourceParsing.sourceText
noncomputable def physicalLedger := Runtime.bondParentLedger
noncomputable def fullState := Runtime.bondParentFullState
noncomputable def exactState := Runtime.bondParentExactState
noncomputable def history := Runtime.bondParentHistory

theorem physicalFrame_eq_parent : physicalFrame = Runtime.bondParentFrame := rfl
theorem physicalLedger_eq_parent : physicalLedger = Runtime.bondParentLedger := rfl
theorem fullState_eq_parent : fullState = Runtime.bondParentFullState := rfl
theorem history_eq_parent : history = Runtime.bondParentHistory := rfl
theorem packetText_eq_verifiedInput : sourcePacketText = SourceParsing.sourceText := rfl

end LAlanine40K2025.BondReadout.Source
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
