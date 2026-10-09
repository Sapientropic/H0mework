import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValuesGauge
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceActualCandidateVertexValuesLorentz
import Lean.Elab.Term
set_option autoImplicit false
namespace LowEnergy.ActualCandidateBra
open Lean Meta Elab Term

private def sourceRowName (index : Nat) (proof : Bool) : Name :=
  let family := if index < 57 then "Gauge" else if index < 73 then "Coframe" else "Lorentz"
  let moduleName := Name.mkSimple ("SourceActualCandidateVertexValues"++family)
  let ns := Name.str (Name.str (Name.num (Name.str `_private moduleName.toString) 0)
    "LowEnergy") "ActualCandidateVertexValues"
  Name.str ns ("row_"++toString index++if proof then "_original" else "")

private def sourceRow (index : Nat) (proof : Bool) : TermElabM Expr := do
  unless 9 ≤ index && index < 97 do throwError "Not an original non-momentum source vertex"
  let name := sourceRowName index proof
  unless (← getEnv).contains name do throwError "The paid source row or its identity is missing: {name}"
  mkConstWithFreshMVarLevels name

/-- Transparent access to the paid short row, preserving its original constant. -/
elab "source_vertex_row%" index:num : term => sourceRow index.getNat false
/-- The paid rfl bridge from the actual global literal to that same row. -/
elab "source_vertex_row_original%" index:num : term => sourceRow index.getNat true
end LowEnergy.ActualCandidateBra
