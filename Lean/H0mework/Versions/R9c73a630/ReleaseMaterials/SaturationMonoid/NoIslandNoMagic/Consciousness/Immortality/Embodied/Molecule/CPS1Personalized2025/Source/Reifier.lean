import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Source.Types
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Histology.Types
import H0mework.Cognition.Empirical.Sha256
import Lean.Elab.Term
import Lean.Meta.AppBuilder
import Lean.ToExpr

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Reifier
open Lean Elab Term
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
def packetSha256 : String := "fe6703ea162a756f295b10326aaf11d8737bdaebc11b303c0a0feb944f7012b5"
private def sourceText : String := include_str "../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/cps1-personalized-program/source/packet.json"
private def sourceHash : String := Sha256.hex sourceText
private def parsed : Except String Json := Json.parse sourceText
def field {α : Type} [FromJson α] (j : Json) (key : String) : TermElabM α :=
  match j.getObjValAs? α key with | .ok v => pure v | .error e => throwError "CPS1 source {key}: {e}"
def packet : TermElabM Json := do
  unless sourceHash == packetSha256 do throwError "Original CPS1 source packet changed"
  match parsed with | .ok j => pure j | .error e => throwError "{e}"
def group (name : String) : TermElabM Json := do field (← packet) name
def decimal (text : String) : TermElabM ℚ := do
  let (negative,word) := match text.toList with
    | '–' :: tail | '-' :: tail => (true,tail)
    | '+' :: tail => (false,tail)
    | tail => (false,tail)
  let some value := LMNACorrection2021.Histology.decimalChars? word | throwError "Original decimal {text}"
  pure (if negative then -value else value)
def decimals (j : Json) (key : String) : TermElabM (List ℚ) := do
  let values : List String ← field j key
  values.mapM decimal
def summaries (j : Json) (key : String) : TermElabM Expr := do
  let values : List (List String) ← field j key
  let result ← values.mapM fun row => do
    let values ← row.mapM decimal
    match values with
    | [m,l,u] => Meta.mkAppM ``Summary.mk #[toExpr m,toExpr l,toExpr u]
    | _ => throwError "Complete summary triple"
  Meta.mkListLit (Lean.mkConst ``Summary) result
def bases (text : String) : TermElabM Expr := do
  let values ← text.toList.mapM fun c => do
    match DNM1Splicing2026.Sequence.base? c with
    | some .adenine => pure (Lean.mkConst ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.adenine)
    | some .cytosine => pure (Lean.mkConst ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.cytosine)
    | some .guanine => pure (Lean.mkConst ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.guanine)
    | some .thymine => pure (Lean.mkConst ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.thymine)
    | none => throwError "Original DNA symbol"
  Meta.mkListLit (Lean.mkConst ``ChemicalGenomeInformation.Interface.CanonicalNucleobase) values
elab "cps1Raw%" key:str : term => do pure (toExpr (← field (← packet) key.getString : String).toList)
elab "cps1Text%" key:str : term => do pure (toExpr (← field (← packet) key.getString : String))
elab "cps1Json%" key:str : term => do
  let value : Json ← field (← packet) key.getString
  pure (toExpr value.compress)
elab "cps1GroupText%" groupName:str key:str : term => do pure (toExpr (← field (← group groupName.getString) key.getString : String))
elab "cps1Nat%" groupName:str key:str : term => do pure (toExpr (← field (← group groupName.getString) key.getString : Nat))
elab "cps1Bases%" groupName:str key:str : term => do bases (← field (← group groupName.getString) key.getString)
elab "cps1Protein%" : term => do
  pure (toExpr ((← field (← group "reference") "protein" : String).toList.map String.singleton))
elab "cps1Assays%" : term => do
  let rows : List Json ← field (← packet) "assay_rows"
  let values ← rows.mapM fun row => do
    let raw : List (Option String) ← field row "numeric_texts"
    let parsed ← raw.mapM fun text => match text with
      | none => pure none
      | some text => if text == "n.d." then pure none else return some (← decimal text)
    Meta.mkAppM ``AssayRow.mk #[toExpr (← field row "protospacer_pam" : String).toList,
      toExpr (← field row "columns" : List String),toExpr raw,toExpr parsed,toExpr (← field row "original_line" : String)]
  Meta.mkListLit (Lean.mkConst ``AssayRow) values
elab "cps1Clinical%" : term => do
  let j ← group "registration"
  Meta.mkAppM ``ClinicalRegistration.mk #[toExpr (← field j "patient_key" : String),
    toExpr (← field j "clinical_dose1_day" : Nat),toExpr (← decimal (← field j "clinical_dose1")),
    toExpr (← field j "clinical_dose2_interval_days" : Nat),toExpr (← decimal (← field j "clinical_dose2")),
    toExpr (← decimals j "first_taper"),toExpr (← decimals j "second_taper"),
    toExpr (← field j "weight_days" : List Nat),toExpr (← decimals j "weights_kg"),
    ← summaries j "ammonia_median_iqr",← summaries j "orotic_median_iqr",
    toExpr (← field j "clinical_dose_unit" : String),toExpr (← field j "scavenger_unit" : String),
    toExpr (← field j "ammonia_unit" : String),toExpr (← field j "orotic_unit" : String),
    toExpr (← field j "clinical_tissue" : String)]
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.CPS1Personalized2025.Reifier
