import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Source.Types
import H0mework.Cognition.Empirical.Sha256
import Lean.Elab.Term
import Lean.Meta.AppBuilder
import Lean.ToExpr

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Source
open Lean Elab Term
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Closure.Empirical.Manifest
def packetSha256 : String := "92eb553a05176b151d65c627272989b4f49a1f8c33d98da51ebf7cd9a5f187cd"
private def sourceText : String := include_str "../../../../../../../../../../../../../evidence/second-edition/v2/original/Biomedical/runtime/calculations/lmna-hgadfn188-correction/source/program.json"
private def sourceHash : String := Sha256.hex sourceText
private def parsed : Except String Json := Json.parse sourceText
private def field {α : Type} [FromJson α] (value : Json) (key : String) : TermElabM α :=
  match value.getObjValAs? α key with | .ok x => pure x | .error e => throwError "LMNA {key}: {e}"
private def packet : TermElabM Json := do
  unless sourceHash == packetSha256 do throwError "LMNA packet bytes changed"
  match parsed with | .ok x => pure x | .error e => throwError "{e}"
private def baseExpr (c : Char) : TermElabM Expr := do
  let n ← match DNM1Splicing2026.Sequence.upperBase c with
    | 'A' => pure ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.adenine
    | 'C' => pure ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.cytosine
    | 'G' => pure ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.guanine
    | 'T' => pure ``ChemicalGenomeInformation.Interface.CanonicalNucleobase.thymine
    | _ => throwError "Invalid original base"
  pure (Lean.mkConst n)
private def basesExpr (s : String) : TermElabM Expr := do
  Meta.mkListLit (Lean.mkConst ``ChemicalGenomeInformation.Interface.CanonicalNucleobase) (← s.toList.mapM baseExpr)
elab "lmnaBases%" group:str key:str : term => do
  let v : Json ← field (← packet) group.getString
  basesExpr (← field v key.getString)
elab "lmnaProtein%" : term => do
  let v : Json ← field (← packet) "transcript"
  let s : String ← field v "protein"
  pure (toExpr (s.toList.map (String.singleton) ++ ["*"]))
elab "lmnaContext%" : term => do
  let v : Json ← field (← packet) "genomic"
  let dna : String ← field v "dna"
  Meta.mkAppM ``DNM1Splicing2026.SequenceContext.mk #[toExpr (← field v "start" : Nat),
    toExpr (← field v "end" : Nat),← basesExpr dna,toExpr dna]
elab "lmnaCode%" : term => do
  let code : Json ← field (← packet) "genetic_code"
  let mut rows : List Expr := []
  for a in ["T","C","A","G"] do
    for b in ["T","C","A","G"] do
      for c in ["T","C","A","G"] do
        let key := a++b++c
        rows := rows ++ [← Meta.mkAppM ``Prod.mk #[← basesExpr key,toExpr (← field code key : String)]]
  Meta.mkListLit (← Meta.mkAppM ``Prod #[Lean.mkConst ``Bases,Lean.mkConst ``String]) rows
elab "lmnaJson%" key:str : term => do
  let v : Json ← field (← packet) key.getString
  pure (toExpr v.compress)
elab "lmnaAssays%" : term => do
  let v : Json ← field (← packet) "assays"
  pure (toExpr v.compress)
def coding : Bases := lmnaBases% "transcript" "coding"
def protein : List String := lmnaProtein%
def rna : Bases := lmnaBases% "transcript" "rna"
def context : SequenceContext := lmnaContext%
def vector : Bases := lmnaBases% "vector" "dna"
def guide : Bases := lmnaBases% "vector" "guide"
def dnaForward : Bases := lmnaBases% "primers" "dna_forward"
def dnaReverse : Bases := lmnaBases% "primers" "dna_reverse"
def code : List (Bases × String) := lmnaCode%
def registration : String := lmnaJson% "registration"
def assays : String := lmnaAssays%
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LMNACorrection2021.Source
