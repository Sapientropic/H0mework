import H0mework.Versions.R9c73a630.Chemistry.LAlanineBandFlowReplay.Model

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.BasinRefinement.WholeBandReplay

open Lean Elab Term Command WholeBandSource SourceRectangle SourceSignedEvaluator IntervalParameterMap

def rectangleRead (values : Array (Int × Int)) : Rectangle := fun axis =>
  integerInterval values[axis.val]!

def fieldRead (values : Array (Int × Int)) : FieldBox :=
  ⟨fun axis => integerInterval values[(WholeCellReplay.gradientIndex axis).val]!,
    fun axis direction => integerInterval values[(WholeCellReplay.hessianIndex axis direction).val]!⟩

private def literal (name : Name) : TermElabM Expr := do
  let some (.defnInfo info) := (← getEnv).find? name | throwError "registered source literal missing"
  unless info.safety == .safe do throwError "safe source required"
  return info.value

private def arrayLiteral (name : Name) (count : Nat) : TermElabM (Array Expr) := do
  let some values ← Meta.getArrayLit? (← literal name) | throwError "native source array required"
  unless values.size == count do throwError "complete source census"
  return values

def sourceInputLiteral (index : Nat) : TermElabM Expr := do
  unless index < 1024 do throwError "source row range"
  let coordinate := fun name count k => do
    pure (mkApp (Lean.mkConst ``rectangleRead) (← arrayLiteral name count)[k]!)
  let initial ← coordinate ``rawinitialBoxes 1024 index
  let tube ← coordinate ``rawtubeBoxes 1024 index
  let endpoint ← coordinate ``rawendpointBoxes 1024 index
  let initialCall ← coordinate ``rawCallBoxes 2048 (2*index)
  let tubeCall ← coordinate ``rawCallBoxes 2048 (2*index+1)
  let reports ← arrayLiteral ``rawCallDensity 2048
  let firstField := mkApp (Lean.mkConst ``fieldRead) reports[2*index]!
  let tubeField := mkApp (Lean.mkConst ``fieldRead) reports[2*index+1]!
  let direction ← Meta.mkAppOptM ``Int.cast #[some (Lean.mkConst ``Rat), none,
    some ((← arrayLiteral ``rawSigns 2)[index%32/16]!)]
  let rational := fun value => mkApp (Lean.mkConst ``Inertia.SourceParsing.rationalRead) value
  let step := rational (← literal ``rawStep)
  let start := rational ((← arrayLiteral ``rawStarts 1024)[index]!)
  let stop := rational ((← arrayLiteral ``rawStops 1024)[index]!)
  return mkAppN (Lean.mkConst ``Inputs.mk)
    #[initial,tube,endpoint,initialCall,tubeCall,firstField,tubeField,direction,step,start,stop]

def finLiteral (value size : Nat) : TermElabM Expr := do
  let proof ← Meta.mkDecideProof (← Meta.mkLT (mkNatLit value) (mkNatLit size))
  return mkApp3 (Lean.mkConst ``Fin.mk) (mkNatLit size) (mkNatLit value) proof

def progress (message : String) : TermElabM Unit := liftM (m := IO) do
  let output ← IO.getStdout
  output.putStrLn message
  output.flush

def emit (text : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command text with
  | .error message => throwError "{message}"
  | .ok command => elabCommand command

/-- Each slice is checked against the original safe source by kernel definitional equality. -/
elab "generateReplayRows " start:num stop:num : command => do
  let first := start.getNat
  let last := stop.getNat
  unless first ≤ last && last ≤ 1024 do throwError "registered row range"
  for r in [first:last] do
    liftTermElabM do
      progress s!"source row {r}: literal join"
      WholeCellSource.declareSource (Name.mkSimple s!"input{r}") (← sourceInputLiteral r)
    emit s!"theorem input{r}_source : input{r} = rowInput {r/32} {r%32/16} {r%16} := rfl"

end LAlanine40K2025.BasinRefinement.WholeBandReplay
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
