import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceBodyFullIO

/-! A separate prebirth spatial APL / gamma-terminal source. The original
52-word born root and its guarded programme remain unchanged. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace ContentFullIO

open Admission PlasticAdmission Lean

def extraNames : Vector String 7 := ⟨#[
  "neural.apl_voltage_uv", "neural.apl_conductance_uv", "neural.apl_dopamine_rise_q",
  "neural.apl_dopamine_decay_q", "neural.apl_dopamine_fraction_q",
  "neural.kc_muscarinic_rise_q", "neural.kc_muscarinic_activation_q"], by decide⟩
def requiredNames : Vector String 59 := BodyFullIO.requiredNames ++ extraNames
def schema : String := "flycns-owned-content-root/spatial-gamma-v1"

abbrev Word := BodyIO.Word
abbrev Words := Vector Word 59

structure Material where
  private mk ::
  admitted : SourceWiringAdmission
  directory : System.FilePath
  primitive : BodyIO.RawCodeFile
  linkedCode : List BodyIO.RawCodeFile
  model : ByteArray
  programmeMetadata : ByteArray
  layout : Vector BodyIO.FieldLayout 59
  addresses : Vector (Fin 59) 59
  address_names : ∀ required, (layout.get (addresses.get required)).name = requiredNames.get required
  names_unique : ∀ left right : Fin 59, (layout.get left).name = (layout.get right).name → left = right
  inventory_complete : ∀ field : Fin 59, ∃ required : Fin 59,
    (layout.get field).name = requiredNames.get required
  instanceId : String
  birthOccurrence : String
  installationId : String

def requiredWord (material : Material) (words : Words) (required : Fin 59) : Word :=
  words.get (material.addresses.get required)
def tickAt (material : Material) (words : Words) : Nat :=
  (requiredWord material words ⟨6, by decide⟩).vector.word 0
def bodyTick (material : Material) (words : Words) : Nat :=
  (requiredWord material words ⟨33, by decide⟩).vector.word 0
def physicsTick (material : Material) (words : Words) : Nat :=
  (requiredWord material words ⟨34, by decide⟩).vector.word 0

def ShapeAt (material : Material) (words : Words) : Prop :=
  (∀ field : Fin 59, if (material.layout.get field).varying then
      (words.get field).vector.count ≤ neuronCount
    else (words.get field).vector.count = (material.layout.get field).count) ∧
  (requiredWord material words ⟨6, by decide⟩).vector.count = 1 ∧
  (requiredWord material words ⟨33, by decide⟩).vector.count = 1 ∧
  (requiredWord material words ⟨34, by decide⟩).vector.count = 1 ∧
  (requiredWord material words ⟨39, by decide⟩).vector.count = (requiredWord material words ⟨40, by decide⟩).vector.count ∧
  (requiredWord material words ⟨41, by decide⟩).vector.count = (requiredWord material words ⟨42, by decide⟩).vector.count
instance (material : Material) (words : Words) : Decidable (ShapeAt material words) := by
  unfold ShapeAt
  infer_instance

structure Current (material : Material) where
  private mk ::
  words : Words
  shape : ShapeAt material words
  clock : tickAt material words = bodyTick material words
  backend : Vector ByteArray 4
  header : ByteArray
  visit : Nat
def Current.tick {material : Material} (current : Current material) : Nat := tickAt material current.words

def readCurrent (material : Material) (directory : System.FilePath) : IO (Current material) := do
  let words ← Vector.ofFnM fun field => do
    let bytes ← IO.FS.readBinFile (directory / (toString field.val ++ ".npy"))
    BodyIO.checkedResult (BodyIO.parseWord (material.layout.get field) bytes)
  let header ← IO.FS.readBinFile (directory / "words.json")
  let document : BodyFullIO.Header ← BodyIO.checkedJson (← BodyIO.readJson (directory / "words.json"))
  if document.schema != schema ∨ document.instance_id != material.instanceId ∨
      document.occurrence_id != material.birthOccurrence ∨ document.installation_sha256 != material.installationId ∨
      document.fields.size != 59 then throw (IO.userError "the Current belongs to another complete content source")
  let backend ← Vector.ofFnM fun field => IO.FS.readBinFile (directory / BodyIO.backendNames.get field)
  if shape : ShapeAt material words then
    if clock : tickAt material words = bodyTick material words then
      return ⟨words, shape, clock, backend, header, document.root_visit⟩
    else throw (IO.userError "the content neural and physical clocks disagree")
  else throw (IO.userError "the complete content inventory changes an installed dimension")

def writeCurrent (material : Material) (current : Current material) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for field in List.finRange 59 do
    IO.FS.writeBinFile (directory / (toString field.val ++ ".npy")) (current.words.get field).bytes
  for field in List.finRange 4 do
    IO.FS.writeBinFile (directory / BodyIO.backendNames.get field) (current.backend.get field)
  IO.FS.writeBinFile (directory / "words.json") current.header

structure Source where
  private mk ::
  material : Material
  initial : Current material
  initial_tick : initial.tick = 0
  initial_visit : initial.visit = 0

def installSource (admitted : SourceWiringAdmission) (trial : BodyFullIO.Trial) : IO Source := do
  let nonce ← IO.monoNanosNow
  let directory := System.FilePath.mk "Lean/scratch/FlyCNS/.cache" / ("content-full-source-" ++ toString nonce)
  if (← directory.pathExists) then throw (IO.userError "the complete content birth is not fresh")
  IO.FS.createDirAll directory
  let primitivePath := System.FilePath.mk "Lean/scratch/FlyCNS/content_full_primitive.py"
  let primitiveBytes ← IO.FS.readBinFile primitivePath
  let captured := directory / "primitive.py"
  IO.FS.writeBinFile captured primitiveBytes
  for (relative, bytes) in BodyIO.graphFiles admitted do
    let path := directory / "raw" / relative
    IO.FS.createDirAll (path.parent.getD directory)
    IO.FS.writeBinFile path bytes
  let result ← IO.Process.output {
    cmd := "Biomedical/Connectomics/.venv/bin/python"
    args := #[captured.toString, "prepare", directory.toString, trial.name] }
  if result.exitCode != 0 then throw (IO.userError ("the complete content birth failed: " ++ result.stderr))
  let installation ← BodyIO.readJson (directory / "installation.json")
  let header : BodyFullIO.Header ← BodyIO.checkedJson (← BodyIO.readJson (directory / "initial" / "words.json"))
  if complete : header.fields.size = 59 then
    let layout : Vector BodyIO.FieldLayout 59 := ⟨header.fields, complete⟩
    let addresses ← Vector.ofFnM fun required => BodyFullIO.sourceAddress layout (requiredNames.get required)
    if named : ∀ required : Fin 59, (layout.get (addresses.get required)).name = requiredNames.get required then
      if unique : ∀ left right : Fin 59, (layout.get left).name = (layout.get right).name → left = right then
        if exhaustive : ∀ field : Fin 59, ∃ required : Fin 59,
            (layout.get field).name = requiredNames.get required then
          let refs : Array BodyIO.CapturedFile ← BodyIO.checkedResult (installation.getObjValAs? _ "files")
          let mut linkedCode : List BodyIO.RawCodeFile := []
          for file in refs do
            let path := directory / file.relative
            linkedCode := linkedCode ++ [⟨System.FilePath.mk file.path, path, ← IO.FS.readBinFile path⟩]
          for (relative, bytes) in BodyIO.graphFiles admitted do
            let path := directory / "raw" / relative
            linkedCode := linkedCode ++ [⟨path, path, bytes⟩]
          let material : Material := ⟨admitted, directory, ⟨primitivePath, captured, primitiveBytes⟩, linkedCode,
            ← IO.FS.readBinFile (directory / "body.mjb"), ← IO.FS.readBinFile (directory / "installation.json"),
            layout, addresses, named, unique, exhaustive, header.instance_id, header.occurrence_id, header.installation_sha256⟩
          let initial ← readCurrent material (directory / "initial")
          if zero : initial.tick = 0 then
            if born : initial.visit = 0 then return ⟨material, initial, zero, born⟩
            else throw (IO.userError "the complete content source consumed an operation before admission")
          else throw (IO.userError "the complete content source consumed a microtick before admission")
        else throw (IO.userError "the content backend includes an unregistered coordinate")
      else throw (IO.userError "the content source aliases two physical coordinates")
    else throw (IO.userError "the content source omits a required original state")
  else throw (IO.userError "the actual source is not the complete 21+25+12+1 carrier")

abbrev operationAt := BodyFullIO.operationAt

def GateAt {material : Material} (current : Current material) (enabled : Bool) : Prop :=
  (requiredWord material current.words ⟨35, by decide⟩).vector.count = 1 ∧
  (requiredWord material current.words ⟨35, by decide⟩).vector.width = 1 ∧
  (requiredWord material current.words ⟨35, by decide⟩).vector.word 0 = if enabled then 1 else 0
instance {material : Material} (current : Current material) (enabled : Bool) : Decidable (GateAt current enabled) := by
  unfold GateAt
  infer_instance
def LocalPreservesAt {material : Material} (before after : Current material) : Prop :=
  (∀ field : Fin 59, field ≠ material.addresses.get ⟨35, by decide⟩ →
    BodyFullIO.SameWord (after.words.get field) (before.words.get field)) ∧
  (∀ field : Fin 4, field.val ≠ 1 → after.backend.get field = before.backend.get field)
instance {material : Material} (before after : Current material) : Decidable (LocalPreservesAt before after) := by
  unfold LocalPreservesAt
  infer_instance
def OperationStateAt {material : Material} (before after : Current material) : Prop :=
  match operationAt before.visit with
  | .neural => True
  | .damage => GateAt before true ∧ GateAt after false ∧ LocalPreservesAt before after
  | .repair => GateAt before false ∧ GateAt after true ∧ LocalPreservesAt before after
instance {material : Material} (before after : Current material) : Decidable (OperationStateAt before after) := by
  unfold OperationStateAt
  cases operationAt before.visit <;> infer_instance

structure Reply (source : Source) (current : Current source.material) where
  private mk ::
  after : Current source.material
  next_visit : after.visit = current.visit + 1
  neural_clock : after.tick = current.tick + (operationAt current.visit).microTicks
  physics_clock : physicsTick source.material after.words =
    physicsTick source.material current.words + 10 * (operationAt current.visit).microTicks
  generatedEvents : ByteArray
  learningTrace : ByteArray
  physicsTrace : ByteArray
  operation_state : OperationStateAt current after

def invoke (source : Source) (current : Current source.material) : IO (Reply source current) := do
  BodyIO.guardCode source.material.primitive
  for file in source.material.linkedCode do BodyIO.guardCode file
  if (← IO.FS.readBinFile (source.material.directory / "body.mjb")) != source.material.model ∨
      (← IO.FS.readBinFile (source.material.directory / "installation.json")) != source.material.programmeMetadata then
    throw (IO.userError "the installed content physical or programme source changed")
  let nonce ← IO.monoNanosNow
  let input := source.material.directory / ("current-" ++ toString nonce)
  let output := source.material.directory / ("generated-" ++ toString nonce)
  writeCurrent source.material current input
  if (← output.pathExists) then throw (IO.userError "the content next was preinstalled")
  let result ← IO.Process.output {
    cmd := "Biomedical/Connectomics/.venv/bin/python"
    args := #[source.material.primitive.capturedPath.toString, "step", source.material.directory.toString,
      input.toString, output.toString] }
  if result.exitCode != 0 then throw (IO.userError ("the content source update failed: " ++ result.stderr))
  let after ← readCurrent source.material output
  if visit : after.visit = current.visit + 1 then
    if neural : after.tick = current.tick + (operationAt current.visit).microTicks then
      if physical : physicsTick source.material after.words =
          physicsTick source.material current.words + 10 * (operationAt current.visit).microTicks then
        let learning ← if operationAt current.visit == .neural then IO.FS.readBinFile (output / "learning-trace.npz") else pure ByteArray.empty
        let physics ← if operationAt current.visit == .neural then IO.FS.readBinFile (output / "physics-trace.npz") else pure ByteArray.empty
        if state : OperationStateAt current after then
          return ⟨after, visit, neural, physical, ← IO.FS.readBinFile (output / "generated-events.npz"), learning, physics, state⟩
        else throw (IO.userError "the content gate operation changes another installed coordinate")
      else throw (IO.userError "the content operation omits an actual physical microcycle")
    else throw (IO.userError "the content operation omits an actual neural microcycle")
  else throw (IO.userError "the content operation omits its next registered visit")

end ContentFullIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
