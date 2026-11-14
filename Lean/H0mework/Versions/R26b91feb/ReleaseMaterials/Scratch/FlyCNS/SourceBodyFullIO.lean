import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceBodyIO

/-! The installed full ContentSource determines its finite complete field
inventory. Its fixed autonomous macro operation executes 100 genuine micro
cycles or a preinstalled gate operation; every actual operation advances the
source-owned visit and is consumed by the same complete ledger compiler. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace BodyFullIO

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Admission PlasticAdmission Lean

def requiredNames : Vector String 52 := ⟨#[
  "neural.voltage", "neural.conductance", "neural.refractory", "neural.delay_nodes",
  "neural.delay_counts", "neural.cursor", "neural.tick", "neural.random_seed", "neural.installation_sha256",
  "neural.adaptation_uv", "neural.release_q", "neural.dopamine_rise_q", "neural.dopamine_decay_q", "neural.dopamine_fraction_q",
  "body.installation_sha256", "body.integration", "body.controller_phases", "body.controller_magnitudes",
  "body.controller_intrinsic_freqs", "body.controller_intrinsic_amps", "body.controller_retraction",
  "body.controller_stumbling", "body.controller_persistence", "body.controller_random_keys",
  "body.controller_random_meta", "body.motor_trace", "body.descending_trace", "body.feeding_trace",
  "body.world_values", "body.sugar_stock", "body.water_stock", "body.odor_gain", "body.peptide_concentrations",
  "body.tick", "body.physics_ticks", "body.controller_enabled", "body.feeding_enabled", "body.peptide_enabled",
  "body.steering_trace", "source.stimulus", "source.sensory_probabilities", "source.auxiliary_neurons", "source.auxiliary_uv",
  "source.plastic_eligibility_q", "source.plastic_dopamine_q", "source.plastic_labile_q", "source.plastic_stable_q",
  "source.plastic_delta_uv", "source.plastic_last_update_tick", "source.plastic_modulation_scratch_q",
  "source.plastic_rules", "diagnostics.plastic_changes"], by decide⟩

abbrev FieldLayout := BodyIO.FieldLayout
abbrev Word := BodyIO.Word
abbrev RawCodeFile := BodyIO.RawCodeFile
abbrev Words (count : Nat) := Vector Word count

structure Header where
  schema : String
  fields : Array FieldLayout
  instance_id : String
  occurrence_id : String
  installation_sha256 : String
  root_visit : Nat
  deriving FromJson

structure Material where
  private mk ::
  admitted : SourceWiringAdmission
  directory : System.FilePath
  primitive : RawCodeFile
  linkedCode : List RawCodeFile
  model : ByteArray
  programmeMetadata : ByteArray
  count : Nat
  count_eq : count = 52
  layout : Vector FieldLayout count
  addresses : Vector (Fin count) 52
  address_names : ∀ required, (layout.get (addresses.get required)).name = requiredNames.get required
  names_unique : ∀ left right : Fin count, (layout.get left).name = (layout.get right).name → left = right
  instanceId : String
  birthOccurrence : String
  installationId : String

def requiredWord (material : Material) (words : Words material.count) (required : Fin 52) : Word :=
  words.get (material.addresses.get required)

def wordTick (material : Material) (words : Words material.count) : Nat :=
  (requiredWord material words ⟨6, by decide⟩).vector.word 0
def bodyTick (material : Material) (words : Words material.count) : Nat :=
  (requiredWord material words ⟨33, by decide⟩).vector.word 0
def physicsTick (material : Material) (words : Words material.count) : Nat :=
  (requiredWord material words ⟨34, by decide⟩).vector.word 0

def ShapeAt (material : Material) (words : Words material.count) : Prop :=
  (∀ field : Fin material.count, if (material.layout.get field).varying then
      (words.get field).vector.count ≤ neuronCount
    else (words.get field).vector.count = (material.layout.get field).count) ∧
  (requiredWord material words ⟨6, by decide⟩).vector.count = 1 ∧
  (requiredWord material words ⟨33, by decide⟩).vector.count = 1 ∧
  (requiredWord material words ⟨34, by decide⟩).vector.count = 1 ∧
  (requiredWord material words ⟨39, by decide⟩).vector.count = (requiredWord material words ⟨40, by decide⟩).vector.count ∧
  (requiredWord material words ⟨41, by decide⟩).vector.count = (requiredWord material words ⟨42, by decide⟩).vector.count

instance (material : Material) (words : Words material.count) : Decidable (ShapeAt material words) := by
  unfold ShapeAt
  infer_instance

structure Current (material : Material) where
  private mk ::
  words : Words material.count
  shape : ShapeAt material words
  clock : wordTick material words = bodyTick material words
  backend : Vector ByteArray 4
  header : ByteArray
  visit : Nat

def Current.tick {material : Material} (current : Current material) : Nat := wordTick material current.words

def readCurrent (material : Material) (directory : System.FilePath) : IO (Current material) := do
  let words ← Vector.ofFnM fun field => do
    let bytes ← IO.FS.readBinFile (directory / (toString field.val ++ ".npy"))
    BodyIO.checkedResult (BodyIO.parseWord (material.layout.get field) bytes)
  let header ← IO.FS.readBinFile (directory / "words.json")
  let document : Header ← BodyIO.checkedJson (← BodyIO.readJson (directory / "words.json"))
  if document.schema != "flycns-owned-content-root/slowda-d2-v1" ∨
      document.instance_id != material.instanceId ∨ document.occurrence_id != material.birthOccurrence ∨
      document.installation_sha256 != material.installationId ∨ document.fields.size != material.count then
    throw (IO.userError "the complete current belongs to another installed content source")
  let backend ← Vector.ofFnM fun field => IO.FS.readBinFile (directory / BodyIO.backendNames.get field)
  if shape : ShapeAt material words then
    if clock : wordTick material words = bodyTick material words then
      return ⟨words, shape, clock, backend, header, document.root_visit⟩
    else throw (IO.userError "the actual neural and body clocks disagree")
  else throw (IO.userError "the installed complete inventory changed physical dimensions")

def writeCurrent (material : Material) (current : Current material) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for field in List.finRange material.count do
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

inductive Trial where
  | trainingH0 | trainingH1 | receiverSugar | receiverWater
  deriving DecidableEq, Repr

def Trial.name : Trial → String
  | .trainingH0 => "training-h0" | .trainingH1 => "training-h1"
  | .receiverSugar => "receiver-sugar" | .receiverWater => "receiver-water"

def sourceAddress {count : Nat} (layout : Vector FieldLayout count) (name : String) : IO (Fin count) := do
  match (List.finRange count).find? (fun field => (layout.get field).name == name) with
  | some field => return field
  | none => throw (IO.userError ("the native complete snapshot omits " ++ name))

/-- The complete raw admission pays the graph and original-row role inventory.
The fixed constructor captures the executed content programme before birth. -/
def installSource (admitted : SourceWiringAdmission) (trial : Trial) : IO Source := do
  let nonce ← IO.monoNanosNow
  let directory := System.FilePath.mk "Lean/scratch/FlyCNS/.cache" / ("body-full-source-" ++ toString nonce)
  if (← directory.pathExists) then throw (IO.userError "the complete source birth directory is not fresh")
  IO.FS.createDirAll directory
  let primitivePath := System.FilePath.mk "Lean/scratch/FlyCNS/body_full_primitive.py"
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
  if result.exitCode != 0 then throw (IO.userError ("the complete source birth failed: " ++ result.stderr))
  let installation ← BodyIO.readJson (directory / "installation.json")
  let header : Header ← BodyIO.checkedJson (← BodyIO.readJson (directory / "initial" / "words.json"))
  let count := header.fields.size
  if complete : count = 52 then
    let layout : Vector FieldLayout count := ⟨header.fields, rfl⟩
    let addresses ← Vector.ofFnM fun required => sourceAddress layout (requiredNames.get required)
    if named : ∀ required : Fin 52, (layout.get (addresses.get required)).name = requiredNames.get required then
      if unique : ∀ left right : Fin count, (layout.get left).name = (layout.get right).name → left = right then
        let refs : Array BodyIO.CapturedFile ← BodyIO.checkedResult (installation.getObjValAs? _ "files")
        let mut linkedCode : List RawCodeFile := []
        for file in refs do
          let path := directory / file.relative
          linkedCode := linkedCode ++ [⟨System.FilePath.mk file.path, path, ← IO.FS.readBinFile path⟩]
        for (relative, bytes) in BodyIO.graphFiles admitted do
          let path := directory / "raw" / relative
          linkedCode := linkedCode ++ [⟨path, path, bytes⟩]
        let material : Material := ⟨admitted, directory, ⟨primitivePath, captured, primitiveBytes⟩, linkedCode,
          ← IO.FS.readBinFile (directory / "body.mjb"), ← IO.FS.readBinFile (directory / "installation.json"),
          count, complete, layout, addresses, named, unique, header.instance_id, header.occurrence_id, header.installation_sha256⟩
        let initial ← readCurrent material (directory / "initial")
        if zero : initial.tick = 0 then
          if born : initial.visit = 0 then return ⟨material, initial, zero, born⟩
          else throw (IO.userError "the source already consumed an operational visit")
        else throw (IO.userError "the source already consumed a neural microtick")
      else throw (IO.userError "the complete snapshot aliases two physical coordinates")
    else throw (IO.userError "native role addresses do not name the complete state")
  else throw (IO.userError "the native source is not the actual 14+25+12+1 content carrier")

inductive Operation where
  | neural | damage | repair
  deriving DecidableEq, Repr

def operationAt (visit : Nat) : Operation :=
  if visit = 55 then .damage else if visit = 58 then .repair else .neural

def Operation.microTicks : Operation → Nat
  | .neural => 100 | .damage | .repair => 0

def Operation.name : Operation → String
  | .neural => "neural" | .damage => "damage" | .repair => "repair"

def SameWord (left right : Word) : Prop :=
  left.bytes = right.bytes ∧ left.vector.dataStart = right.vector.dataStart ∧
    left.vector.width = right.vector.width ∧ left.vector.count = right.vector.count

instance (left right : Word) : Decidable (SameWord left right) := by
  unfold SameWord
  infer_instance

def GateAt {material : Material} (current : Current material) (enabled : Bool) : Prop :=
  (requiredWord material current.words ⟨35, by decide⟩).vector.count = 1 ∧
  (requiredWord material current.words ⟨35, by decide⟩).vector.width = 1 ∧
  (requiredWord material current.words ⟨35, by decide⟩).vector.word 0 = if enabled then 1 else 0

instance {material : Material} (current : Current material) (enabled : Bool) : Decidable (GateAt current enabled) := by
  unfold GateAt
  infer_instance

def LocalPreservesAt {material : Material} (before after : Current material) : Prop :=
  (∀ field : Fin material.count, field ≠ material.addresses.get ⟨35, by decide⟩ →
    SameWord (after.words.get field) (before.words.get field)) ∧
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
  if (← IO.FS.readBinFile (source.material.directory / "body.mjb")) != source.material.model then
    throw (IO.userError "the installed complete physical source changed")
  if (← IO.FS.readBinFile (source.material.directory / "installation.json")) != source.material.programmeMetadata then
    throw (IO.userError "the prebirth complete source programme changed")
  let nonce ← IO.monoNanosNow
  let input := source.material.directory / ("current-" ++ toString nonce)
  let output := source.material.directory / ("generated-" ++ toString nonce)
  writeCurrent source.material current input
  if (← output.pathExists) then throw (IO.userError "a complete autonomous next was preinstalled")
  let result ← IO.Process.output {
    cmd := "Biomedical/Connectomics/.venv/bin/python"
    args := #[source.material.primitive.capturedPath.toString, "step", source.material.directory.toString,
      input.toString, output.toString] }
  if result.exitCode != 0 then throw (IO.userError ("the complete native update failed: " ++ result.stderr))
  let after ← readCurrent source.material output
  let header ← BodyIO.readJson (output / "words.json")
  let actualOperation : String ← BodyIO.checkedResult (header.getObjValAs? _ "operation")
  if actualOperation != (operationAt current.visit).name then
    throw (IO.userError "the current did not consume its preinstalled autonomous operation")
  if visit : after.visit = current.visit + 1 then
    if neural : after.tick = current.tick + (operationAt current.visit).microTicks then
      if physical : physicsTick source.material after.words = physicsTick source.material current.words +
          10 * (operationAt current.visit).microTicks then
        let learning ← if operationAt current.visit == .neural then
          IO.FS.readBinFile (output / "learning-trace.npz") else pure ByteArray.empty
        let physics ← if operationAt current.visit == .neural then
          IO.FS.readBinFile (output / "physics-trace.npz") else pure ByteArray.empty
        if state : OperationStateAt current after then
          return ⟨after, visit, neural, physical, ← IO.FS.readBinFile (output / "generated-events.npz"), learning, physics, state⟩
        else throw (IO.userError "the actual gate operation changed another installed coordinate or failed settlement")
      else throw (IO.userError "the autonomous operation omitted an actual physical microcycle")
    else throw (IO.userError "the autonomous operation omitted an actual neural microcycle")
  else throw (IO.userError "the autonomous operation did not generate its next registered visit")

inductive CycleAt (source : Source) (current : Current source.material)
  | ready
  | completed (reply : Reply source current)

def CycleAt.materialNext {source : Source} {current : Current source.material} :
    CycleAt source current → Current source.material
  | .ready => current
  | .completed reply => reply.after

abbrev Responsibility := Fin 6

def network (source : Source) : WorldRelationNetwork where
  Support := Current source.material
  Anchor := String
  Incidence := Nat
  Lineage := String
  Responsibility := Responsibility
  Claim := Responsibility
  anchorAt := fun _ => source.material.instanceId
  incidenceAt := Current.visit
  lineageAt := fun _ => source.material.instanceId
  OpenAt := fun _ _ => Unit
  openClaimAt := fun {_support} {responsibility} _ => responsibility
  HoldsAt := fun _ _ => Unit
  ObstructionAt := fun _ => PEmpty
  obstructionClaim := PEmpty.elim
  SemanticChangeAt := fun _ _ _ => PEmpty
  DispositionAt := fun current _ => CycleAt source current

def vocabulary (source : Source) : Vocabulary where
  Current := Current source.material
  Anchor := String
  Incidence := Nat
  Lineage := String
  anchorAt := fun _ => source.material.instanceId
  incidenceAt := Current.visit
  lineageAt := fun _ => source.material.instanceId
  NativeWriteAt := CycleAt source
  RelationWriteAt := fun _ => PEmpty
  ContinuedTransportAt := fun _ => PEmpty
  BorromeanRedirectAt := fun _ => PEmpty
  FaithfulTerminalAt := fun _ => PEmpty
  nativeTarget := CycleAt.materialNext
  relationTarget := PEmpty.elim
  continuedTarget := PEmpty.elim
  redirectTarget := PEmpty.elim

variable (source : Source)

def entry (current : Current source.material) (responsibility : Responsibility) :
    OpenResponsibilityAt (network source) current := ⟨responsibility, ()⟩

def inventory (current : Current source.material) :
    ConstructivePresentation Responsibility (OpenResponsibilityAt (network source) current) where
  forward := entry source current
  backward := Sigma.fst
  backward_forward := fun _ => rfl
  forward_backward := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl

inductive EventAt : Current source.material → Current source.material → Type
  | ready (current : Current source.material) : EventAt current current
  | completed (current : Current source.material) (reply : Reply source current) : EventAt current current

def eventCycle {current support : Current source.material} (event : EventAt source current support) :
    CycleAt source current := by
  cases event with
  | ready => exact .ready
  | completed reply => exact .completed reply

def eventLaw : SourceNativeEventAlgebra (network source) (vocabulary source) where
  EventAt := EventAt source
  compile := fun {_current} {_support} event => .nativeWrite (eventCycle source event)
  AffectedInventoryAt := fun _ => Responsibility
  affectedInventoryPresentation := fun {_current} {_support} _ => inventory source _
  anchorKey := id
  incidenceKey := id
  lineageKey := id
  anchor_commutes := fun _ => rfl
  incidence_commutes := fun event => by cases event <;> rfl
  lineage_commutes := fun _ => rfl

def nativeSource : SourceNativeSource (network source) (vocabulary source) where
  initial := source.initial
  law := eventLaw source

def readyOccurrence (current : Current source.material) :
    (nativeSource source).toRootSource.actual.OccurrenceAt current := ⟨current, .ready current⟩

def completedOccurrence (current : Current source.material) (reply : Reply source current) :
    (nativeSource source).toRootSource.actual.OccurrenceAt current := ⟨current, .completed current reply⟩

def target {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) : Current source.material :=
  (eventCycle source occurrence.2).materialNext

structure ExactRowAt {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current)
    {targetSupport : Current source.material}
    (oldEntry : OpenResponsibilityAt (network source) occurrence.1)
    (newEntry : OpenResponsibilityAt (network source) targetSupport) : Type where
  target_eq : targetSupport = target source occurrence
  responsibility_eq : oldEntry.1 = newEntry.1

def writeRowSource : LedgerWriteRowSourceAt (nativeSource source) (ExactRowAt source) where
  IncidenceOccurrenceAt := ExactRowAt source
  compileEvolution := fun {_current} {_occurrence} {_target} {_old} {_new} exact => by
    cases _occurrence with
    | mk support event =>
      cases event with
      | ready => exact .transferred .ready rfl exact.responsibility_eq (Nat.le_refl _)
      | completed reply => exact .transferred (.completed reply) rfl exact.responsibility_eq (Nat.le_refl _)
  compileExact := id

def completePatch {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) :
    FiniteGeneratedLedgerWritePatchAt (writeRowSource source) occurrence ⟨target source occurrence⟩ :=
  .complete
    { size := 6
      sourceEntryAt := entry source occurrence.1
      targetEntryAt := entry source (target source occurrence)
      rowAt := fun responsibility => (writeRowSource source).generate ⟨rfl, rfl⟩ }
    { destinationIndex := Sigma.fst
      originIndex := Sigma.fst
      destination_sound := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl
      origin_sound := by rintro ⟨responsibility, receipt⟩; cases receipt; rfl }

def ledgerCompiler : SourceNativeLedgerCompiler (nativeSource source) where
  IncidenceTransitionAt := fun {_current} _ (old : Nat) (new : Nat) => PLift (old ≤ new)
  ExactTransitionAt := ExactRowAt source
  exact_incidence := fun {_current} {_occurrence} {_target} {_old} {_new} exact => by
    refine ⟨?_⟩
    change _occurrence.1.visit ≤ _target.visit
    rw [exact.target_eq]
    cases _occurrence with
    | mk support event =>
      cases event with
      | ready => exact Nat.le_refl _
      | completed reply =>
        change _current.visit ≤ reply.after.visit
        rw [reply.next_visit]
        exact Nat.le_succ _
  exact_lineage := fun _ => rfl
  writeRowSource := writeRowSource source
  terminalRowSource := LedgerTerminalRowSourceAt.empty (nativeSource source)
  compile := fun {current} occurrence => by
    cases occurrence with
    | mk support event =>
      cases event with
      | ready =>
        exact .nativeWrite .ready rfl (readyOccurrence source current)
          (completePatch source (readyOccurrence source current)).toLedgerWriteEvolution
      | completed reply =>
        exact .nativeWrite (.completed reply) rfl (readyOccurrence source reply.after)
          (completePatch source (completedOccurrence source current reply)).toLedgerWriteEvolution
  compilePatch := fun {current} occurrence => by
    cases occurrence with
    | mk support event =>
      cases event with
      | ready => exact ⟨completePatch source (readyOccurrence source current), rfl⟩
      | completed reply => exact ⟨completePatch source (completedOccurrence source current reply), rfl⟩

/-- Exact native chart of actual IO words, already carrying full support. -/
def chart := (eventLaw source).toOccurrenceChart

structure GeneratedAt (current : Current source.material) where
  private mk ::
  reply : Reply source current

def GeneratedAt.occurrence {current : Current source.material} (generated : GeneratedAt source current) :=
  completedOccurrence source current generated.reply

def GeneratedAt.patch {current : Current source.material} (generated : GeneratedAt source current) :=
  completePatch source generated.occurrence

def GeneratedAt.ledger {current : Current source.material} (generated : GeneratedAt source current) :=
  (ledgerCompiler source).compile generated.occurrence

def GeneratedAt.next {current : Current source.material} (generated : GeneratedAt source current) :=
  generated.reply.after

/-- No callback is supplied at installation.  This root's only completed
event producer is the concrete preinstalled native invocation above. -/
def emitIO (current : Current source.material) : IO (GeneratedAt source current) := do
  let reply ← invoke source current
  return ⟨reply⟩

theorem actual_support {current : Current source.material} (generated : GeneratedAt source current) :
    generated.occurrence.1 = current := rfl

theorem actual_next_visit {current : Current source.material} (generated : GeneratedAt source current) :
    generated.next.visit = current.visit + 1 := generated.reply.next_visit

theorem actual_next_clock {current : Current source.material} (generated : GeneratedAt source current) :
    generated.next.tick = current.tick + (operationAt current.visit).microTicks := generated.reply.neural_clock

theorem actual_target_is_generated_next {current : Current source.material} (generated : GeneratedAt source current) :
    target source generated.occurrence = generated.next := rfl

theorem all_six_source_entries {current : Current source.material}
    (generated : GeneratedAt source current) (responsibility : Responsibility) :
    (inventory source generated.occurrence.1).forward responsibility = entry source current responsibility := rfl

def restructuringLaw : SourceNativeLedgerRestructuringLaw (nativeSource source) :=
  identityOnlyWorldLedgerRestructuringLaw (nativeSource source) source.material.instanceId (by
    intro _ _
    change Subsingleton Unit
    infer_instance)

def restructuringCertification {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) :
    SourceNativeLedgerRestructuringCertificationAt (restructuringLaw source)
      ((ledgerCompiler source).compile occurrence) := by
  cases occurrence with
  | mk support event =>
    cases event <;>
      apply ExactLedgerRestructuringCertificationAt.ofInjective <;>
      (rintro ⟨left, leftReceipt⟩ ⟨right, rightReceipt⟩ same
       cases leftReceipt
       cases rightReceipt
       have sameResponsibility := congrArg Sigma.fst same
       change left = right at sameResponsibility
       cases sameResponsibility
       rfl)

def restructuringSource : SourceNativeRestructuringLedgerSource (network source) (vocabulary source) where
  source := nativeSource source
  compiler :=
    { ledgerCompiler := ledgerCompiler source
      restructuringLaw := restructuringLaw source
      certifyRestructuring := restructuringCertification source }


inductive Face where
  | before | after | whole | neural | plastic | weights | body | world | inputs | microTrace | sourceMaterial
  deriving DecidableEq

def CompletedAt {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) : Type :=
  match eventCycle source occurrence.2 with
  | .ready => PEmpty
  | .completed _ => Unit

def WaitingAt {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) : Type :=
  match eventCycle source occurrence.2 with
  | .ready => Unit
  | .completed _ => PEmpty

def classifyCompletion {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current) :
    CompletedAt source occurrence ⊕ WaitingAt source occurrence := by
  cases occurrence with
  | mk support event =>
    cases event with
    | ready => exact .inr ()
    | completed reply => exact .inl ()

def afterAt {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current)
    (active : CompletedAt source occurrence) : Current source.material := by
  cases occurrence with
  | mk support event =>
    cases event with
    | ready => exact nomatch active
    | completed reply => exact reply.after

def bytesAt (current : Current source.material) (field : Fin source.material.count) : ByteArray :=
  (current.words.get field).bytes

def intervalBytes (current : Current source.material) (offset size : Nat)
    (bounded : offset + size ≤ 52) : Vector ByteArray size :=
  Vector.ofFn fun field => (requiredWord source.material current.words ⟨offset + field.val, by omega⟩).bytes


def signedWord (value : Nat) : Int :=
  if value < 2 ^ 63 then Int.ofNat value else Int.ofNat value - Int.ofNat (2 ^ 64)

def deltaAt (current : Current source.material) (site : Fin sourceSites) : Int :=
  signedWord ((requiredWord source.material current.words ⟨47, by decide⟩).vector.word site.val)

def originalWeight (current : Current source.material) (edge : Fin edgeCount) : Int :=
  let graph := source.material.admitted.base.graph.rawGraph
  let delta := match source.material.admitted.wiring.candidate.siteAt edge with
    | none => 0 | some site => deltaAt source current site
  graph.transmitterSign (graph.pre edge) * (275 * Int.ofNat (graph.contacts edge) + delta)

structure MicroTrace where
  events : ByteArray
  learning : ByteArray
  physics : ByteArray

def Payload (face : Face) : Type :=
  match face with
  | .before | .after => Current source.material
  | .whole => Vector ByteArray source.material.count
  | .neural => Vector ByteArray 14
  | .plastic => Vector ByteArray 8
  | .weights => Fin edgeCount → Int
  | .body => Vector ByteArray 25
  | .world => Vector ByteArray 6
  | .inputs => Vector ByteArray 4
  | .microTrace => MicroTrace
  | .sourceMaterial => Material

def readCompleted (face : Face) (current : Current source.material) (trace : MicroTrace) : Payload source face :=
  match face with
  | .before | .after => current
  | .whole => current.words.map BodyIO.Word.bytes
  | .neural => intervalBytes source current 0 14 (by decide)
  | .plastic => intervalBytes source current 43 8 (by decide)
  | .weights => originalWeight source current
  | .body => intervalBytes source current 14 25 (by decide)
  | .world => Vector.ofFn fun field =>
      let address : Fin 52 := match field.val with
        | 0 => ⟨28, by decide⟩ | 1 => ⟨29, by decide⟩ | 2 => ⟨30, by decide⟩
        | 3 => ⟨31, by decide⟩ | 4 => ⟨32, by decide⟩ | _ => ⟨37, by decide⟩
      (requiredWord source.material current.words address).bytes
  | .inputs => intervalBytes source current 39 4 (by decide)
  | .microTrace => trace
  | .sourceMaterial => source.material

def traceAt {current : Current source.material}
    (occurrence : (nativeSource source).toRootSource.actual.OccurrenceAt current)
    (active : CompletedAt source occurrence) : MicroTrace := by
  cases occurrence with
  | mk support event =>
    cases event with
    | ready => exact nomatch active
    | completed reply => exact ⟨reply.generatedEvents, reply.learningTrace, reply.physicsTrace⟩

def projectionLaw : SourceNativeProjectionLaw (restructuringSource source).toLedgerSource where
  Projection := Face
  ActiveAt := fun face {_} occurrence => match face with
    | .before | .sourceMaterial => Unit | _ => CompletedAt source occurrence
  InactiveAt := fun face {_} occurrence => match face with
    | .before | .sourceMaterial => PEmpty | _ => WaitingAt source occurrence
  classify := fun face {_} occurrence => by
    cases face <;> first | exact .inl () | exact classifyCompletion source occurrence
  PayloadAt := fun face {_} _ _ => Payload source face
  project := fun face {current} occurrence active => match face with
    | .before => current
    | .sourceMaterial => source.material
    | .after => readCompleted source .after (afterAt source occurrence active) (traceAt source occurrence active)
    | .whole => readCompleted source .whole (afterAt source occurrence active) (traceAt source occurrence active)
    | .neural => readCompleted source .neural (afterAt source occurrence active) (traceAt source occurrence active)
    | .plastic => readCompleted source .plastic (afterAt source occurrence active) (traceAt source occurrence active)
    | .weights => readCompleted source .weights (afterAt source occurrence active) (traceAt source occurrence active)
    | .body => readCompleted source .body (afterAt source occurrence active) (traceAt source occurrence active)
    | .world => readCompleted source .world (afterAt source occurrence active) (traceAt source occurrence active)
    | .inputs => readCompleted source .inputs (afterAt source occurrence active) (traceAt source occurrence active)
    | .microTrace => traceAt source occurrence active

def authoritySource : SourceNativeAuthoritySource (network source) (vocabulary source) where
  restructuringSource := restructuringSource source
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource source)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (network source)
  projectionLaw := projectionLaw source

structure IORoot where
  private mk ::
  fixedSource : Source

def installedIORoot : IORoot := ⟨source⟩
def IORoot.initial (root : IORoot) : Current root.fixedSource.material := root.fixedSource.initial
def IORoot.emit (root : IORoot) (current : Current root.fixedSource.material) :
    IO (GeneratedAt root.fixedSource current) := emitIO root.fixedSource current

def GeneratedAt.wordRead {current : Current source.material} (generated : GeneratedAt source current) (face : Face) :=
  (projectionLaw source).outcomeAt face generated.occurrence

theorem completed_whole_read {current : Current source.material} (generated : GeneratedAt source current) :
    GeneratedAt.wordRead source generated .whole = .inl ⟨(), generated.next.words.map BodyIO.Word.bytes⟩ := rfl

set_option linter.defProp false in
def actual_word_ledger_next {current : Current source.material} (generated : GeneratedAt source current) :=
  And.intro (actual_support source generated)
    (And.intro (actual_target_is_generated_next source generated)
      (And.intro (actual_next_visit source generated)
        (And.intro (actual_next_clock source generated) (completed_whole_read source generated))))

def installMaleCNSFullBodyIORoot (admitted : SourceWiringAdmission) (trial : Trial) : IO IORoot := do
  let source ← installSource admitted trial
  return installedIORoot source

end BodyFullIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
