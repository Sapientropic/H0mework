import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourcePlasticAdmission

/-! A prospective source-owned IO emitter.  Its fixed primitive reconstructs
the registered current, executes NN/Q20/controller/MJB/world, and generates
the complete next word image.  The kernel pays word identity, dataflow and
whole-ledger accounting.  Foreign Python/Numba/MuJoCo execution is explicit;
no pure-process realization or ODE theorem is asserted here. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace BodyIO

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
open Admission PlasticAdmission Lean

def fieldNames : Vector String 46 := ⟨#[
  "neural.voltage", "neural.conductance", "neural.refractory", "neural.delay_nodes",
  "neural.delay_counts", "neural.cursor", "neural.tick", "neural.random_seed", "neural.installation_sha256",
  "body.installation_sha256", "body.integration", "body.controller_phases", "body.controller_magnitudes",
  "body.controller_intrinsic_freqs", "body.controller_intrinsic_amps", "body.controller_retraction",
  "body.controller_stumbling", "body.controller_persistence", "body.controller_random_keys",
  "body.controller_random_meta", "body.motor_trace", "body.descending_trace", "body.feeding_trace",
  "body.world_values", "body.sugar_stock", "body.water_stock", "body.odor_gain", "body.peptide_concentrations",
  "body.tick", "body.physics_ticks", "body.controller_enabled", "body.feeding_enabled", "body.peptide_enabled",
  "source.stimulus", "source.sensory_probabilities", "source.auxiliary_neurons", "source.auxiliary_uv",
  "source.plastic_eligibility_q", "source.plastic_dopamine_q", "source.plastic_labile_q", "source.plastic_stable_q",
  "source.plastic_delta_uv", "source.plastic_last_update_tick", "source.plastic_modulation_scratch_q",
  "source.plastic_rules", "diagnostics.plastic_changes"], by decide⟩

structure FieldLayout where
  name : String
  dtype : String
  width : Nat
  count : Nat
  varying : Bool
  deriving FromJson

structure WordHeader where
  schema : String
  fields : Array FieldLayout
  instance_id : String
  occurrence_id : String
  installation_sha256 : String
  deriving FromJson

structure CapturedFile where
  path : String
  relative : String
  deriving FromJson

structure RawCodeFile where
  activePath : System.FilePath
  capturedPath : System.FilePath
  bytes : ByteArray

structure Material where
  private mk ::
  admitted : SourceWiringAdmission
  directory : System.FilePath
  primitive : RawCodeFile
  linkedCode : List RawCodeFile
  model : ByteArray
  programmeMetadata : ByteArray
  layout : Vector FieldLayout 46
  layout_names : ∀ field, (layout.get field).name = fieldNames.get field
  instanceId : String
  birthOccurrence : String
  installationId : String

structure Word where
  private mk ::
  bytes : ByteArray
  vector : NpyVector bytes

def parseWord (layout : FieldLayout) (bytes : ByteArray) : Except String Word := do
  let vector ← parseNpyVector bytes layout.dtype layout.width
  return ⟨bytes, vector⟩

abbrev Words := Vector Word 46

def ShapeAt (material : Material) (words : Words) : Prop :=
  (∀ field : Fin 46, if (material.layout.get field).varying then
      (words.get field).vector.count ≤ neuronCount
    else (words.get field).vector.count = (material.layout.get field).count) ∧
  (words.get ⟨6, by decide⟩).vector.count = 1 ∧
  (words.get ⟨28, by decide⟩).vector.count = 1 ∧
  (words.get ⟨29, by decide⟩).vector.count = 1 ∧
  (words.get ⟨33, by decide⟩).vector.count = (words.get ⟨34, by decide⟩).vector.count ∧
  (words.get ⟨35, by decide⟩).vector.count = (words.get ⟨36, by decide⟩).vector.count

instance (material : Material) (words : Words) : Decidable (ShapeAt material words) := by
  unfold ShapeAt
  infer_instance

def wordTick (words : Words) : Nat := (words.get ⟨6, by decide⟩).vector.word 0
def bodyTick (words : Words) : Nat := (words.get ⟨28, by decide⟩).vector.word 0
def physicsTick (words : Words) : Nat := (words.get ⟨29, by decide⟩).vector.word 0

/-- Backend bytes are registered too: restart cannot hide state in NPZ/JSON
which is absent from the individual word faces. -/
structure Current (material : Material) where
  private mk ::
  words : Words
  shape : ShapeAt material words
  clock : wordTick words = bodyTick words
  backend : Vector ByteArray 4
  header : ByteArray

def Current.tick {material : Material} (current : Current material) : Nat := wordTick current.words

def backendNames : Vector String 4 := ⟨#["neural.npz", "body.npz", "source-state.npz", "source.json"], by decide⟩

def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok value => return value
  | .error reason => throw (IO.userError reason)

def checkedJson {α : Type} [FromJson α] (value : Json) : IO α :=
  match fromJson? value with
  | .ok result => pure result
  | .error reason => throw (IO.userError reason)

def checkedResult {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error reason => throw (IO.userError reason)

def readCurrent (material : Material) (directory : System.FilePath) : IO (Current material) := do
  let words ← Vector.ofFnM fun field => do
    let bytes ← IO.FS.readBinFile (directory / (toString field.val ++ ".npy"))
    match parseWord (material.layout.get field) bytes with
    | .ok word => pure word
    | .error reason => throw (IO.userError reason)
  let header ← IO.FS.readBinFile (directory / "words.json")
  let document : WordHeader ← checkedJson (← readJson (directory / "words.json"))
  if document.schema != "flycns-owned-body-root-primitive/legacy275-v1" ∨
      document.instance_id != material.instanceId ∨ document.occurrence_id != material.birthOccurrence ∨
      document.installation_sha256 != material.installationId then
    throw (IO.userError "word image belongs to another installed source")
  let backend ← Vector.ofFnM fun field => IO.FS.readBinFile (directory / backendNames.get field)
  if shape : ShapeAt material words then
    if clock : wordTick words = bodyTick words then return ⟨words, shape, clock, backend, header⟩
    else throw (IO.userError "neural and physical source currents disagree")
  else throw (IO.userError "complete word image dimensions changed")

structure Source where
  private mk ::
  material : Material
  initial : Current material
  initial_tick : initial.tick = 0

def guardCode (code : RawCodeFile) : IO Unit := do
  if (← IO.FS.readBinFile code.activePath) != code.bytes ∨
      (← IO.FS.readBinFile code.capturedPath) != code.bytes then
    throw (IO.userError "preinstalled primitive or controller code changed")

def runPrimitive (material : Material) (mode : String) (arguments : Array String) : IO Unit := do
  guardCode material.primitive
  for file in material.linkedCode do guardCode file
  if (← IO.FS.readBinFile (material.directory / "body.mjb")) != material.model then
    throw (IO.userError "the installed full raw physical model changed")
  if (← IO.FS.readBinFile (material.directory / "installation.json")) != material.programmeMetadata then
    throw (IO.userError "the installed source/material programme changed")
  let result ← IO.Process.output {
    cmd := "Biomedical/Connectomics/.venv/bin/python"
    args := #[material.primitive.capturedPath.toString, mode, material.directory.toString] ++ arguments }
  if result.exitCode != 0 then throw (IO.userError ("owned native primitive failed: " ++ result.stderr))

def writeCurrent (material : Material) (current : Current material) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for field in List.finRange 4 do
    IO.FS.writeBinFile (directory / backendNames.get field) (current.backend.get field)
  for field in List.finRange 46 do
    IO.FS.writeBinFile (directory / (toString field.val ++ ".npy")) (current.words.get field).bytes
  IO.FS.writeBinFile (directory / "words.json") current.header

/-- The private reply is minted only after the owned primitive executes. -/
structure Reply (source : Source) (current : Current source.material) where
  private mk ::
  after : Current source.material
  next_clock : after.tick = current.tick + 1
  physics_clock : physicsTick after.words = physicsTick current.words + 10
  generatedEvents : ByteArray

def invoke (source : Source) (current : Current source.material) : IO (Reply source current) := do
  let nonce ← IO.monoNanosNow
  let input := source.material.directory / ("current-" ++ toString nonce)
  let output := source.material.directory / ("generated-" ++ toString nonce)
  writeCurrent source.material current input
  if (← output.pathExists) then throw (IO.userError "a future material output was preinstalled")
  runPrimitive source.material "step" #[input.toString, output.toString]
  let after ← readCurrent source.material output
  if next : after.tick = current.tick + 1 then
    if physical : physicsTick after.words = physicsTick current.words + 10 then
      return ⟨after, next, physical, ← IO.FS.readBinFile (output / "generated-events.npz")⟩
    else throw (IO.userError "actual primitive omitted a physical substep")
  else throw (IO.userError "actual primitive omitted the neural source update")

def graphFiles (admitted : SourceWiringAdmission) : List (String × ByteArray) :=
  let graph := admitted.base.graph.vectors.original
  let wiring := admitted.wiring.candidate.vectors.original
  [("data/body-annotations-male-cns-v1.0-minconf-0.5.feather", admitted.base.annotations),
   ("data/body-neurotransmitters-male-cns-v1.0.feather", admitted.base.neurotransmitters),
   ("data/connectome-weights-male-cns-v1.0-minconf-0.5.feather", admitted.base.originalWeights),
   ("graph/manifest.json", admitted.graphManifest),
   ("graph/body_ids.npy", graph.bodyIds), ("graph/indptr.npy", graph.indptr),
   ("graph/indices.npy", graph.indices), ("graph/counts.npy", graph.counts),
   ("graph/sign.npy", graph.sign), ("graph/source_row.npy", graph.sourceRow),
   ("graph/mushroom-body/role_kc.npy", wiring.roleKC),
   ("graph/mushroom-body/role_dan.npy", wiring.roleDAN),
   ("graph/mushroom-body/role_mbon.npy", wiring.roleMBON),
   ("graph/mushroom-body/domain_neurons.npy", wiring.domains),
   ("graph/mushroom-body/site_edges.npy", wiring.siteEdges),
   ("graph/mushroom-body/site_domains.npy", wiring.siteDomains),
   ("graph/mushroom-body/dan_edges.npy", wiring.danEdges),
   ("graph/mushroom-body/dan_domains.npy", wiring.danDomains)]

def sourceParameters : String :=
  "{\"patches\":[{\"position_mm\":[1,0,0.5],\"radius_mm\":3,\"sugar\":1,\"water\":0.4}],\"odor_sources\":[{\"position_mm\":[-3,0,0.5],\"strength\":[1,0],\"sigma_mm\":3},{\"position_mm\":[3,0,0.5],\"strength\":[0,1],\"sigma_mm\":3}],\"energy\":0.5,\"hydration\":0.5}"

/-- Inputs are the already strong source-byte admission.  Body initialization
is executed before any neural tick and projection/ledger installation. -/
def installSource (admitted : SourceWiringAdmission) : IO Source := do
  let nonce ← IO.monoNanosNow
  let directory := System.FilePath.mk "Lean/scratch/FlyCNS/.cache" / ("body-source-" ++ toString nonce)
  if (← directory.pathExists) then throw (IO.userError "source installation directory is not fresh")
  IO.FS.createDirAll directory
  let primitivePath := System.FilePath.mk "Lean/scratch/FlyCNS/body_root_primitive.py"
  let primitiveBytes ← IO.FS.readBinFile primitivePath
  let capturedPrimitive := directory / "primitive.py"
  IO.FS.writeBinFile capturedPrimitive primitiveBytes
  IO.FS.writeFile (directory / "parameters.json") sourceParameters
  for (relative, bytes) in graphFiles admitted do
    let path := directory / "raw" / relative
    IO.FS.createDirAll (path.parent.getD directory)
    IO.FS.writeBinFile path bytes
  let result ← IO.Process.output {
    cmd := "Biomedical/Connectomics/.venv/bin/python"
    args := #[capturedPrimitive.toString, "prepare", directory.toString] }
  if result.exitCode != 0 then throw (IO.userError result.stderr)
  let installation ← readJson (directory / "installation.json")
  let header : WordHeader ← checkedJson (← readJson (directory / "initial" / "words.json"))
  if count : header.fields.size = 46 then
    let layout : Vector FieldLayout 46 := ⟨header.fields, count⟩
    if names : ∀ field : Fin 46, (layout.get field).name = fieldNames.get field then
      let refs : Array CapturedFile ← checkedResult (installation.getObjValAs? (Array CapturedFile) "files")
      let mut linkedCode : List RawCodeFile := []
      for file in refs do
        let capturedPath := directory / file.relative
        let bytes ← IO.FS.readBinFile capturedPath
        linkedCode := linkedCode ++ [⟨System.FilePath.mk file.path, capturedPath, bytes⟩]
      for (relative, bytes) in graphFiles admitted do
        let path := directory / "raw" / relative
        linkedCode := linkedCode ++ [⟨path, path, bytes⟩]
      let parametersPath := directory / "parameters.json"
      linkedCode := linkedCode ++ [⟨parametersPath, parametersPath, ← IO.FS.readBinFile parametersPath⟩]
      let material : Material := ⟨admitted, directory,
        ⟨primitivePath, capturedPrimitive, primitiveBytes⟩, linkedCode,
        ← IO.FS.readBinFile (directory / "body.mjb"),
        ← IO.FS.readBinFile (directory / "installation.json"), layout, names,
        header.instance_id, header.occurrence_id, header.installation_sha256⟩
      let initial ← readCurrent material (directory / "initial")
      if zero : initial.tick = 0 then return ⟨material, initial, zero⟩
      else throw (IO.userError "body source was installed after a neural update")
    else throw (IO.userError "body source omits a registered material coordinate")
  else throw (IO.userError "body source word catalogue differs")

/-! The ready event is the source's next invocation boundary, not a completed
physical tick.  The IO root emits a completed event only after `invoke`.
This makes the existing total ledger compiler usable without inventing a
pure foreign result. -/

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
  incidenceAt := Current.tick
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
  incidenceAt := Current.tick
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
    change _occurrence.1.tick ≤ _target.tick
    rw [exact.target_eq]
    cases _occurrence with
    | mk support event =>
      cases event with
      | ready => exact Nat.le_refl _
      | completed reply =>
        change _current.tick ≤ reply.after.tick
        rw [reply.next_clock]
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

theorem actual_next_clock {current : Current source.material} (generated : GeneratedAt source current) :
    generated.next.tick = current.tick + 1 := generated.reply.next_clock

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
  | before | after | neural | plastic | weights | body | world | inputs | sourceMaterial
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

def bytesAt (current : Current source.material) (field : Fin 46) : ByteArray :=
  (current.words.get field).bytes

def intervalBytes (current : Current source.material) (offset size : Nat)
    (bounded : offset + size ≤ 46) : Vector ByteArray size :=
  Vector.ofFn fun field => bytesAt source current ⟨offset + field.val, by omega⟩

def signedWord (value : Nat) : Int :=
  if value < 2 ^ 63 then Int.ofNat value else Int.ofNat value - Int.ofNat (2 ^ 64)

def deltaAt (current : Current source.material) (site : Fin sourceSites) : Int :=
  signedWord ((current.words.get ⟨41, by decide⟩).vector.word site.val)

def originalWeight (current : Current source.material) (edge : Fin edgeCount) : Int :=
  let graph := source.material.admitted.base.graph.rawGraph
  let delta := match source.material.admitted.wiring.candidate.siteAt edge with
    | none => 0
    | some site => deltaAt source current site
  graph.transmitterSign (graph.pre edge) * (275 * Int.ofNat (graph.contacts edge) + delta)

def Payload (face : Face) : Type :=
  match face with
  | .before | .after => Current source.material
  | .neural => Vector ByteArray 9
  | .plastic => Vector ByteArray 8
  | .weights => Fin edgeCount → Int
  | .body => Vector ByteArray 24
  | .world => Vector ByteArray 6
  | .inputs => Vector ByteArray 4
  | .sourceMaterial => Material

def readCompleted (face : Face) (current : Current source.material) : Payload source face :=
  match face with
  | .before | .after => current
  | .neural => intervalBytes source current 0 9 (by decide)
  | .plastic => intervalBytes source current 37 8 (by decide)
  | .weights => originalWeight source current
  | .body => intervalBytes source current 9 24 (by decide)
  | .world => ⟨#[bytesAt source current ⟨23, by decide⟩, bytesAt source current ⟨24, by decide⟩,
      bytesAt source current ⟨25, by decide⟩, bytesAt source current ⟨26, by decide⟩,
      bytesAt source current ⟨27, by decide⟩, bytesAt source current ⟨32, by decide⟩], by simp⟩
  | .inputs => intervalBytes source current 33 4 (by decide)
  | .sourceMaterial => source.material

def projectionLaw : SourceNativeProjectionLaw (restructuringSource source).toLedgerSource where
  Projection := Face
  ActiveAt := fun face {_} occurrence =>
    match face with
    | .before | .sourceMaterial => Unit
    | _ => CompletedAt source occurrence
  InactiveAt := fun face {_} occurrence =>
    match face with
    | .before | .sourceMaterial => PEmpty
    | _ => WaitingAt source occurrence
  classify := fun face {_} occurrence => by
    cases face <;> first | exact .inl () | exact classifyCompletion source occurrence
  PayloadAt := fun face {_} _ _ => Payload source face
  project := fun face {current} occurrence active =>
    match face with
    | .before => current
    | .sourceMaterial => source.material
    | .after => readCompleted source .after (afterAt source occurrence active)
    | .neural => readCompleted source .neural (afterAt source occurrence active)
    | .plastic => readCompleted source .plastic (afterAt source occurrence active)
    | .weights => readCompleted source .weights (afterAt source occurrence active)
    | .body => readCompleted source .body (afterAt source occurrence active)
    | .world => readCompleted source .world (afterAt source occurrence active)
    | .inputs => readCompleted source .inputs (afterAt source occurrence active)

def authoritySource : SourceNativeAuthoritySource (network source) (vocabulary source) where
  restructuringSource := restructuringSource source
  eventInventoryAdmission := .reflOfNoFaithfulTerminal (restructuringSource source)
    (fun _ => ⟨fun terminal => nomatch terminal⟩)
  lawSurface := .rootSemantic (network source)
  projectionLaw := projectionLaw source

/-- An owned effectful source root, not a fabricated pure closure. -/
structure IORoot where
  private mk ::
  fixedSource : Source

def installedIORoot : IORoot := ⟨source⟩

def IORoot.emit (root : IORoot) (current : Current root.fixedSource.material) :
    IO (GeneratedAt root.fixedSource current) := emitIO root.fixedSource current

def IORoot.initial (root : IORoot) : Current root.fixedSource.material := root.fixedSource.initial

def GeneratedAt.wordRead {current : Current source.material} (generated : GeneratedAt source current) (face : Face) :=
  (projectionLaw source).outcomeAt face generated.occurrence

theorem completed_after_read {current : Current source.material} (generated : GeneratedAt source current) :
    GeneratedAt.wordRead source generated .after = .inl ⟨(), generated.next⟩ := rfl

theorem completed_body_read {current : Current source.material} (generated : GeneratedAt source current) :
    GeneratedAt.wordRead source generated .body = .inl ⟨(), intervalBytes source generated.next 9 24 (by decide)⟩ := rfl

theorem ready_after_is_pending (current : Current source.material) :
    (projectionLaw source).outcomeAt .after (readyOccurrence source current) = .inr () := rfl

set_option linter.defProp false in
def actual_word_ledger_next {current : Current source.material} (generated : GeneratedAt source current) :=
  And.intro (actual_support source generated)
    (And.intro (actual_target_is_generated_next source generated)
      (And.intro (actual_next_clock source generated) (completed_after_read source generated)))

def installMaleCNSBodyIORoot (admitted : SourceWiringAdmission) : IO IORoot := do
  let source ← installSource admitted
  return installedIORoot source

end BodyIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
