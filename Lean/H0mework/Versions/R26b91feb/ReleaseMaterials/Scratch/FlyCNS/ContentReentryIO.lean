import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceContentFullIO
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentFullPackedIO
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BoundKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3BoundPublication

/-! Complete implementation reentry of the already born physical source.
This is a new Lean carrier of the same saved source; it does not reconstruct
the private old Source value or execute a new physical source birth. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace ContentReentryIO

open Admission PlasticAdmission Lean RepresentationIO

def physicalDirectory : System.FilePath := "Lean/scratch/FlyCNS/.cache/content-full-source-194395711321541"
def recordedDirectory : System.FilePath := physicalDirectory / "implementation-record"
def recordRegistrationSHA : String := "fe5c01267a3f068814824845503be3d4df3a15ff00ffea82f0955436f021f5ba"
def boundaryVisit : Nat := 2
abbrev Word := BodyIO.Word
abbrev Words := Vector Word 59

structure Material where
  private mk ::
  graph : MaleCNSAdmission
  siteBytes : ByteArray
  sites : NpyVector siteBytes
  site_count : sites.count = sourceSites
  site_bounds : ∀ site : Fin sourceSites, sites.word site.val < edgeCount
  site_positive : ∀ site : Fin sourceSites,
    graph.graph.rawGraph.transmitterSign (graph.graph.rawGraph.pre ⟨sites.word site.val, site_bounds site⟩) = 1
  directory : System.FilePath
  physicalDirectory : System.FilePath
  primitive : BodyIO.RawCodeFile
  linked : List BodyIO.RawCodeFile
  installation : ByteArray
  priorLedger : ByteArray
  model : ByteArray
  layout : Vector BodyIO.FieldLayout 59
  addresses : Vector (Fin 59) 59
  names : ∀ field, (layout.get (addresses.get field)).name = ContentFullIO.requiredNames.get field
  unique : ∀ left right : Fin 59, (layout.get left).name = (layout.get right).name → left = right
  complete : ∀ field : Fin 59, ∃ required : Fin 59,
    (layout.get field).name = ContentFullIO.requiredNames.get required
  instanceId : String
  occurrenceId : String
  installationId : String

def wordAt (material : Material) (words : Words) (field : Fin 59) : Word := words.get (material.addresses.get field)
def tickAt (material : Material) (words : Words) : Nat := (wordAt material words ⟨6, by decide⟩).vector.word 0
def bodyTick (material : Material) (words : Words) : Nat := (wordAt material words ⟨33, by decide⟩).vector.word 0
def physicsTick (material : Material) (words : Words) : Nat := (wordAt material words ⟨34, by decide⟩).vector.word 0
def ShapeAt (material : Material) (words : Words) : Prop :=
  (∀ field : Fin 59, if (material.layout.get field).varying then
    (words.get field).vector.count ≤ neuronCount else (words.get field).vector.count = (material.layout.get field).count) ∧
  (wordAt material words ⟨6, by decide⟩).vector.count = 1 ∧
  (wordAt material words ⟨33, by decide⟩).vector.count = 1 ∧
  (wordAt material words ⟨34, by decide⟩).vector.count = 1 ∧
  (wordAt material words ⟨39, by decide⟩).vector.count = (wordAt material words ⟨40, by decide⟩).vector.count ∧
  (wordAt material words ⟨41, by decide⟩).vector.count = (wordAt material words ⟨42, by decide⟩).vector.count
instance (material : Material) (words : Words) : Decidable (ShapeAt material words) := by unfold ShapeAt; infer_instance

structure Current (material : Material) where
  private mk ::
  words : Words
  shape : ShapeAt material words
  clock : tickAt material words = bodyTick material words
  backend : Vector ByteArray 4
  header : ByteArray
  visit : Nat
def Current.tick {material : Material} (current : Current material) : Nat := tickAt material current.words
def capture {material : Material} (current : Current material) : ContentFullPackedIO.Image :=
  ⟨current.words.map captureWord, current.backend, current.header, current.visit⟩
theorem capture_injective {material : Material} : Function.Injective (capture (material := material)) := by
  intro left right same
  have words : left.words = right.words := by
    apply Vector.ext
    intro field bound
    apply captureWord_injective
    have image := congrArg (fun images => images[field]) (congrArg ContentFullPackedIO.Image.words same)
    simpa only [capture, Vector.getElem_map] using image
  have backend := congrArg ContentFullPackedIO.Image.backend same
  have header := congrArg ContentFullPackedIO.Image.header same
  have visit := congrArg ContentFullPackedIO.Image.visit same
  cases left
  cases right
  simp_all [capture]

def readCurrent (material : Material) (path : System.FilePath) : IO (Current material) := do
  let words ← Vector.ofFnM fun field => do
    BodyIO.checkedResult (BodyIO.parseWord (material.layout.get field)
      (← IO.FS.readBinFile (path / (toString field.val ++ ".npy"))))
  let header ← IO.FS.readBinFile (path / "words.json")
  let doc : BodyFullIO.Header ← BodyIO.checkedJson (← BodyIO.readJson (path / "words.json"))
  if doc.schema != ContentFullIO.schema ∨ doc.instance_id != material.instanceId ∨
      doc.occurrence_id != material.occurrenceId ∨ doc.installation_sha256 != material.installationId ∨ doc.fields.size != 59 then
    throw (IO.userError "implementation reentry changed the original physical source identity or inventory")
  let backend ← Vector.ofFnM fun field => IO.FS.readBinFile (path / BodyIO.backendNames.get field)
  if shape : ShapeAt material words then
    if clock : tickAt material words = bodyTick material words then return ⟨words, shape, clock, backend, header, doc.root_visit⟩
    else throw (IO.userError "reentry neural and body clocks differ")
  else throw (IO.userError "reentry changes an original physical dimension")
def writeCurrent {material : Material} (current : Current material) (path : System.FilePath) : IO Unit := do
  IO.FS.createDirAll path
  for field in List.finRange 59 do IO.FS.writeBinFile (path / (toString field.val ++ ".npy")) (current.words.get field).bytes
  for field in List.finRange 4 do IO.FS.writeBinFile (path / BodyIO.backendNames.get field) (current.backend.get field)
  IO.FS.writeBinFile (path / "words.json") current.header

structure Source where
  private mk ::
  material : Material
  born : Current material
  born_tick : born.tick = 0
  born_visit : born.visit = 0
  initial : Current material
  initial_tick : initial.tick = 200
  initial_visit : initial.visit = boundaryVisit
  originalImage : ContentFullPackedIO.Image
  whole_transport : capture initial = originalImage

/-- Decode a newly generated complete image into the original born-source
Current. This parser creates neither a Source nor an evaluated successor. -/
def parseCurrentImage (source : Source) (image : ContentFullPackedIO.Image) :
    Except String (Current source.material) := do
  let text ← match String.fromUTF8? image.header with
    | some text => pure text
    | none => .error "the complete Current header is not valid UTF8"
  let raw ← Json.parse text
  let document : BodyFullIO.Header ← fromJson? raw
  if document.schema != ContentFullIO.schema || document.instance_id != source.material.instanceId ||
      document.occurrence_id != source.material.occurrenceId ||
      document.installation_sha256 != source.material.installationId || document.fields.size != 59 ||
      document.root_visit != image.visit then
    throw "the current belongs to another complete born source"
  let words ← Vector.ofFnM fun field =>
    BodyIO.parseWord (source.material.layout.get field) (image.words.get field).bytes
  for field in List.finRange 59 do
    let parsed := (words.get field).vector
    let given := image.words.get field
    if parsed.dataStart != given.dataStart || parsed.width != given.width || parsed.count != given.count then
      throw "the generated word descriptors disagree with their original NPY"
  if shape : ShapeAt source.material words then
    if clock : tickAt source.material words=bodyTick source.material words then
      return ⟨words,shape,clock,image.backend,image.header,image.visit⟩
    else throw "the original source neural/body clocks disagree"
  else throw "the source operation changes its complete original dimensions"

def guard (material : Material) : IO Unit := do
  BodyIO.guardCode material.primitive
  for file in material.linked do BodyIO.guardCode file
  if (← IO.FS.readBinFile (material.physicalDirectory / "installation.json")) != material.installation ∨
      (← IO.FS.readBinFile (material.physicalDirectory / "activation.json")) != material.priorLedger ∨
      (← IO.FS.readBinFile (material.physicalDirectory / "body.mjb")) != material.model then
    throw (IO.userError "the original physical source law or model changed")

/-- Reentry reads the actual original birth and the latest registered
Current. It never calls prepare, creates a UUID, or accepts a selected source. -/
def reopenSource : IO Source := do
  let graph ← Admission.loadMaleCNSFullGraph
  let directory := System.FilePath.mk "Lean/scratch/FlyCNS/.cache" / ("content-reentry-" ++ toString (← IO.monoNanosNow))
  if (← directory.pathExists) then throw (IO.userError "the new implementation directory is not fresh")
  let installation ← IO.FS.readBinFile (physicalDirectory / "installation.json")
  let priorLedger ← IO.FS.readBinFile (physicalDirectory / "activation.json")
  let ledger ← BodyIO.readJson (physicalDirectory / "activation.json")
  let ledgerFields : Nat ← BodyIO.checkedResult (ledger.getObjValAs? _ "field_count")
  let ledgerRows : Array Json ← BodyIO.checkedResult (ledger.getObjValAs? _ "steps")
  if ledgerFields != 59 ∨ ledgerRows.size != boundaryVisit then
    throw (IO.userError "reentry does not retain the original complete two-operation ledger")
  for index in [:ledgerRows.size] do
    let before : Nat ← BodyIO.checkedResult ((ledgerRows[index]!).getObjValAs? _ "before_visit")
    let after : Nat ← BodyIO.checkedResult ((ledgerRows[index]!).getObjValAs? _ "after_visit")
    let rows : Nat ← BodyIO.checkedResult ((ledgerRows[index]!).getObjValAs? _ "complete_ledger_rows")
    if before != index ∨ after != index + 1 ∨ rows != 6 then
      throw (IO.userError "reentry changes an original whole-ledger visit or responsibility row")
  let doc : BodyFullIO.Header ← BodyIO.checkedJson (← BodyIO.readJson (physicalDirectory / "initial" / "words.json"))
  let ledgerInstance : String ← BodyIO.checkedResult (ledger.getObjValAs? _ "instance_id")
  let ledgerOccurrence : String ← BodyIO.checkedResult (ledger.getObjValAs? _ "birth_occurrence")
  let ledgerInstallation : String ← BodyIO.checkedResult (ledger.getObjValAs? _ "installation")
  if ledgerInstance != doc.instance_id ∨ ledgerOccurrence != doc.occurrence_id ∨
      ledgerInstallation != doc.installation_sha256 then
    throw (IO.userError "the complete original ledger belongs to another born physical source")
  let lastTick : Nat ← BodyIO.checkedResult ((ledgerRows[1]!).getObjValAs? _ "after_tick")
  let lastPhysics : Nat ← BodyIO.checkedResult ((ledgerRows[1]!).getObjValAs? _ "physics_tick")
  let lastCurrent : String ← BodyIO.checkedResult ((ledgerRows[1]!).getObjValAs? _ "current")
  if lastTick != 200 ∨ lastPhysics != 2000 ∨ lastCurrent != (physicalDirectory / "observed-2").toString then
    throw (IO.userError "the reentry boundary is not the source's exact latest registered current")
  if size : doc.fields.size = 59 then
    let layout : Vector BodyIO.FieldLayout 59 := ⟨doc.fields, size⟩
    let addresses ← Vector.ofFnM fun field => BodyFullIO.sourceAddress layout (ContentFullIO.requiredNames.get field)
    if names : ∀ field : Fin 59, (layout.get (addresses.get field)).name = ContentFullIO.requiredNames.get field then
      if unique : ∀ left right : Fin 59, (layout.get left).name = (layout.get right).name → left = right then
        if complete : ∀ field : Fin 59, ∃ required : Fin 59,
            (layout.get field).name = ContentFullIO.requiredNames.get required then
          let refs : Array BodyIO.CapturedFile ← BodyIO.checkedResult
            ((← BodyIO.readJson (physicalDirectory / "installation.json")).getObjValAs? _ "files")
          let mut linked : List BodyIO.RawCodeFile := []
          for ref in refs do
            let path := physicalDirectory / ref.relative
            linked := linked ++ [⟨System.FilePath.mk ref.path, path, ← IO.FS.readBinFile path⟩]
          let original := graph.graph.vectors.original
          let rawFiles : List (String × ByteArray) := [
            ("data/body-annotations-male-cns-v1.0-minconf-0.5.feather", graph.annotations),
            ("data/body-neurotransmitters-male-cns-v1.0.feather", graph.neurotransmitters),
            ("data/connectome-weights-male-cns-v1.0-minconf-0.5.feather", graph.originalWeights),
            ("graph/body_ids.npy", original.bodyIds), ("graph/indptr.npy", original.indptr),
            ("graph/indices.npy", original.indices), ("graph/counts.npy", original.counts),
            ("graph/sign.npy", original.sign), ("graph/source_row.npy", original.sourceRow)]
          for (relative, bytes) in rawFiles do
            let path := physicalDirectory / "raw" / relative
            if (← IO.FS.readBinFile path) != bytes then throw (IO.userError "the reentered graph is not the original complete admitted graph")
            linked := linked ++ [⟨path, path, bytes⟩]
          for (relative, sha, size) in [
              ("graph/manifest.json", "2566977e6d32f0664eeb1be65cd33cd0cf6e9a2053a041d3c08a89f0025c20e2", 2361),
              ("graph/mushroom-body/role_kc.npy", "e049b03d297a0f1f3263d2c875cca49161fec9509123c676fc25680a710d4400", 165250),
              ("graph/mushroom-body/role_dan.npy", "fcf6e07be558864bcdeae76371bc90ed4084e11b333bb5f6c4ac05f13e94ad74", 165250),
              ("graph/mushroom-body/role_mbon.npy", "9fbf4d71c08e7fbe14c2e6c33a5254d871d1fa9bb4f6c90f4cf2af258385dcc5", 165250),
              ("graph/mushroom-body/domain_neurons.npy", "07776718fbcb7b5f80d35b407f57c280afef3c786fdfdc5d39c8d7073cae9404", 516),
              ("graph/mushroom-body/site_edges.npy", "252908f1568834a3f3eef9cdfe43a336e76a959cf98790da67ddfb6cdac76852", 489808),
              ("graph/mushroom-body/site_domains.npy", "b490068dfbd1d973557f78d49004c3b1e4998267f618904f03c6b1eb64c24b1a", 244968),
              ("graph/mushroom-body/dan_edges.npy", "5393e13575cba2a796728daa8c334716ba4420ee54d4d0c20edf4e32c66992cf", 25112),
              ("graph/mushroom-body/dan_domains.npy", "72447abafb0b9b8b015f25bf09e30a890eb8ddeb7a1519b38dfbe101898e3795", 12620)] do
            let bytes ← Admission.readFrozenFile relative sha size
            let path := physicalDirectory / "raw" / relative
            if (← IO.FS.readBinFile path) != bytes then throw (IO.userError "the reentry changes an original admitted role coordinate")
            linked := linked ++ [⟨path, path, bytes⟩]
          let siteBytes ← IO.FS.readBinFile (physicalDirectory / "raw/graph/mushroom-body/site_edges.npy")
          let sites ← BodyIO.checkedResult (parseNpyVector siteBytes "<i8" 8)
          if siteCount : sites.count = sourceSites then
            if siteBounds : ∀ site : Fin sourceSites, sites.word site.val < edgeCount then
              if sitePositive : ∀ site : Fin sourceSites,
                  graph.graph.rawGraph.transmitterSign
                    (graph.graph.rawGraph.pre ⟨sites.word site.val, siteBounds site⟩) = 1 then
                let primitivePath := physicalDirectory / "primitive.py"
                let material : Material := ⟨graph, siteBytes, sites, siteCount, siteBounds, sitePositive, directory, physicalDirectory,
                  ⟨"Lean/scratch/FlyCNS/content_full_primitive.py", primitivePath, ← IO.FS.readBinFile primitivePath⟩,
                  linked, installation, priorLedger, ← IO.FS.readBinFile (physicalDirectory / "body.mjb"),
                  layout, addresses, names, unique, complete, doc.instance_id, doc.occurrence_id, doc.installation_sha256⟩
                guard material
                let born ← readCurrent material (physicalDirectory / "initial")
                let initial ← readCurrent material (physicalDirectory / "observed-2")
                if bornTick : born.tick = 0 then
                  if bornVisit : born.visit = 0 then
                    if tick : initial.tick = 200 then
                      if visit : initial.visit = boundaryVisit then
                        IO.FS.createDirAll directory
                        writeCurrent initial (directory / "initial")
                        let restored ← readCurrent material (directory / "initial")
                        if transport : capture restored = capture initial then
                          return ⟨material, born, bornTick, bornVisit, restored, by rw [capture_injective transport]; exact tick,
                            by rw [capture_injective transport]; exact visit, capture initial, transport⟩
                        else throw (IO.userError "complete implementation transport changed one original coordinate")
                      else throw (IO.userError "reentry starts at another original source visit")
                    else throw (IO.userError "reentry starts at another physical tick")
                  else throw (IO.userError "the original source did not begin at its birth visit")
                else throw (IO.userError "the original source did not begin at its neural birth")
              else throw (IO.userError "an original learned site changes its positive transmitter sign")
            else throw (IO.userError "an original learned site leaves the complete graph")
          else throw (IO.userError "the original learned-site inventory changes")
        else throw (IO.userError "reentry omits an original source coordinate")
      else throw (IO.userError "reentry aliases original source coordinates")
    else throw (IO.userError "reentry changes original state role names")
  else throw (IO.userError "reentry does not retain all 59 original coordinates")

structure Reply (source : Source) (current : Current source.material) where
  private mk ::
  after : Current source.material
  next_visit : after.visit = current.visit + 1
  next_tick : after.tick = current.tick + (BodyFullIO.operationAt current.visit).microTicks
  next_physics : physicsTick source.material after.words = physicsTick source.material current.words +
    10 * (BodyFullIO.operationAt current.visit).microTicks
  events : ByteArray
  learning : ByteArray
  physics : ByteArray

/-- Fixed raw-derived installation; this performs no neural/physical step. -/
def installPure (source : Source) : IO _root_.FlyCNS.C3BoundKernel.Installation := do
  guard source.material
  if source.material.physicalDirectory != physicalDirectory then throw (IO.userError "pure producer belongs to another physical source")
  let original ← BodyIO.readJson (source.material.physicalDirectory/"installation.json")
  let sha : String ← BodyIO.checkedResult (original.getObjValAs? _ "source_programme_sha256")
  if sha != "c7b485e855c3018d16284cf8930cc3a862be537a7a62d99f71cd1caa5b445780" then
    throw (IO.userError "pure producer does not own the original C7 programme")
  _root_.FlyCNS.C3BoundKernel.install ⟨source.material.instanceId,source.material.occurrenceId,source.material.installationId⟩

/-- Numerical generation is internal and fixed. The caller supplies the
already sealed installation and this source's complete original Current. -/
def invokePure (source : Source) (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (current : Current source.material) : Except String (_root_.FlyCNS.C3Successful.Result × Current source.material) := do
  if installed.identity.instanceId != source.material.instanceId || installed.identity.occurrenceId != source.material.occurrenceId ||
      installed.identity.installationId != source.material.installationId then throw "pure material belongs to another source"
  let named := (List.finRange 59).toArray.map fun i =>
    let field := current.words.get i
    ((source.material.layout.get i).name,
      _root_.FlyCNS.C3Integer.Word.mk field.vector.width (field.bytes.extract field.vector.dataStart field.bytes.size))
  let result ← _root_.FlyCNS.C3BoundKernel.generate installed ⟨named,current.backend.get ⟨3,by decide⟩,current.visit⟩
  let written := result.written
  if count : written.words.size=59 then
    let rawWords : Vector ByteArray 59 := ⟨written.words,count⟩
    let parsed ← Vector.ofFnM fun i => BodyIO.parseWord (source.material.layout.get i) (rawWords.get i)
    if backends : written.archives.size=3 then
      let original : Vector ByteArray 3 := ⟨written.archives,backends⟩
      let complete : Vector ByteArray 4 := original++(⟨#[written.sourceDocument],rfl⟩ : Vector ByteArray 1)
      let after ← parseCurrentImage source ⟨parsed.map captureWord,complete,written.header,written.visit⟩
      return (result,after)
    else throw "pure source writer omitted an original backend"
  else throw "pure source writer omitted an original coordinate"

/-- Original compressed formatting receives only internally generated PL
members. It cannot evaluate a neuron/body or select a future coordinate. -/
private def formatPureLearning (source : Source) (generated : _root_.FlyCNS.C3Successful.Result) : IO ByteArray := do
  match generated.learning with
  | none => return ByteArray.empty
  | some members =>
    let path := source.material.directory/("pure-learning-"++toString (← IO.monoNanosNow))
    IO.FS.createDirAll path
    let mut descriptions := #[]
    for i in [:members.size] do
      if h : i<members.size then
        let m := members[i]
        IO.FS.writeBinFile (path/(toString i++".bin")) m.payload
        descriptions:=descriptions.push (Json.mkObj [("name",toJson m.name),("dtype",toJson m.dtype),("shape",toJson m.shape)])
    IO.FS.writeFile (path/"members.json") (Json.arr descriptions).compress
    let programme := "from pathlib import Path\nimport sys,json,numpy as np\np=Path(sys.argv[1])\nd=json.loads((p/'members.json').read_text())\na={m['name']:np.fromfile(p/(str(i)+'.bin'),dtype=m['dtype']).reshape(m['shape']) for i,m in enumerate(d)}\nnp.savez_compressed(p/'learning.npz',**a)\n"
    let result ← IO.Process.output {cmd:="Biomedical/Connectomics/.venv/bin/python",args:=#["-c",programme,path.toString]}
    if result.exitCode != 0 then throw (IO.userError result.stderr)
    IO.FS.readBinFile (path/"learning.npz")

def replyPure (source : Source) (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (current : Current source.material) : IO (Reply source current) := do
  guard source.material
  let (generated,after) ← BodyIO.checkedResult (invokePure source installed current)
  let learning ← formatPureLearning source generated
  if visit : after.visit=current.visit+1 then
    if tick : after.tick=current.tick+(BodyFullIO.operationAt current.visit).microTicks then
      if physical : physicsTick source.material after.words=physicsTick source.material current.words+
          10*(BodyFullIO.operationAt current.visit).microTicks then
        return ⟨after,visit,tick,physical,generated.events,learning,generated.physics.getD ByteArray.empty⟩
      else throw (IO.userError "the pure source omits a physical microcycle")
    else throw (IO.userError "the pure source omits a neural microcycle")
  else throw (IO.userError "the pure source omits its registered next visit")

def invoke (source : Source) (current : Current source.material) : IO (Reply source current) := do
  guard source.material
  let nonce ← IO.monoNanosNow
  let input := source.material.directory / ("current-" ++ toString nonce)
  let output := source.material.directory / ("generated-" ++ toString nonce)
  writeCurrent current input
  if (← output.pathExists) then throw (IO.userError "the reentered native next was preinstalled")
  let result ← IO.Process.output {
    cmd := "Biomedical/Connectomics/.venv/bin/python"
    args := #[source.material.primitive.capturedPath.toString, "step", source.material.physicalDirectory.toString,
      input.toString, output.toString] }
  if result.exitCode != 0 then throw (IO.userError ("original physical source continuation failed: " ++ result.stderr))
  let after ← readCurrent source.material output
  if visit : after.visit = current.visit + 1 then
    if tick : after.tick = current.tick + (BodyFullIO.operationAt current.visit).microTicks then
      if physical : physicsTick source.material after.words = physicsTick source.material current.words +
          10 * (BodyFullIO.operationAt current.visit).microTicks then
        let learning ← if BodyFullIO.operationAt current.visit == .neural then
          IO.FS.readBinFile (output / "learning-trace.npz") else pure ByteArray.empty
        let physics ← if BodyFullIO.operationAt current.visit == .neural then
          IO.FS.readBinFile (output / "physics-trace.npz") else pure ByteArray.empty
        return ⟨after, visit, tick, physical, ← IO.FS.readBinFile (output / "generated-events.npz"),
          learning, physics⟩
      else throw (IO.userError "the reentered source omits a physical microcycle")
    else throw (IO.userError "the reentered source omits a neural microcycle")
  else throw (IO.userError "the reentered source omits its registered next visit")

/-- Decode a completed source record. This readout does not generate a new
physical operation; the registered predecessor is checked by the public
source-specific entry points below. -/
private def readCompletedAt (source : Source) (current : Current source.material)
    (path : System.FilePath) : IO (Reply source current) := do
  guard source.material
  let after ← readCurrent source.material path
  if visit : after.visit = current.visit + 1 then
    if tick : after.tick = current.tick + (BodyFullIO.operationAt current.visit).microTicks then
      if physical : physicsTick source.material after.words = physicsTick source.material current.words +
          10 * (BodyFullIO.operationAt current.visit).microTicks then
        return ⟨after, visit, tick, physical, ← IO.FS.readBinFile (path / "generated-events.npz"),
          ← IO.FS.readBinFile (path / "learning-trace.npz"), ← IO.FS.readBinFile (path / "physics-trace.npz")⟩
      else throw (IO.userError "the recorded source omits a physical microcycle")
    else throw (IO.userError "the recorded source omits a neural microcycle")
  else throw (IO.userError "the recorded source omits its original registered visit")

def readOriginalReply (source : Source) (current : Current source.material) : IO (Reply source current) := do
  if current.visit ≥ boundaryVisit then throw (IO.userError "this is not an original prior registered write")
  let input := if current.visit = 0 then source.material.physicalDirectory / "initial" else
    source.material.physicalDirectory / ("observed-" ++ toString current.visit)
  let original ← readCurrent source.material input
  if capture original != capture current then
    throw (IO.userError "the original ledger is being read at another complete predecessor")
  readCompletedAt source current (source.material.physicalDirectory / ("observed-" ++ toString (current.visit + 1)))

/-- The implementation's completed native record is consumed only after its
actual source-owned report binds original identity, boundary and two later
visits. Neither a caller-selected target nor a six-point proof is input. -/
def readImplementationReply (source : Source)
    (current : Current source.material) (reopened : Bool := false) : IO (Reply source current) := do
  let implementation := recordedDirectory
  let registered ← IO.FS.readBinFile (implementation / "registration.json")
  if (← Admission.sha256Bytes registered) != recordRegistrationSHA then
    throw (IO.userError "the physical source's actual complete reentry registration changed")
  let registration ← BodyIO.readJson (implementation / "registration.json")
  let originalImplementation : String ← BodyIO.checkedResult (registration.getObjValAs? _ "original_implementation")
  let registrationSchema : String ← BodyIO.checkedResult (registration.getObjValAs? _ "schema")
  if registrationSchema != "flycns-source-fixed-complete-reentry-record/v1" then
    throw (IO.userError "the physical source has no fixed complete implementation record")
  let originals : Array Json ← BodyIO.checkedResult (registration.getObjValAs? _ "artifacts")
  let required : List String := (List.range 59).map (fun index => toString index ++ ".npy") ++
    ["neural.npz", "body.npz", "source-state.npz", "source.json", "words.json",
      "generated-events.npz", "learning-trace.npz", "physics-trace.npz"]
  let groups := ["observed-3", "following/original", "following/reopened", "independent-3", "independent-4"]
  if originals.size != groups.length * required.length then
    throw (IO.userError "the fixed record omits a complete native or independent carrier")
  for group in groups do
    for name in required do
      let relative := group ++ "/" ++ name
      let matching ← originals.filterM fun row => do
        let path : String ← BodyIO.checkedResult (row.getObjValAs? _ "relative")
        return path == relative
      if matching.size != 1 then throw (IO.userError "the fixed record aliases or omits an actual artifact")
      let sha : String ← BodyIO.checkedResult ((matching[0]!).getObjValAs? _ "sha256")
      let size : Nat ← BodyIO.checkedResult ((matching[0]!).getObjValAs? _ "size_bytes")
      let bytes ← IO.FS.readBinFile (implementation / relative)
      if bytes.size != size ∨ (← Admission.sha256Bytes bytes) != sha then
        throw (IO.userError "one registered native or independent artifact changed")
  for (native, independent) in [("observed-3", "independent-3"), ("following/original", "independent-4"),
      ("following/reopened", "independent-4")] do
    for name in required do
      if (← IO.FS.readBinFile (implementation / native / name)) !=
          (← IO.FS.readBinFile (implementation / independent / name)) then
        throw (IO.userError "the fixed recorded native operation differs from its complete independent recurrence")
  for (visit, beforeTick, afterTick) in [(3, 200, 300), (4, 300, 400)] do
    let independent ← BodyIO.readJson (implementation / ("independent-" ++ toString visit ++ ".json"))
    for (key, expected) in [("original_source", (← IO.currentDir) / physicalDirectory |>.toString),
        ("implementation", (← IO.currentDir) / System.FilePath.mk originalImplementation |>.toString),
        ("instance_id", source.material.instanceId), ("occurrence_id", source.material.occurrenceId),
        ("installation_sha256", source.material.installationId),
        ("reader_sha256", "db461428e22247258642ed302afd458ac43da0d8957fdbed838f94c2d5ecb6ae"),
        ("original_current", ((← IO.currentDir) / System.FilePath.mk originalImplementation /
          ("independent-input-" ++ toString (visit - 1))).toString),
        ("native_output", ((← IO.currentDir) / System.FilePath.mk originalImplementation /
          (if visit = 3 then "observed-3" else "following/original")).toString),
        ("underlying_independent_reader_sha256", "02c272d39422638929575de37be3000c459ec4d06031e31ee57379f618304504")] do
      let actual : String ← BodyIO.checkedResult (independent.getObjValAs? _ key)
      if actual != expected then throw (IO.userError "the fixed independent record has another original source or reader")
    for (key, expected) in [("before_visit", visit - 1), ("after_visit", visit),
        ("before_tick", beforeTick), ("after_tick", afterTick), ("literal_files", 67)] do
      let actual : Nat ← BodyIO.checkedResult (independent.getObjValAs? _ key)
      if actual != expected then throw (IO.userError "the fixed independent record has another origin or incomplete occurrence")
  let report ← BodyIO.readJson (implementation / "reentry-six.json")
  for (key, expected) in [("schema", "flycns-same-source-complete-reentry-six/v1"),
      ("physical_source", source.material.physicalDirectory.toString),
      ("implementation", originalImplementation), ("instance_id", source.material.instanceId),
      ("occurrence_id", source.material.occurrenceId), ("installation_sha256", source.material.installationId)] do
    let actual : String ← BodyIO.checkedResult (report.getObjValAs? _ key)
    if actual != expected then throw (IO.userError "the recorded continuation belongs to another source or implementation")
  for (key, expected) in [("before_visit", 2), ("after_visit", 3), ("following_visit", 4),
      ("before_tick", 200), ("after_tick", 300), ("following_tick", 400)] do
    let actual : Nat ← BodyIO.checkedResult (report.getObjValAs? _ key)
    if actual != expected then throw (IO.userError "the recorded continuation is not the original current's two actual successors")
  if current.visit != 2 ∧ current.visit != 3 then
    throw (IO.userError "the implementation has no actual completed record at this visit")
  if reopened ∧ current.visit != 3 then
    throw (IO.userError "the implementation has no reopened branch at this visit")
  let input := if current.visit = 2 then source.material.physicalDirectory / "observed-2" else implementation / "observed-3"
  let before ← readCurrent source.material input
  if capture before != capture current then
    throw (IO.userError "the recorded implementation does not continue this complete predecessor")
  let output := if current.visit = 2 then implementation / "observed-3" else
    implementation / (if reopened then "following/reopened" else "following/original")
  readCompletedAt source current output

def publicationInput (source : Source) (current : Current source.material) : _root_.FlyCNS.C3BoundState.RawCurrent :=
  let named := (List.finRange 59).toArray.map fun i =>
    let field := current.words.get i
    ((source.material.layout.get i).name,
      _root_.FlyCNS.C3Integer.Word.mk field.vector.width (field.bytes.extract field.vector.dataStart field.bytes.size))
  ⟨named,current.backend.get ⟨3,by decide⟩,current.visit⟩

private def decodePublication (source : Source) (published : _root_.FlyCNS.C3Published.Result) :
    Except String (Current source.material) := do
  let written := published.numerical.written
  if count : written.words.size=59 then
    let rawWords : Vector ByteArray 59 := ⟨written.words,count⟩
    let parsed ← Vector.ofFnM fun i => BodyIO.parseWord (source.material.layout.get i) (rawWords.get i)
    if backends : written.archives.size=3 then
      let original : Vector ByteArray 3 := ⟨written.archives,backends⟩
      let complete : Vector ByteArray 4 := original++(⟨#[written.sourceDocument],rfl⟩ : Vector ByteArray 1)
      parseCurrentImage source ⟨parsed.map captureWord,complete,written.header,written.visit⟩
    else throw "pure source writer omitted an original backend"
  else throw "pure source writer omitted an original coordinate"

structure PublishedReplyAt (source : Source) (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (current : Current source.material) where
  private mk ::
  published : _root_.FlyCNS.C3Published.Result
  reply : Reply source current
  generated : _root_.FlyCNS.C3BoundPublication.generate installed (publicationInput source current)=.ok published
  decoded : decodePublication source published=.ok reply.after
  events : reply.events=published.numerical.events
  learning : reply.learning=published.learning
  physics : reply.physics=published.numerical.physics.getD ByteArray.empty

/-- Source-owned publication keeps the internally generated result and the
original private Reply together. All numeric/metadata/trace bytes are pure;
the effect layer only checks the existing source guard. -/
def replyPublished (source : Source) (installed : _root_.FlyCNS.C3BoundKernel.Installation)
    (current : Current source.material) : IO (PublishedReplyAt source installed current) := do
  guard source.material
  if installed.identity.instanceId != source.material.instanceId ||
      installed.identity.occurrenceId != source.material.occurrenceId ||
      installed.identity.installationId != source.material.installationId then
    throw (IO.userError "pure material belongs to another source")
  match generated:_root_.FlyCNS.C3BoundPublication.generate installed (publicationInput source current) with
  | .error why => throw (IO.userError why)
  | .ok published =>
    match decoded:decodePublication source published with
    | .error why => throw (IO.userError why)
    | .ok after =>
      if visit:after.visit=current.visit+1 then
        if tick:after.tick=current.tick+(BodyFullIO.operationAt current.visit).microTicks then
          if physical:physicsTick source.material after.words=physicsTick source.material current.words+
              10*(BodyFullIO.operationAt current.visit).microTicks then
            let reply : Reply source current := ⟨after,visit,tick,physical,published.numerical.events,
              published.learning,published.numerical.physics.getD ByteArray.empty⟩
            return ⟨published,reply,generated,decoded,rfl,rfl,rfl⟩
          else throw (IO.userError "the pure source omits a physical microcycle")
        else throw (IO.userError "the pure source omits a neural microcycle")
      else throw (IO.userError "the pure source omits its registered next visit")

end ContentReentryIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
