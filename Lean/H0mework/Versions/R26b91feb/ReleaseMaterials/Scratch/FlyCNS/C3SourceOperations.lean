import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentReentryLedger

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3

open ContentReentryIO ContentReentryRoot

/-- Complete literal register inventory of the held original source. -/
def registers (source : ContentReentryIO.Source) := source.material.layout

structure NormalFormAt (source : ContentReentryIO.Source)
    (current : ContentReentryIO.Current source.material) where
  private mk ::
  after : ContentReentryIO.Current source.material
  next_visit : after.visit = current.visit + 1
  next_tick : after.tick = current.tick + (BodyFullIO.operationAt current.visit).microTicks
  next_physics : ContentReentryIO.physicsTick source.material after.words =
    ContentReentryIO.physicsTick source.material current.words +
    10 * (BodyFullIO.operationAt current.visit).microTicks
  events : ByteArray
  learning : ByteArray
  physics : ByteArray

/-- The concrete interpreter takes only the held original material and
complete current. No evaluator, target state or physics-after is a parameter.
It is effectful here; a pure primitive semantics must be paid separately. -/
def execute (source : ContentReentryIO.Source)
    (current : ContentReentryIO.Current source.material) :
    IO (NormalFormAt source current) := do
  ContentReentryIO.guard source.material
  let nonce ← IO.monoNanosNow
  let directory := System.FilePath.mk "Lean/scratch/FlyCNS/.cache/C3" / toString nonce
  let input := directory / "before"
  let output := directory / "generated"
  ContentReentryIO.writeCurrent current input
  let result ← IO.Process.output {
    cmd := "Biomedical/Connectomics/.venv/bin/python"
    args := #["Lean/scratch/FlyCNS/C3Programme.py", "generate", output.toString,
      "--current", input.toString] }
  if result.exitCode != 0 then
    throw (IO.userError ("the original C7 operation programme failed: " ++ result.stderr))
  let after ← ContentReentryIO.readCurrent source.material output
  if visit : after.visit = current.visit + 1 then
    if tick : after.tick = current.tick + (BodyFullIO.operationAt current.visit).microTicks then
      if physics : ContentReentryIO.physicsTick source.material after.words =
          ContentReentryIO.physicsTick source.material current.words +
          10 * (BodyFullIO.operationAt current.visit).microTicks then
        let learning ← if BodyFullIO.operationAt current.visit == .neural then
          IO.FS.readBinFile (output / "learning-trace.npz") else pure ByteArray.empty
        let physical ← if BodyFullIO.operationAt current.visit == .neural then
          IO.FS.readBinFile (output / "physics-trace.npz") else pure ByteArray.empty
        return ⟨after, visit, tick, physics, ← IO.FS.readBinFile (output / "generated-events.npz"), learning, physical⟩
      else throw (IO.userError "the source operation graph omitted a physical microstep")
    else throw (IO.userError "the source operation graph omitted a neural microstep")
  else throw (IO.userError "the source operation graph omitted the registered next visit")

structure AcceptedAt (source : ContentReentryIO.Source)
    (current : ContentReentryIO.Current source.material) where
  private mk ::
  computed : NormalFormAt source current
  original : ContentReentryRoot.GeneratedAt source current
  whole : ContentReentryIO.capture computed.after = ContentReentryIO.capture original.next
  events : computed.events = original.reply.events
  learning : computed.learning = original.reply.learning
  physics : computed.physics = original.reply.physics

def normalFormDirectory : System.FilePath := "Lean/scratch/FlyCNS/.cache/C3/normal-form-validation"

/-- Read the already executed normal forms of this new concrete producer.
The validation entry fixes its original NN200 input and two consecutive
computations. No original source operation is run by this reader. -/
def readComputed (source : ContentReentryIO.Source)
    (current : ContentReentryIO.Current source.material) : IO (NormalFormAt source current) := do
  ContentReentryIO.guard source.material
  if current.visit != 2 ∧ current.visit != 3 then
    throw (IO.userError "the C3 constructor has no recorded computation at this source visit")
  let report ← BodyIO.readJson (normalFormDirectory / "result.json")
  let constructor : String ← BodyIO.checkedResult (report.getObjValAs? _ "constructor_sha256")
  if constructor != "bfec5186b756e3642f2c583e951d7769b008dec01f784b323a55fdd47a074774" then
    throw (IO.userError "the C3 normal form comes from another constructor")
  let output := normalFormDirectory / ("generated-" ++ toString (current.visit + 1))
  let after ← ContentReentryIO.readCurrent source.material output
  if visit : after.visit = current.visit + 1 then
    if tick : after.tick = current.tick + (BodyFullIO.operationAt current.visit).microTicks then
      if physics : ContentReentryIO.physicsTick source.material after.words =
          ContentReentryIO.physicsTick source.material current.words +
          10 * (BodyFullIO.operationAt current.visit).microTicks then
        return ⟨after, visit, tick, physics, ← IO.FS.readBinFile (output / "generated-events.npz"),
          ← IO.FS.readBinFile (output / "learning-trace.npz"), ← IO.FS.readBinFile (output / "physics-trace.npz")⟩
      else throw (IO.userError "recorded C3 normal form physical interval differs")
    else throw (IO.userError "recorded C3 normal form neural interval differs")
  else throw (IO.userError "recorded C3 normal form source visit differs")

/-- The original actual occurrence is read only after the source-only
operation normal form has been computed. Its tapes cannot drive execution. -/
def consumeOriginal (source : ContentReentryIO.Source)
    (current : ContentReentryIO.Current source.material) : IO (AcceptedAt source current) := do
  let computed ← execute source current
  let original ← ContentReentryRoot.readImplementation source current
  if whole : ContentReentryIO.capture computed.after = ContentReentryIO.capture original.next then
    if events : computed.events = original.reply.events then
      if learning : computed.learning = original.reply.learning then
        if physics : computed.physics = original.reply.physics then
          return ⟨computed, original, whole, events, learning, physics⟩
        else throw (IO.userError "C3 original physical operation trace differs")
      else throw (IO.userError "C3 original learning operation trace differs")
    else throw (IO.userError "C3 original operation events differ")
  else throw (IO.userError "C3 complete original operation normal form differs")

def consumeComputed (source : ContentReentryIO.Source)
    (current : ContentReentryIO.Current source.material) : IO (AcceptedAt source current) := do
  let computed ← readComputed source current
  let original ← ContentReentryRoot.readImplementation source current
  if whole : ContentReentryIO.capture computed.after = ContentReentryIO.capture original.next then
    if events : computed.events = original.reply.events then
      if learning : computed.learning = original.reply.learning then
        if physics : computed.physics = original.reply.physics then
          return ⟨computed, original, whole, events, learning, physics⟩
        else throw (IO.userError "recorded C3 original physical operation trace differs")
      else throw (IO.userError "recorded C3 original learning operation trace differs")
    else throw (IO.userError "recorded C3 original operation events differ")
  else throw (IO.userError "recorded C3 complete original operation normal form differs")

theorem generated_current_exact (source : ContentReentryIO.Source)
    {current : ContentReentryIO.Current source.material} (accepted : AcceptedAt source current) :
    accepted.computed.after = accepted.original.next :=
  ContentReentryIO.capture_injective accepted.whole

/-- Direct consumer: the generated object has the original occurrence,
ledger compiler, six destination rows and complete next current. -/
theorem all_original_rows (source : ContentReentryIO.Source)
    {current : ContentReentryIO.Current source.material}
    (generated : ContentReentryRoot.GeneratedAt source current)
    (responsibility : ContentReentryRoot.Responsibility) :
    (generated.patch.toLedgerWriteEvolution.destination
      (ContentReentryRoot.entry source current responsibility)).1 =
      ContentReentryRoot.entry source generated.next responsibility :=
  ContentReentryRoot.actual_six_rows source generated responsibility

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3
