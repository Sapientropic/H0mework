import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3WriterStep
set_option autoImplicit false
namespace FlyCNS.C3Raw
open FlyCNS.C3Integer

structure Material where
  writer : FlyCNS.C3Writer.Material

/-- All original body words are retained, including immutable installation,
controller RNG inventory and flags. Numeric projections never replace them. -/
structure Current where
  numerical : FlyCNS.C3Native.State
  bodyWords : Array Word
  sourceDocument : ByteArray
  visit : Nat
  traceBytes : Array ByteArray
  metadata : Array (String × ByteArray)

def floats (values : Array Float) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for value in values do
    for b in [:8] do bytes := bytes.push ((value.toBits >>> UInt64.ofNat (8*b)).toUInt8)
  return bytes
def signed (values : A) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for value in values do
    for b in [:8] do bytes := bytes.push ((value.toUInt64 >>> UInt64.ofNat (8*b)).toUInt8)
  return bytes
def narrow (values : Array Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for value in values do
    for b in [:4] do bytes := bytes.push ((UInt32.ofNat value >>> UInt32.ofNat (8*b)).toUInt8)
  return bytes

def neuralNames : Array String := #["voltage","conductance","refractory","delay_nodes","delay_counts","cursor","tick",
  "random_seed","installation_sha256","adaptation_uv","release_q","dopamine_rise_q","dopamine_decay_q","dopamine_fraction_q",
  "apl_voltage_uv","apl_conductance_uv","apl_dopamine_rise_q","apl_dopamine_decay_q","apl_dopamine_fraction_q",
  "kc_muscarinic_rise_q","kc_muscarinic_activation_q"]
def plasticNames : Array String := #["plastic_eligibility_q","plastic_dopamine_q","plastic_labile_q","plastic_stable_q",
  "plastic_delta_uv","plastic_last_update_tick","plastic_modulation_scratch_q"]
def indexOf (names : Array String) (name : String) : Nat := Id.run do
  for i in [:names.size] do if names[i]! == name then return i
  return 0
def integerBytes (values : A) (width : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for value in values do
    for b in [:width] do bytes := bytes.push ((value.toUInt64 >>> UInt64.ofNat (8*b)).toUInt8)
  return bytes
def bodyIndex (material : Material) (name : String) : Nat := Id.run do
  let mut body := 0
  for f in material.writer.fields do
    if f.name.startsWith "body." then
      if f.name=="body."++name then return body
      body := body+1
  return body
def updateWord (words : Array Word) (index width : Nat) (bytes : ByteArray) : Array Word :=
  words.set! index ⟨width,bytes⟩

def bodyWords (m : Material) (before : Current) (after : FlyCNS.C3Native.State) (neuralTicks : Nat) : Array Word := Id.run do
  let body := after.body
  let mut words := before.bodyWords
  let physical := body.physics
  let oldIntegration := before.bodyWords[bodyIndex m "integration"]!
  -- Original mjSTATE_INTEGRATION order: time,qpos,qvel,warmstart,ctrl,
  -- qfrc_applied,xfrc_applied. The applied external-body tail remains source data.
  let integration := floats (#[physical.time]++physical.position++physical.velocity++physical.warmstart++physical.control++physical.applied) ++
    oldIntegration.bytes.extract (8*348) oldIntegration.bytes.size
  words := updateWord words (bodyIndex m "integration") 8 integration
  for (name,value) in [("controller_phases",body.gait.oscillator.phases),("controller_magnitudes",body.gait.oscillator.magnitudes),
    ("controller_intrinsic_freqs",body.gait.oscillator.frequencies),("controller_intrinsic_amps",body.gait.oscillator.amplitudes),
    ("controller_retraction",body.gait.retraction),("controller_stumbling",body.gait.stumbling),
    ("motor_trace",body.signal.motor),("descending_trace",body.signal.descending),("feeding_trace",#[body.signal.feeding]),
    ("world_values",body.resource.values),("sugar_stock",body.resource.sugar),("water_stock",body.resource.water),
    ("odor_gain",body.odorGains),("peptide_concentrations",body.resource.peptide),("steering_trace",body.signal.steering)] do
    words := updateWord words (bodyIndex m name) 8 (floats value)
  words := updateWord words (bodyIndex m "controller_persistence") 8 (signed body.gait.persistence)
  for (name,increment) in [("tick",neuralTicks),("physics_ticks",10*neuralTicks)] do
    let i := bodyIndex m name
    words := updateWord words i 8 (signed #[before.bodyWords[i]!.int 0+Int64.ofNat increment])
  words := updateWord words (bodyIndex m "controller_enabled") 1
    ⟨#[if body.signal.controllerEnabled then 1 else 0]⟩
  return words

/-- Every original field is reconstituted with its source dtype/shape.
Immutable byte/RNG/context material is preserved, never silently omitted. -/
def registers (m : Material) (before : Current) (after : FlyCNS.C3Native.State)
    (neuralTicks : Nat) : Array FlyCNS.C3Writer.Register := Id.run do
  let bodies := bodyWords m before after neuralTicks
  let mut body := 0
  let mut result := #[]
  for field in m.writer.fields do
    let name := (field.name.splitOn ".").tail |> String.intercalate "."
    let bytes := if field.name.startsWith "body." then bodies[body]!.bytes
      else if field.name.startsWith "neural." then
        if name=="installation_sha256" then after.neural.installation.bytes
        else integerBytes after.neural.neural[indexOf neuralNames name]! field.width
      else if field.name=="diagnostics.plastic_changes" then signed #[Int64.ofNat after.neural.plasticChanges]
      else if name=="stimulus" then narrow after.pending.sensory
      else if name=="sensory_probabilities" then floats (after.pending.probability.map Float.ofBits)
      else if name=="auxiliary_neurons" then narrow after.pending.auxiliary
      else if name=="auxiliary_uv" then signed after.pending.uv
      else if name=="plastic_rules" then signed after.neural.rules
      else signed after.neural.plastic[indexOf plasticNames name]!
    let shape := if field.varying then #[bytes.size/field.width] else field.shape
    result := result.push ⟨bytes,shape⟩
    if field.name.startsWith "body." then body := body+1
  return result

def writeMicrotickObservation (m : Material) (before : Current) (computed : FlyCNS.C3Native.Result) : FlyCNS.C3Writer.Result :=
  FlyCNS.C3Writer.generate m.writer ⟨registers m before computed.state 1,before.visit,
    "neural",computed.events.fired.size,computed.events.inputCells.size,before.sourceDocument⟩

end FlyCNS.C3Raw
