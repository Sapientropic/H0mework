import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3RawInventory
set_option autoImplicit false
namespace FlyCNS.C3Registered
open Lean FlyCNS.C3Integer
inductive Kind where
  | neural (index : Fin 21)
  | body (index : Fin 25)
  | source (index : Fin 12)
  | diagnostic

def bodyNames : Array String := #["installation_sha256","integration","controller_phases","controller_magnitudes",
  "controller_intrinsic_freqs","controller_intrinsic_amps","controller_retraction","controller_stumbling","controller_persistence",
  "controller_random_keys","controller_random_meta","motor_trace","descending_trace","feeding_trace","world_values",
  "sugar_stock","water_stock","odor_gain","peptide_concentrations","tick","physics_ticks","controller_enabled",
  "feeding_enabled","peptide_enabled","steering_trace"]
def sourceNames : Array String := #["stimulus","sensory_probabilities","auxiliary_neurons","auxiliary_uv",
  "plastic_eligibility_q","plastic_dopamine_q","plastic_labile_q","plastic_stable_q","plastic_delta_uv",
  "plastic_last_update_tick","plastic_modulation_scratch_q","plastic_rules"]
def kind (field : Fin 59) : Kind :=
  if h : field.val < 21 then .neural ⟨field.val,h⟩
  else if h' : field.val < 46 then .body ⟨field.val-21,by omega⟩
  else if h'' : field.val < 58 then .source ⟨field.val-46,by omega⟩
  else .diagnostic
def name : Kind → String
  | .neural i => "neural."++FlyCNS.C3Raw.neuralNames[i.val]!
  | .body i => "body."++bodyNames[i.val]!
  | .source i => "source."++sourceNames[i.val]!
  | .diagnostic => "diagnostics.plastic_changes"
def expectedNames : Vector String 59 := Vector.ofFn fun field => name (kind field)

def dtypeWidth : Kind → String × Nat
  | .neural i => if i.val==8 then ("<U64",256)
      else if i.val==2 || i.val==3 || i.val==4 then ("<i4",4)
      else if i.val==7 then ("<u8",8) else ("<i8",8)
  | .body i => if i.val==0 then ("<U64",256)
      else if i.val==9 then ("<u4",4)
      else if i.val==21 || i.val==22 || i.val==23 then ("|b1",1)
      else if i.val==8 || i.val==19 || i.val==20 then ("<i8",8) else ("<f8",8)
  | .source i => if i.val==0 || i.val==2 then ("<i4",4)
      else if i.val==1 then ("<f8",8) else ("<i8",8)
  | .diagnostic => ("<i8",8)
def initialShape : Kind → Array Nat
  | .neural i =>
      if i.val==3 then #[2,165122] else if i.val==4 then #[2]
      else if i.val==5 || i.val==6 || i.val==7 || i.val==8 then #[]
      else if 14≤i.val && i.val<19 then #[88905]
      else if 19≤i.val then #[1557] else #[165122]
  | .body i =>
      if i.val==1 then #[762]
      else if (2≤i.val && i.val≤8) then #[6]
      else if i.val==9 then #[624]
      else if i.val==10 || i.val==18 then #[3]
      else if i.val==11 || i.val==12 || i.val==17 then #[2]
      else if i.val==14 then #[8]
      else if i.val==15 || i.val==16 then #[1]
      else if i.val==24 then #[4] else #[]
  | .source i =>
      if i.val<4 then #[0]
      else if i.val==5 || i.val==10 then #[97]
      else if i.val==11 then #[97,11] else #[61210]
  | .diagnostic => #[]
def descriptor (field : Fin 59) : FlyCNS.C3Writer.Field :=
  let k := kind field
  let (dtype,width) := dtypeWidth k
  ⟨name k,dtype,width,initialShape k,46≤field.val && field.val<50⟩
def SourceLayout (layout : Vector FlyCNS.C3Writer.Field 59) : Prop :=
  ∀ i : Fin 59, (layout.get i).dtype=(descriptor i).dtype ∧
    (layout.get i).width=(descriptor i).width ∧ (layout.get i).shape=(descriptor i).shape ∧
    (layout.get i).varying=(descriptor i).varying
instance (layout : Vector FlyCNS.C3Writer.Field 59) : Decidable (SourceLayout layout) := by
  unfold SourceLayout
  infer_instance

/-- A source parser constructs this table from actual descriptors. Complete
name/unique/role admission precedes any registered pure operation. -/
structure Material where
  writer : FlyCNS.C3Writer.Material
  layout : Vector FlyCNS.C3Writer.Field 59
  same_layout : layout.toArray = writer.fields
  names : ∀ field : Fin 59,(layout.get field).name = expectedNames.get field
  unique : ∀ a b : Fin 59,(layout.get a).name=(layout.get b).name → a=b
  original_layout : SourceLayout layout

def admit (writer : FlyCNS.C3Writer.Material) : Except String Material :=
  if count : writer.fields.size=59 then
    let layout : Vector FlyCNS.C3Writer.Field 59 := ⟨writer.fields,count⟩
    if names : ∀ field : Fin 59,(layout.get field).name=expectedNames.get field then
      if unique : ∀ a b : Fin 59,(layout.get a).name=(layout.get b).name → a=b then
        if original : SourceLayout layout then .ok ⟨writer,layout,rfl,names,unique,original⟩
        else .error "source catalogue changed original field interpretation or dimensions"
      else .error "source catalogue aliases an original field"
    else .error "source catalogue changed a named original coordinate"
  else .error "source catalogue is not complete59"

def payload (after : FlyCNS.C3Native.State) (bodies : Vector Word 25)
    (field : FlyCNS.C3Writer.Field) : Kind → ByteArray
  | .neural i => if i.val==8 then after.neural.installation.bytes
    else FlyCNS.C3Raw.integerBytes after.neural.neural[i.val]! field.width
  | .body i => (bodies.get i).bytes
  | .diagnostic => FlyCNS.C3Raw.signed #[Int64.ofNat after.neural.plasticChanges]
  | .source i =>
    if i.val==0 then FlyCNS.C3Raw.narrow after.pending.sensory
    else if i.val==1 then FlyCNS.C3Raw.floats (after.pending.probability.map Float.ofBits)
    else if i.val==2 then FlyCNS.C3Raw.narrow after.pending.auxiliary
    else if i.val==3 then FlyCNS.C3Raw.signed after.pending.uv
    else if i.val==11 then FlyCNS.C3Raw.signed after.neural.rules
    else FlyCNS.C3Raw.signed after.neural.plastic[i.val-4]!

/-- Body updates use original ordinal ports after exact catalogue admission;
there is no string lookup and no unknown-name fallthrough. Static ordinals
are installation, RNG keys/meta and the two unchanged body flags. -/
def generatedBodies (before : Vector Word 25) (after : FlyCNS.C3Native.State) (ticks : Nat) : Vector Word 25 :=
  Vector.ofFn fun i =>
    let b := after.body
    let p := b.physics
    let floatWord := fun a : Array Float => Word.mk 8 (FlyCNS.C3Raw.floats a)
    match i.val with
    | 1 =>
      let old := (before.get ⟨1,by decide⟩).bytes
      ⟨8,FlyCNS.C3Raw.floats (#[p.time]++p.position++p.velocity++p.warmstart++p.control++p.applied)++old.extract (8*348) old.size⟩
    | 2 => floatWord b.gait.oscillator.phases
    | 3 => floatWord b.gait.oscillator.magnitudes
    | 4 => floatWord b.gait.oscillator.frequencies
    | 5 => floatWord b.gait.oscillator.amplitudes
    | 6 => floatWord b.gait.retraction
    | 7 => floatWord b.gait.stumbling
    | 8 => ⟨8,FlyCNS.C3Raw.signed b.gait.persistence⟩
    | 11 => floatWord b.signal.motor
    | 12 => floatWord b.signal.descending
    | 13 => floatWord #[b.signal.feeding]
    | 14 => floatWord b.resource.values
    | 15 => floatWord b.resource.sugar
    | 16 => floatWord b.resource.water
    | 17 => floatWord b.odorGains
    | 18 => floatWord b.resource.peptide
    | 19 => ⟨8,FlyCNS.C3Raw.signed #[(before.get ⟨19,by decide⟩).int 0+Int64.ofNat ticks]⟩
    | 20 => ⟨8,FlyCNS.C3Raw.signed #[(before.get ⟨20,by decide⟩).int 0+Int64.ofNat (10*ticks)]⟩
    | 21 => ⟨1,⟨#[if b.signal.controllerEnabled then 1 else 0]⟩⟩
    | 24 => floatWord b.signal.steering
    | _ => before.get i

def registers (m : Material) (after : FlyCNS.C3Native.State) (bodies : Vector Word 25) :
    Vector FlyCNS.C3Writer.Register 59 := Vector.ofFn fun i =>
  let field := m.layout.get i
  let bytes := payload after bodies field (kind i)
  ⟨bytes,if field.varying then #[bytes.size/field.width] else field.shape⟩

theorem complete_name (m : Material) (field : Fin 59) :
    (m.layout.get field).name=name (kind field) := by
  simpa [expectedNames,Vector.get,Fin.cast] using m.names field
theorem no_name_alias (m : Material) (a b : Fin 59)
    (same : (m.layout.get a).name=(m.layout.get b).name) : a=b := m.unique a b same

end FlyCNS.C3Registered
