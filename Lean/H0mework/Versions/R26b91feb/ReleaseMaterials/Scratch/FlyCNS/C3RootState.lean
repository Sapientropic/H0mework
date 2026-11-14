import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3RootSplice
set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3RootState
open ContentReentryIO Lean
abbrev IntegerWord := _root_.FlyCNS.C3Integer.Word
def word (source : ContentReentryIO.Source) (current : Current source.material) (name : String) : Except String IntegerWord := do
  let field := (List.finRange 59).find? fun i => (source.material.layout.get i).name==name
  match field with
  | none => .error ("original source omits named coordinate: "++name)
  | some i =>
    let value := current.words.get i
    return ⟨value.vector.width,value.bytes.extract value.vector.dataStart value.bytes.size⟩
def integers (w : IntegerWord) : Array Int64 :=
  (List.range (_root_.FlyCNS.C3Integer.count w)).toArray.map w.int
def floats (w : IntegerWord) : Array Float :=
  (List.range (_root_.FlyCNS.C3Integer.count w)).toArray.map fun i => Float.ofBits (w.bits i)
def nodes (w : IntegerWord) : Array Nat :=
  (integers w).map fun i => i.toInt.toNat

/-- Every NN21/PL/body/pending coordinate comes from the original admitted
Current. Backend JSON carries its source-owned history; no after enters. -/
def decode (source : ContentReentryIO.Source) (current : Current source.material) :
    Except String _root_.FlyCNS.C3Successful.Current := do
  let mut ns := #[]
  for name in _root_.FlyCNS.C3Raw.neuralNames do ns:=ns.push (integers (← word source current ("neural."++name)))
  let installation ← word source current "neural.installation_sha256"
  let mut ps := #[]
  for name in _root_.FlyCNS.C3Raw.plasticNames do ps:=ps.push (integers (← word source current ("source."++name)))
  let rules := integers (← word source current "source.plastic_rules")
  let changes := (← word source current "diagnostics.plastic_changes").bits 0 |>.toNat
  let nn : _root_.FlyCNS.C3Integer.State := ⟨ns,installation,ps,rules,changes⟩
  let sensory := nodes (← word source current "source.stimulus")
  let probabilities := (List.range sensory.size).toArray.map (← word source current "source.sensory_probabilities").bits
  let pending : _root_.FlyCNS.C3Integer.Pending := ⟨sensory,probabilities,nodes (← word source current "source.auxiliary_neurons"),
    integers (← word source current "source.auxiliary_uv")⟩
  let mut bodies := #[]
  for name in _root_.FlyCNS.C3Registered.bodyNames do bodies:=bodies.push (← word source current ("body."++name))
  if count : bodies.size=25 then
    let get := fun i => floats bodies[i]!
    let integration := get 1
    let physical : _root_.FlyCNS.C3Physical.State := ⟨integration.extract 1 76,integration.extract 76 150,
      integration.extract 150 224,integration.extract 274 348,integration.extract 224 274,integration[0]!⟩
    let signal : _root_.FlyCNS.C3BodySignal.State := ⟨get 11,get 12,(get 13)[0]!,get 24,
      bodies[21]!.bits 0 != 0,bodies[22]!.bits 0 != 0⟩
    let oscillator : _root_.FlyCNS.C3CPG.State := ⟨get 2,get 3,get 4,get 5⟩
    let gait : _root_.FlyCNS.C3Gait.State := ⟨oscillator,get 6,get 7,integers bodies[8]!⟩
    let resource : _root_.FlyCNS.C3Resource.State := ⟨get 14,get 15,get 16,get 18,bodies[23]!.bits 0 != 0⟩
    let numerical : _root_.FlyCNS.C3Native.State := ⟨nn,pending,⟨physical,signal,gait,resource,get 17⟩⟩
    let document := current.backend.get ⟨3,by decide⟩
    let text ← match String.fromUTF8? document with | some text => pure text | none => .error "source JSON is not UTF8"
    let json ← Json.parse text
    let historyJson ← json.getObjVal? "environment_input_history"
    let historyRows ← historyJson.getArr?
    let mut events := #[]
    for h in historyRows do
      let tick : Int ← h.getObjValAs? _ "tick"
      let sugar ← h.getObjVal? "sugar_stock";let water ← h.getObjVal? "water_stock"
      let e : _root_.FlyCNS.C3Programme.StockEvent := ⟨Int64.ofInt tick,← h.getObjValAs? _ "odor_before",← h.getObjValAs? _ "odor_after",
        ← sugar.getObjValAs? _ "before",← sugar.getObjValAs? _ "after",← sugar.getObjValAs? _ "supplied",← sugar.getObjValAs? _ "removed",
        ← water.getObjValAs? _ "before",← water.getObjValAs? _ "after",← water.getObjValAs? _ "supplied",← water.getObjValAs? _ "removed"⟩
      events:=events.push e
    let history ← _root_.FlyCNS.C3History.capture events.toList
    return ⟨⟨⟨numerical,events⟩,⟨bodies,count⟩,document,current.visit⟩,history⟩
  else .error "original complete body inventory changed"

end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS.C3RootState
