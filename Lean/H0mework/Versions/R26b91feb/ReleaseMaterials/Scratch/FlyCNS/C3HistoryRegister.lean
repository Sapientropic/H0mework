import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3DocumentStep
set_option autoImplicit false
namespace FlyCNS.C3History
open FlyCNS.C3Programme

/-- Twelve binary64 words retain every actual odor/stock before/after,
supplied and removed coordinate. Tick is the original material address. -/
structure Record where
  words : Vector UInt64 12
abbrev Slots := Vector (Option Record) 4
def addresses : Vector Int64 4 := ⟨#[0,500,3500,4000],by decide⟩
def empty : Slots := Vector.replicate 4 none
def encode (h : StockEvent) : Except String Record :=
  let values := h.odorBefore++h.odorAfter++h.sugarBefore++h.sugarAfter++h.sugarSupplied++h.sugarRemoved++
    h.waterBefore++h.waterAfter++h.waterSupplied++h.waterRemoved
  if shape : h.odorBefore.size=2 ∧ h.odorAfter.size=2 ∧ h.sugarBefore.size=1 ∧ h.sugarAfter.size=1 ∧
      h.sugarSupplied.size=1 ∧ h.sugarRemoved.size=1 ∧ h.waterBefore.size=1 ∧ h.waterAfter.size=1 ∧
      h.waterSupplied.size=1 ∧ h.waterRemoved.size=1 then
    if size : values.size=12 then .ok ⟨⟨values.map Float.toBits,by simpa using size⟩⟩
    else .error "registered physical stock record lost a coordinate"
  else .error "registered stock history dimensions differ"
def decode (address : Fin 4) (record : Record) : StockEvent :=
  let values := record.words.toArray.map Float.ofBits
  ⟨addresses.get address,values.extract 0 2,values.extract 2 4,values.extract 4 5,
    values.extract 5 6,values.extract 6 7,values.extract 7 8,values.extract 8 9,
    values.extract 9 10,values.extract 10 11,values.extract 11 12⟩
def events (slots : Slots) : Array StockEvent :=
  (List.finRange 4).toArray.filterMap fun i => (slots.get i).map (decode i)
def insert (slots : Slots) (h : StockEvent) : Except String Slots := do
  let slot := (List.finRange 4).find? fun i => addresses.get i==h.tick
  match slot with
  | none => .error "stock history names an unregistered source address"
  | some i =>
    if (slots.get i).isSome then .error "raw environmental input repeated"
    else return slots.set i (some (← encode h))
def capture : List StockEvent → Except String Slots
  | [] => .ok empty
  | h::rest => do
    let slots ← capture rest
    insert slots h

structure Current where
  numerical : FlyCNS.C3Native.State
  history : Slots

/-- The original source apply produces the exchange. Its registered finite
history is written immediately from that event, without a completed tape. -/
def apply (material : Material) (current : Current) : Except String Current := do
  let original ← FlyCNS.C3Programme.apply material ⟨current.numerical,events current.history⟩
  let history ← capture original.environmentHistory.toList
  return ⟨original.numerical,history⟩

theorem events_bounded (slots : Slots) : (events slots).size≤4 := by
  unfold events
  exact Nat.le_trans Array.size_filterMap_le (by simp)

end FlyCNS.C3History
