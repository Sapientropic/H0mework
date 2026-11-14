import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3DecimalStep
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3ProgrammeKernel
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3WriterStep
set_option autoImplicit false
namespace FlyCNS.C3Document

def numbers (values : Array Float) : String :=
  "["++String.intercalate "," (values.toList.map fun x => FlyCNS.C3Decimal.encode x.toBits)++"]"
def stock (before after supplied removed : Array Float) : String :=
  "{\"after\":"++numbers after++",\"before\":"++numbers before++",\"removed\":"++numbers removed++
    ",\"supplied\":"++numbers supplied++"}"
def event (h : FlyCNS.C3Programme.StockEvent) : String :=
  "{\"odor_after\":"++numbers h.odorAfter++",\"odor_before\":"++numbers h.odorBefore++
    ",\"sugar_stock\":"++stock h.sugarBefore h.sugarAfter h.sugarSupplied h.sugarRemoved++
    ",\"tick\":"++toString h.tick.toInt++",\"water_stock\":"++
      stock h.waterBefore h.waterAfter h.waterSupplied h.waterRemoved++"}"
def history (values : Array FlyCNS.C3Programme.StockEvent) : ByteArray :=
  ("["++String.intercalate "," (values.toList.map event)++"]").toUTF8

/-- Only the source-generated environment member changes. The complete
original source material, identities, lineage and context remain literal. -/
def replaceHistory (before : ByteArray) (generated : ByteArray) : Except String ByteArray := Id.run do
  let marker := "\"environment_input_history\":".toUTF8
  let mut start : Option Nat := none
  for i in [:before.size] do
    if before.extract i (i+marker.size)==marker then
      start:=some (i+marker.size)
      break
  match start with
  | none => return .error "the complete source omits its registered environment history"
  | some first =>
    let mut depth : Nat := 0
    let mut quoted := false
    let mut escaped := false
    let mut finish : Option Nat := none
    for i in [first:before.size] do
      let c := before.get! i
      if quoted then
        if escaped then escaped:=false
        else if c==92 then escaped:=true
        else if c==34 then quoted:=false
      else if c==34 then quoted:=true
      else if c==91 then depth:=depth+1
      else if c==93 then
        if depth==0 then return .error "the source environment history has an unmatched bracket"
        depth:=depth-1
        if depth==0 then
          finish:=some (i+1)
          break
    match finish with
    | none => return .error "the source environment history is incomplete"
    | some last => return .ok (before.extract 0 first++generated++before.extract last before.size)

def generate (before : ByteArray) (events : Array FlyCNS.C3Programme.StockEvent) (changes : Nat) : Except String ByteArray := do
  let values := events.flatMap fun h => h.odorBefore++h.odorAfter++h.sugarBefore++h.sugarAfter++
    h.sugarSupplied++h.sugarRemoved++h.waterBefore++h.waterAfter++h.waterSupplied++h.waterRemoved
  if values.any (fun x => x.toBits.toNat/2^52%2048 == 2047) then
    throw "Out of range float values are not JSON compliant"
  let updated ← replaceHistory before (history events)
  return FlyCNS.C3Writer.sourceDocument updated changes

end FlyCNS.C3Document
