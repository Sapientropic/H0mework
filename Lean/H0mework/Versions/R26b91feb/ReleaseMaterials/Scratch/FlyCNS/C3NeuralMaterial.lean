import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3IntegerStep

set_option autoImplicit false

namespace FlyCNS.C3Integer
open Lean

structure WordRow where
  name : String
  file : String
  width : Nat
  count : Nat
  sha256 : String
  deriving FromJson

def jsonResult {α : Type} (e : Except String α) : IO α :=
  match e with | .ok a => pure a | .error why => throw (IO.userError why)

def readMaterial (directory : System.FilePath) : IO (Material × State) := do
  let doc ← jsonResult (Json.parse (← IO.FS.readFile (directory/"material.json")))
  let schema : String ← jsonResult (doc.getObjValAs? _ "schema")
  let code : String ← jsonResult (doc.getObjValAs? _ "programme_sha256")
  if schema != "flycns-c3-pure-integer-source-material/v1" ||
      code != "c7b485e855c3018d16284cf8930cc3a862be537a7a62d99f71cd1caa5b445780" then
    throw (IO.userError "integer material is not the original C7 source")
  let rows : Array WordRow ← jsonResult (doc.getObjValAs? _ "constants")
  let mut constants : Std.HashMap String Word := {}
  for row in rows do
    let bytes ← IO.FS.readBinFile (directory/row.file)
    if bytes.size != row.width*row.count then throw (IO.userError "constant word shape differs")
    constants := constants.insert row.name ⟨row.width,bytes⟩
  let parametersJSON ← jsonResult (doc.getObjVal? "parameters")
  let pairs ← jsonResult parametersJSON.getObj?
  let mut parameters : Std.HashMap String I := {}
  for (name,value) in pairs.toArray do
    let n : Int ← jsonResult (fromJson? value)
    parameters := parameters.insert name (Int64.ofInt n)
  let mut slots : Std.HashMap Nat Nat := {}
  let edges := constants["plastic.edges"]!
  for site in [:count edges] do slots := slots.insert (edges.int site).toInt.toNat site
  let stateRows : Array WordRow ← jsonResult (doc.getObjValAs? _ "state")
  let mut neural := Array.replicate 21 (#[] : A)
  let mut plastic := Array.replicate 7 (#[] : A)
  let mut rules : A := #[]
  let mut installation : Word := ⟨256,ByteArray.empty⟩
  for row in stateRows do
    let bytes ← IO.FS.readBinFile (directory/"state"/row.file)
    if bytes.size != row.width*row.count then throw (IO.userError "current word shape differs")
    let word : Word := ⟨row.width,bytes⟩
    if row.name == "neural.8" then
      installation := word
      continue
    let values := (List.range row.count).toArray.map word.int
    if row.name.startsWith "neural." then
      neural := neural.set! (row.name.drop 7).toString.toNat! values
    else if row.name.startsWith "plastic." then
      plastic := plastic.set! (row.name.drop 8).toString.toNat! values
    else rules := values
  let changes : Nat ← jsonResult (doc.getObjValAs? _ "plastic_changes")
  if neural[0]!.size != 165122 || neural[14]!.size != 88905 || neural[19]!.size != 1557 ||
      plastic[0]!.size != 61210 || plastic[1]!.size != 97 || rules.size != 1067 then
    throw (IO.userError "incomplete original NN21/plastic inventory")
  if installation.bytes.size != 256 then throw (IO.userError "missing original neural installation word")
  return (⟨constants,parameters,slots⟩,⟨neural,installation,plastic,rules,changes⟩)

def readPending (directory : System.FilePath) : IO Pending := do
  let cells : Word := ⟨4,← IO.FS.readBinFile (directory/"stimulus.bin")⟩
  let probabilities : Word := ⟨8,← IO.FS.readBinFile (directory/"sensory_probabilities.bin")⟩
  let auxiliary : Word := ⟨4,← IO.FS.readBinFile (directory/"auxiliary_neurons.bin")⟩
  let uv : Word := ⟨8,← IO.FS.readBinFile (directory/"auxiliary_uv.bin")⟩
  if count cells != count probabilities || count auxiliary != count uv then
    throw (IO.userError "pending inventory is incomplete")
  return ⟨(List.range (count cells)).toArray.map fun n => (cells.int n).toInt.toNat,
    (List.range (count cells)).toArray.map probabilities.bits,
    (List.range (count auxiliary)).toArray.map fun n => (auxiliary.int n).toInt.toNat,
    (List.range (count auxiliary)).toArray.map uv.int⟩

def writeInts (file : System.FilePath) (values : A) : IO Unit := do
  let mut bytes := ByteArray.emptyWithCapacity (values.size*8)
  for value in values do
    let bits := value.toUInt64
    for b in [:8] do bytes := bytes.push ((bits >>> UInt64.ofNat (8*b)).toUInt8)
  IO.FS.writeBinFile file bytes

def writeNext (directory : System.FilePath) (next : Next) : IO Unit := do
  IO.FS.createDirAll directory
  for index in [:7] do writeInts (directory/("plastic."++toString index++".bin")) next.state.plastic[index]!
  for (name,values) in [("fired",next.events.fired.map Int64.ofNat),
      ("input_cells",next.events.inputCells.map Int64.ofNat),("input_uv",next.events.inputUV),
      ("graded_cells",next.events.gradedCells.map Int64.ofNat),("graded_fraction",next.events.gradedFraction),
      ("graded_dose",next.events.gradedDose),("terminal_cells",next.events.terminalCells.map Int64.ofNat),
      ("terminal_gain",next.events.terminalGain)] do
    writeInts (directory/(name++".bin")) values
  IO.FS.writeFile (directory/"next.json") (Json.compress (Json.mkObj [
    ("tick",toJson (getA next.state.neural[6]! 0).toInt),
    ("plastic_changes",toJson next.state.plasticChanges)]))

end FlyCNS.C3Integer
