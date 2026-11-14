import Lean
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3IntegerStep

set_option autoImplicit false
namespace FlyCNS.C3Writer
open Lean

structure Field where
  name : String
  dtype : String
  width : Nat
  shape : Array Nat
  varying : Bool
  deriving FromJson, ToJson, Inhabited

structure Material where
  schema : String
  instance_id : String
  occurrence_id : String
  installation_sha256 : String
  fields : Array Field
  archives : Array (Array String)
  deriving FromJson

structure Register where
  bytes : ByteArray
  shape : Array Nat
  deriving Inhabited

structure Frame where
  registers : Array Register
  beforeVisit : Nat
  operation : String
  spikes : Nat
  inputs : Nat
  sourceDocument : ByteArray

structure Result where
  words : Array ByteArray
  header : ByteArray
  visit : Nat
  sourceDocument : ByteArray
  archives : Array ByteArray

def product (shape : Array Nat) : Nat := shape.foldl (·*·) 1
def spaces (n : Nat) : String := String.ofList (List.replicate n ' ')
def little (n width : Nat) : ByteArray := Id.run do
  let mut result := ByteArray.empty
  for i in [:width] do result := result.push (UInt8.ofNat (n/2^(8*i)%256))
  return result

def crcTable : Array UInt32 := (List.range 256).toArray.map fun n => Id.run do
  let mut crc := UInt32.ofNat n
  for _ in [:8] do crc := if crc &&& 1 == 1 then (crc >>> 1) ^^^ 0xEDB88320 else crc >>> 1
  return crc
def crc32 (bytes : ByteArray) : Nat := Id.run do
  let mut crc : UInt32 := 0xFFFFFFFF
  for i in [:bytes.size] do
    crc := (crc >>> 8) ^^^ crcTable[((crc ^^^ (bytes.get! i).toUInt32) &&& 255).toNat]!
  return (crc ^^^ 0xFFFFFFFF).toNat

/-- Original ZIP_STORED / forced ZIP64 local records. CRC, sizes and offsets
are generated from the newly serialized numeric members. -/
def archive (members : Array (String × ByteArray)) : ByteArray := Id.run do
  let mut payload := ByteArray.empty
  let mut directory := ByteArray.empty
  for (name,bytes) in members do
    let file := (name++".npy").toUTF8
    let crc := crc32 bytes
    let offset := payload.size
    let extra := little 1 2++little 16 2++little bytes.size 8++little bytes.size 8
    let localHeader := little 0x04034B50 4++little 45 2++little 0 2++little 0 2++little 0 2++little 33 2++
      little crc 4++little 0xFFFFFFFF 4++little 0xFFFFFFFF 4++little file.size 2++little extra.size 2++file++extra
    payload := payload++localHeader++bytes
    directory := directory++little 0x02014B50 4++little 813 2++little 45 2++little 0 2++little 0 2++
      little 0 2++little 33 2++little crc 4++little bytes.size 4++little bytes.size 4++little file.size 2++
      little 0 2++little 0 2++little 0 2++little 0 2++little 25165824 4++little offset 4++file
  let ending := little 0x06054B50 4++little 0 2++little 0 2++little members.size 2++little members.size 2++
    little directory.size 4++little payload.size 4++little 0 2
  return payload++directory++ending

/-- Original NumPy 2.4.6 version-1 numeric NPY header, including its growth
padding and 64-byte alignment. The payload is an actual typed source register. -/
def npy (dtype : String) (shape : Array Nat) (payload : ByteArray) : ByteArray :=
  let dimensions := String.intercalate ", " (shape.toList.map toString)
  let tuple := if shape.isEmpty then "()" else "("++dimensions++(if shape.size==1 then ",)" else ")")
  let text := "{'descr': '"++dtype++"', 'fortran_order': False, 'shape': "++tuple++", }"
  let grown := text++spaces (if shape.isEmpty then 0 else 21-(toString shape[0]!).length)
  let size := grown.utf8ByteSize+1
  let padding := 64-((10+size)%64)
  let header := (grown++spaces padding++"\n").toUTF8
  let magic : ByteArray := ⟨#[147,78,85,77,80,89,1,0]⟩
  magic++little header.size 2++header++payload

def fieldJson (field : Field) (register : Register) : Json :=
  Json.mkObj [("count",toJson (product register.shape)),("dtype",toJson field.dtype),
    ("name",toJson field.name),("shape",toJson register.shape),("varying",toJson field.varying),("width",toJson field.width)]

def namedBits (m : Material) (f : Frame) (name : String) : Nat := Id.run do
  for i in [:m.fields.size] do
    if m.fields[i]!.name==name then
      return (FlyCNS.C3Integer.Word.bits ⟨m.fields[i]!.width,f.registers[i]!.bytes⟩ 0).toNat
  return 0

/-- Update the source-owned integer while retaining all original current
material/context bytes. No future JSON is supplied. -/
def sourceDocument (current : ByteArray) (changes : Nat) : ByteArray := Id.run do
  let marker := "\"diagnostics\":{\"plastic_changes\":".toUTF8
  let mut start : Option Nat := none
  for i in [:current.size] do
    if i+marker.size <= current.size && current.extract i (i+marker.size) == marker then
      start := some (i+marker.size)
      break
  match start with
  | none => return current
  | some first =>
      let mut last := first
      for i in [first:current.size] do
        let b := current.get! i
        if b < 48 || b > 57 then break
        last := i+1
      return current.extract 0 first++(toString changes).toUTF8++current.extract last current.size

/-- Complete numeric coordinates and header are produced from material,
registers and the current visit; neither next NPY nor next JSON is input. -/
def generate (m : Material) (f : Frame) : Result :=
  let fields := (List.range m.fields.size).toArray.map fun i => fieldJson m.fields[i]! f.registers[i]!
  let words := (List.range m.fields.size).toArray.map fun i =>
    npy m.fields[i]!.dtype #[product f.registers[i]!.shape] f.registers[i]!.bytes
  let visit := f.beforeVisit+1
  let header := Json.mkObj [("body_tick",toJson (namedBits m f "body.tick")),("fields",.arr fields),
    ("generated_inputs",toJson f.inputs),("generated_spikes",toJson f.spikes),
    ("installation_sha256",toJson m.installation_sha256),("instance_id",toJson m.instance_id),
    ("occurrence_id",toJson m.occurrence_id),("operation",toJson f.operation),
    ("physics_tick",toJson (namedBits m f "body.physics_ticks")),("root_visit",toJson visit),
    ("schema",toJson m.schema),("tick",toJson (namedBits m f "neural.tick"))]
  let archives := m.archives.map fun names => archive (names.map fun name => Id.run do
    for i in [:m.fields.size] do
      if m.fields[i]!.name == name then
        let member := (name.splitOn ".").tail |> String.intercalate "."
        return (member,npy m.fields[i]!.dtype f.registers[i]!.shape f.registers[i]!.bytes)
    return (name,ByteArray.empty))
  ⟨words,header.compress.toUTF8,visit,
    sourceDocument f.sourceDocument (namedBits m f "diagnostics.plastic_changes"),archives⟩

end FlyCNS.C3Writer
