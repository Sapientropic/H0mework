import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.ContentFullRoot
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourcePackedRuntimeIO

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace ContentFullPackedIO

open ContentFullIO ContentFullRoot RepresentationIO

local instance : DecidableEq WordImage := fun left right =>
  decidable_of_iff (PackedRuntimeIO.WordEqual left right) (PackedRuntimeIO.wordEqual_iff left right)

structure Image where
  words : Vector WordImage 59
  backend : Vector ByteArray 4
  header : ByteArray
  visit : Nat
  deriving DecidableEq
def capture {material : Material} (current : Current material) : Image :=
  ⟨current.words.map captureWord, current.backend, current.header, current.visit⟩
theorem capture_injective {material : Material} : Function.Injective (capture (material := material)) := by
  intro left right same
  have words : left.words = right.words := by
    apply Vector.ext
    intro field bound
    have image := congrArg (fun images => images[field]) (congrArg Image.words same)
    apply captureWord_injective
    simpa only [capture, Vector.getElem_map] using image
  have backend := congrArg Image.backend same
  have header := congrArg Image.header same
  have visit := congrArg Image.visit same
  cases left
  cases right
  simp_all [capture]

structure Packet where
  words : Vector PackedWordImage 59
  backend : Vector (List WholeRepresentation.Block) 4
  header : List WholeRepresentation.Block
  visit : Nat
def unpack (packet : Packet) : Image :=
  ⟨packet.words.map unpackWord, packet.backend.map unpackBytes, unpackBytes packet.header, packet.visit⟩
def packetCurrent {material : Material} (current : Current material) : Packet :=
  ⟨current.words.map (packWord ∘ captureWord), current.backend.map packBytes, packBytes current.header, current.visit⟩
theorem unpack_packetCurrent {material : Material} (current : Current material) :
    unpack (packetCurrent current) = capture current := by
  have words : (current.words.map (packWord ∘ captureWord)).map unpackWord = current.words.map captureWord := by
    apply Vector.ext
    intro field bound
    simp only [Vector.getElem_map, Function.comp_apply, unpack_packWord]
  have backend : (current.backend.map packBytes).map unpackBytes = current.backend := by
    apply Vector.ext
    intro field bound
    simp only [Vector.getElem_map, unpack_packBytes]
  simp only [unpack, packetCurrent, capture, words, backend, unpack_packBytes]

def writeImage (image : Image) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for field in List.finRange 59 do
    IO.FS.writeBinFile (directory / (toString field.val ++ ".npy")) (image.words.get field).bytes
  for field in List.finRange 4 do
    IO.FS.writeBinFile (directory / BodyIO.backendNames.get field) (image.backend.get field)
  IO.FS.writeBinFile (directory / "words.json") image.header

variable (source : ContentFullIO.Source)
structure DecodedAt (packet : Packet) where
  private mk ::
  current : Current source.material
  exact : capture current = unpack packet
def decode (packet : Packet) : IO (DecodedAt source packet) := do
  let nonce ← IO.monoNanosNow
  let path := source.material.directory / ("packed-input-" ++ toString nonce)
  if (← path.pathExists) then throw (IO.userError "the decoded content input was preinstalled")
  writeImage (unpack packet) path
  let current ← readCurrent source.material path
  if exact : capture current = unpack packet then return ⟨current, exact⟩
  else throw (IO.userError "the packet changes a content coordinate, interpretation or root visit")

structure StepAt (packet : Packet) where
  private mk ::
  decoded : DecodedAt source packet
  generated : GeneratedAt source decoded.current
  next : Packet
  exact : unpack next = capture generated.next
def execute (packet : Packet) : IO (StepAt source packet) := do
  let decoded ← decode source packet
  let generated ← emit source decoded.current
  return ⟨decoded, generated, packetCurrent generated.next, unpack_packetCurrent _⟩

theorem decoded_original (original : Current source.material) (decoded : DecodedAt source (packetCurrent original)) :
    decoded.current = original := capture_injective (decoded.exact.trans (unpack_packetCurrent original))
theorem continuation_current {packet : Packet} (first : StepAt source packet) (second : StepAt source first.next) :
    second.decoded.current = first.generated.next := capture_injective (second.decoded.exact.trans first.exact)
theorem continuation_every_reader {Output : Type} (reader : Current source.material → Output)
    {packet : Packet} (first : StepAt source packet) (second : StepAt source first.next) :
    reader second.decoded.current = reader first.generated.next := by rw [continuation_current source first second]

inductive TraceAt : Packet → Nat → Type
  | done (packet : Packet) : TraceAt packet 0
  | more {packet : Packet} {fuel : Nat} (step : StepAt source packet)
      (rest : TraceAt step.next fuel) : TraceAt packet (fuel + 1)
def runAccounted : (fuel : Nat) → (packet : Packet) → IO (TraceAt source packet fuel)
  | 0, packet => pure (.done packet)
  | fuel + 1, packet => do
      let step ← execute source packet
      return .more step (← runAccounted fuel step.next)

end ContentFullPackedIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
