import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceBodyFullIO
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourcePackedRuntimeIO

/-! Complete materialized packets for the actual ContentSource macro runtime.
The fixed parser reconstructs every installed word, backend, header and visit;
only that decoded current enters the same autonomous root.emit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace BodyFullPackedIO

open BodyFullIO RepresentationIO

structure Image (material : BodyFullIO.Material) where
  words : Vector WordImage material.count
  backend : Vector ByteArray 4
  header : ByteArray
  visit : Nat

def capture {material : BodyFullIO.Material} (current : BodyFullIO.Current material) : Image material :=
  ⟨current.words.map captureWord, current.backend, current.header, current.visit⟩

theorem capture_injective {material : BodyFullIO.Material} :
    Function.Injective (capture (material := material)) := by
  intro left right same
  have words : left.words = right.words := by
    apply Vector.ext
    intro field bound
    have images := congrArg Image.words same
    have image := congrArg (fun images => images[field]) images
    apply captureWord_injective
    simpa only [capture, Vector.getElem_map] using image
  have backend := congrArg Image.backend same
  have header := congrArg Image.header same
  have visit := congrArg Image.visit same
  cases left
  cases right
  simp_all [capture]

structure Packet (material : BodyFullIO.Material) where
  words : Vector PackedWordImage material.count
  backend : Vector (List WholeRepresentation.Block) 4
  header : List WholeRepresentation.Block
  visit : Nat

def unpack {material : BodyFullIO.Material} (packet : Packet material) : Image material :=
  ⟨packet.words.map unpackWord, packet.backend.map unpackBytes, unpackBytes packet.header, packet.visit⟩

def packetCurrent {material : BodyFullIO.Material} (current : BodyFullIO.Current material) : Packet material :=
  ⟨current.words.map (packWord ∘ captureWord), current.backend.map packBytes, packBytes current.header, current.visit⟩

theorem unpack_packetCurrent {material : BodyFullIO.Material} (current : BodyFullIO.Current material) :
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

def ImageEqual {material : BodyFullIO.Material} (left right : Image material) : Prop :=
  (∀ field : Fin material.count, PackedRuntimeIO.WordEqual (left.words.get field) (right.words.get field)) ∧
  left.backend = right.backend ∧ left.header = right.header ∧ left.visit = right.visit

instance {material : BodyFullIO.Material} (left right : Image material) : Decidable (ImageEqual left right) := by
  unfold ImageEqual
  infer_instance

theorem imageEqual_iff {material : BodyFullIO.Material} (left right : Image material) :
    ImageEqual left right ↔ left = right := by
  constructor
  · rintro ⟨words, backend, header, visit⟩
    have words_eq : left.words = right.words := by
      apply Vector.ext
      intro field bound
      exact (PackedRuntimeIO.wordEqual_iff _ _).1 (words ⟨field, bound⟩)
    cases left
    cases right
    simp_all
  · intro same
    cases same
    exact ⟨fun _ => (PackedRuntimeIO.wordEqual_iff _ _).2 rfl, rfl, rfl, rfl⟩

def writeImage {material : BodyFullIO.Material} (image : Image material) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for field in List.finRange material.count do
    IO.FS.writeBinFile (directory / (toString field.val ++ ".npy")) (image.words.get field).bytes
  for field in List.finRange 4 do
    IO.FS.writeBinFile (directory / BodyIO.backendNames.get field) (image.backend.get field)
  IO.FS.writeBinFile (directory / "words.json") image.header

variable (root : BodyFullIO.IORoot)

structure DecodedAt (packet : Packet root.fixedSource.material) where
  private mk ::
  current : BodyFullIO.Current root.fixedSource.material
  image_eq : capture current = unpack packet

def decodePacked (packet : Packet root.fixedSource.material) : IO (DecodedAt root packet) := do
  let nonce ← IO.monoNanosNow
  let directory := root.fixedSource.material.directory / ("packed-input-" ++ toString nonce)
  if (← directory.pathExists) then throw (IO.userError "complete packed input was preinstalled")
  let image := unpack packet
  writeImage image directory
  let current ← BodyFullIO.readCurrent root.fixedSource.material directory
  if exact : ImageEqual (capture current) image then
    return ⟨current, (imageEqual_iff _ _).1 exact⟩
  else throw (IO.userError "decoded full content current differs in bytes, interpretation or root visit")

theorem decoded_original (original : BodyFullIO.Current root.fixedSource.material)
    (decoded : DecodedAt root (packetCurrent original)) : decoded.current = original := by
  apply capture_injective
  exact decoded.image_eq.trans (unpack_packetCurrent original)

structure StepAt (packet : Packet root.fixedSource.material) where
  private mk ::
  decoded : DecodedAt root packet
  generated : BodyFullIO.GeneratedAt root.fixedSource decoded.current
  next : Packet root.fixedSource.material
  next_image : unpack next = capture generated.next

def executePacked (packet : Packet root.fixedSource.material) : IO (StepAt root packet) := do
  let decoded ← decodePacked root packet
  let generated ← root.emit decoded.current
  return ⟨decoded, generated, packetCurrent generated.next, unpack_packetCurrent _⟩

theorem step_next_exact {packet : Packet root.fixedSource.material} (step : StepAt root packet) :
    unpack step.next = capture step.generated.next := step.next_image

theorem step_support_exact {packet : Packet root.fixedSource.material} (step : StepAt root packet) :
    capture step.generated.occurrence.1 = unpack packet := by
  rw [BodyFullIO.actual_support]
  exact step.decoded.image_eq

theorem continuation_current {packet : Packet root.fixedSource.material} (first : StepAt root packet)
    (second : StepAt root first.next) : second.decoded.current = first.generated.next := by
  apply capture_injective
  exact second.decoded.image_eq.trans first.next_image

theorem continuation_every_reader {Output : Type}
    (reader : BodyFullIO.Current root.fixedSource.material → Output)
    {packet : Packet root.fixedSource.material} (first : StepAt root packet) (second : StepAt root first.next) :
    reader second.decoded.current = reader first.generated.next := by
  rw [continuation_current root first second]

set_option linter.defProp false in
def step_whole_ledger_next {packet : Packet root.fixedSource.material} (step : StepAt root packet) :=
  And.intro (step_support_exact root step)
    (And.intro (step_next_exact root step) (BodyFullIO.actual_word_ledger_next root.fixedSource step.generated))

inductive TraceAt : (initial : Packet root.fixedSource.material) → Nat → Type
  | done (packet : Packet root.fixedSource.material) : TraceAt packet 0
  | more {packet : Packet root.fixedSource.material} {fuel : Nat}
      (step : StepAt root packet) (rest : TraceAt step.next fuel) : TraceAt packet (fuel + 1)

def TraceAt.final {packet : Packet root.fixedSource.material} {fuel : Nat} : TraceAt root packet fuel → Packet root.fixedSource.material
  | .done final => final
  | .more _ rest => rest.final

def runAccounted : (fuel : Nat) → (packet : Packet root.fixedSource.material) → IO (TraceAt root packet fuel)
  | 0, packet => pure (.done packet)
  | fuel + 1, packet => do
      let step ← executePacked root packet
      let rest ← runAccounted fuel step.next
      return .more step rest

end BodyFullPackedIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
