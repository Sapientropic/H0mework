import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceRepresentationIO

/-! The packed image is the sole mutable current input. Fixed readCurrent
reconstructs the private native Current from all decoded original files;
only exact whole-image agreement admits it to the same root.emit. -/

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace PackedRuntimeIO

open RepresentationIO

/-- A packet has only materialized finite data. In particular it cannot
retain an original Current through a Fin-indexed encoder closure. -/
structure Packet where
  words : Vector PackedWordImage 46
  backend : Vector (List WholeRepresentation.Block) 4
  header : List WholeRepresentation.Block

def Packet.image (packet : Packet) : PackedCurrentImage :=
  ⟨packet.words.get, packet.backend.get, packet.header⟩

def freezeImage (image : PackedCurrentImage) : Packet :=
  ⟨Vector.ofFn image.words, Vector.ofFn image.backend, image.header⟩

theorem frozen_image (image : PackedCurrentImage) : (freezeImage image).image = image := by
  cases image with
  | mk words backend header =>
      have word_get : (Vector.ofFn words).get = words := by
        funext field
        exact Vector.getElem_ofFn field.isLt
      have backend_get : (Vector.ofFn backend).get = backend := by
        funext field
        exact Vector.getElem_ofFn field.isLt
      simp only [freezeImage, Packet.image, word_get, backend_get]

def packetCurrent {material : BodyIO.Material} (current : BodyIO.Current material) : Packet :=
  freezeImage (packedCurrent current)

theorem unpack_packetCurrent {material : BodyIO.Material} (current : BodyIO.Current material) :
    unpackImage (packetCurrent current).image = capture current := by
  rw [packetCurrent, frozen_image]
  exact unpack_packImage _

def WordEqual (left right : WordImage) : Prop :=
  left.bytes = right.bytes ∧ left.dataStart = right.dataStart ∧
    left.width = right.width ∧ left.count = right.count

instance (left right : WordImage) : Decidable (WordEqual left right) := by
  unfold WordEqual
  infer_instance

theorem wordEqual_iff (left right : WordImage) : WordEqual left right ↔ left = right := by
  cases left
  cases right
  simp only [WordEqual, WordImage.mk.injEq]

def ImageEqual (left right : CurrentImage) : Prop :=
  (∀ field : Fin 46, WordEqual (left.words field) (right.words field)) ∧
    (∀ field : Fin 4, left.backend field = right.backend field) ∧ left.header = right.header

instance (left right : CurrentImage) : Decidable (ImageEqual left right) := by
  unfold ImageEqual
  infer_instance

theorem imageEqual_iff (left right : CurrentImage) : ImageEqual left right ↔ left = right := by
  constructor
  · rintro ⟨words, backend, header⟩
    have words_eq := funext (fun field => (wordEqual_iff _ _).1 (words field))
    have backend_eq := funext backend
    cases left
    cases right
    simp_all
  · intro identical
    cases identical
    exact ⟨fun _ => (wordEqual_iff _ _).2 rfl, fun _ => rfl, rfl⟩

def writeImage (image : CurrentImage) (directory : System.FilePath) : IO Unit := do
  IO.FS.createDirAll directory
  for field in List.finRange 46 do
    IO.FS.writeBinFile (directory / (toString field.val ++ ".npy")) (image.words field).bytes
  for field in List.finRange 4 do
    IO.FS.writeBinFile (directory / BodyIO.backendNames.get field) (image.backend field)
  IO.FS.writeBinFile (directory / "words.json") image.header

variable (root : BodyIO.IORoot)

structure DecodedAt (packed : Packet) where
  private mk ::
  current : BodyIO.Current root.fixedSource.material
  image_eq : capture current = unpackImage packed.image

/-- No original Current or range/choice witness is supplied. The only native
constructor is the preinstalled source's fixed public parser. -/
def decodePacked (packed : Packet) : IO (DecodedAt root packed) := do
  let nonce ← IO.monoNanosNow
  let directory := root.fixedSource.material.directory / ("packed-input-" ++ toString nonce)
  if (← directory.pathExists) then throw (IO.userError "packed reconstruction directory is not fresh")
  let image := unpackImage packed.image
  writeImage image directory
  let current ← BodyIO.readCurrent root.fixedSource.material directory
  if exact : ImageEqual (capture current) image then
    return ⟨current, (imageEqual_iff _ _).1 exact⟩
  else throw (IO.userError "parsed complete current differs from decoded bytes or descriptors")

theorem decoded_original (original : BodyIO.Current root.fixedSource.material)
    (decoded : DecodedAt root (packetCurrent original)) : decoded.current = original := by
  apply capture_injective
  exact decoded.image_eq.trans (unpack_packetCurrent original)

theorem decoded_reader_identity {Output : Type}
    (reader : BodyIO.Current root.fixedSource.material → Output)
    (original : BodyIO.Current root.fixedSource.material)
    (decoded : DecodedAt root (packetCurrent original)) : reader decoded.current = reader original := by
  rw [decoded_original root original decoded]

structure StepAt (packed : Packet) where
  private mk ::
  decoded : DecodedAt root packed
  generated : BodyIO.GeneratedAt root.fixedSource decoded.current
  next : Packet
  next_image : unpackImage next.image = capture generated.next

def executePacked (packed : Packet) : IO (StepAt root packed) := do
  let decoded ← decodePacked root packed
  let generated ← root.emit decoded.current
  return ⟨decoded, generated, packetCurrent generated.next, unpack_packetCurrent _⟩

theorem step_next_exact {packed : Packet} (step : StepAt root packed) :
    unpackImage step.next.image = capture step.generated.next := step.next_image

theorem step_support_exact {packed : Packet} (step : StepAt root packed) :
    capture step.generated.occurrence.1 = unpackImage packed.image := by
  rw [BodyIO.actual_support]
  exact step.decoded.image_eq

/-- Reconstruction at the next invocation is the previous actual whole
Current, not a merely equivalent reader face. -/
theorem continuation_current {packed : Packet} (first : StepAt root packed)
    (second : StepAt root first.next) : second.decoded.current = first.generated.next := by
  apply capture_injective
  exact second.decoded.image_eq.trans first.next_image

theorem continuation_reader_identity {Output : Type}
    (reader : BodyIO.Current root.fixedSource.material → Output) {packed : Packet}
    (first : StepAt root packed) (second : StepAt root first.next) :
    reader second.decoded.current = reader first.generated.next := by
  rw [continuation_current root first second]

theorem step_original_reader {Output : Type}
    (reader : BodyIO.Current root.fixedSource.material → Output)
    (original : BodyIO.Current root.fixedSource.material)
    (step : StepAt root (packetCurrent original)) :
    reader step.generated.occurrence.1 = reader original := by
  rw [BodyIO.actual_support]
  exact decoded_reader_identity root reader original step.decoded

set_option linter.defProp false in
def step_whole_ledger_next {packed : Packet} (step : StepAt root packed) :=
  And.intro (step_support_exact root step)
    (And.intro (step_next_exact root step)
      (completed_codec_ledger_next root step.generated))

/-- Every iteration discards the previous native execution driver and
reconstructs solely from its packed next with the same fixed source. -/
def advancePacked : Nat → Packet → IO Packet
  | 0, packed => pure packed
  | fuel + 1, packed => do
      let step ← executePacked root packed
      advancePacked fuel step.next

inductive TraceAt : (initial : Packet) → Nat → Type
  | done (packed : Packet) : TraceAt packed 0
  | more {packed : Packet} {fuel : Nat}
      (step : StepAt root packed) (rest : TraceAt step.next fuel) : TraceAt packed (fuel + 1)

def TraceAt.final {packed : Packet} {fuel : Nat} : TraceAt root packed fuel → Packet
  | .done final => final
  | .more _ rest => rest.final

/-- A bounded accounted trace records actual returned replies. It is a
consumer of the packed execution, not material supplied to that execution. -/
def runAccounted : (fuel : Nat) → (packed : Packet) → IO (TraceAt root packed fuel)
  | 0, packed => pure (.done packed)
  | fuel + 1, packed => do
      let step ← executePacked root packed
      let rest ← runAccounted fuel step.next
      return .more step rest

end PackedRuntimeIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
