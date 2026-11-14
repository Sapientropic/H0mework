import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceBodyIO
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceRepresentation

set_option autoImplicit false

open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace RepresentationIO

universe u v

/-- Standard EST laws keep the same success/error and world token. No
foreign action is evaluated or replaced by a pure value. -/
local instance lawfulEST (ε σ : Type) : LawfulMonad (EST ε σ) := .mk'
  (id_map := fun effect => funext fun world => by
    change (match effect world with
      | .ok value next => .ok value next
      | .error error next => .error error next) = effect world
    cases effect world <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun effect _ _ => funext fun world => by
    simp only [bind, EST.bind]
    cases effect world <;> rfl)

local instance lawfulIO : LawfulMonad IO := lawfulEST IO.Error IO.RealWorld

structure Codec (Raw Packed : Type u) where
  encode : Raw → Packed
  decode : Packed → Raw
  decode_encode : Function.LeftInverse decode encode

namespace Codec

variable {Raw Packed : Type u} (codec : Codec Raw Packed)
variable {m : Type u → Type v} [Monad m] [LawfulMonad m]

theorem map_decode_encode (effect : m Raw) : codec.decode <$> (codec.encode <$> effect) = effect := by
  rw [Functor.map_map]
  change (codec.decode ∘ codec.encode) <$> effect = effect
  have identical : codec.decode ∘ codec.encode = id := funext codec.decode_encode
  rw [identical, id_map]

def liftEffect (action : Raw → m Raw) (packed : Packed) : m Packed :=
  codec.encode <$> action (codec.decode packed)

omit [LawfulMonad m] in
theorem liftEffect_source (action : Raw → m Raw) (state : Raw) :
    codec.liftEffect action (codec.encode state) = codec.encode <$> action state := by
  unfold liftEffect
  rw [codec.decode_encode state]

theorem decoded_liftEffect_source (action : Raw → m Raw) (state : Raw) :
    codec.decode <$> codec.liftEffect action (codec.encode state) = action state := by
  rw [liftEffect_source, map_decode_encode]

end Codec

def runEffect {I State : Type u} {m : Type u → Type v} [Monad m]
    (actions : I → State → m State) : List I → State → m State
  | [], state => pure state
  | letter :: rest, state => actions letter state >>= runEffect actions rest

theorem effect_words_conjugate {I Raw Packed : Type u} {m : Type u → Type v}
    [Monad m] [LawfulMonad m] (codec : Codec Raw Packed)
    (actions : I → Raw → m Raw) (word : List I) (state : Raw) :
    runEffect (fun letter => codec.liftEffect (actions letter)) word (codec.encode state) =
      codec.encode <$> runEffect actions word state := by
  induction word generalizing state with
  | nil => simp [runEffect]
  | cons letter rest previous =>
      simp only [runEffect, Codec.liftEffect_source, bind_map_left, map_bind]
      congr 1
      funext next
      exact previous next

theorem decoded_effect_words {I Raw Packed : Type u} {m : Type u → Type v}
    [Monad m] [LawfulMonad m] (codec : Codec Raw Packed)
    (actions : I → Raw → m Raw) (word : List I) (state : Raw) :
    codec.decode <$> runEffect (fun letter => codec.liftEffect (actions letter)) word (codec.encode state) =
      runEffect actions word state := by
  rw [effect_words_conjugate, codec.map_decode_encode]

open WholeRepresentation

def byteList (bytes : ByteArray) : List Byte := bytes.data.toList.map UInt8.toFin
def byteArray (bytes : List Byte) : ByteArray := ⟨(bytes.map UInt8.ofFin).toArray⟩

theorem byteArray_byteList (bytes : ByteArray) : byteArray (byteList bytes) = bytes := by
  cases bytes with
  | mk data =>
      change ByteArray.mk (((data.toList.map UInt8.toFin).map UInt8.ofFin).toArray) = ByteArray.mk data
      rw [List.map_map]
      have identity : UInt8.ofFin ∘ UInt8.toFin = id := by
        funext value
        cases value
        rfl
      simp [identity]

def packBytes (bytes : ByteArray) : List Block := packAux (byteList bytes).length (byteList bytes)
def unpackBytes (blocks : List Block) : ByteArray := byteArray (unpack blocks)

theorem unpack_packBytes (bytes : ByteArray) : unpackBytes (packBytes bytes) = bytes := by
  rw [unpackBytes, packBytes, unpack_packAux, byteArray_byteList]

structure WordImage where
  bytes : ByteArray
  dataStart : Nat
  width : Nat
  count : Nat

structure PackedWordImage where
  blocks : List Block
  dataStart : Nat
  width : Nat
  count : Nat

def captureWord (word : BodyIO.Word) : WordImage :=
  ⟨word.bytes, word.vector.dataStart, word.vector.width, word.vector.count⟩

theorem captureWord_injective : Function.Injective captureWord := by
  intro left right same
  cases left
  cases right
  rename_i leftBytes leftVector rightBytes rightVector
  cases leftVector
  cases rightVector
  simp only [captureWord, WordImage.mk.injEq] at same
  rcases same with ⟨sameBytes, sameStart, sameWidth, sameCount⟩
  cases sameBytes
  cases sameStart
  cases sameWidth
  cases sameCount
  rfl

def packWord (image : WordImage) : PackedWordImage :=
  ⟨packBytes image.bytes, image.dataStart, image.width, image.count⟩

def unpackWord (image : PackedWordImage) : WordImage :=
  ⟨unpackBytes image.blocks, image.dataStart, image.width, image.count⟩

theorem unpack_packWord (image : WordImage) : unpackWord (packWord image) = image := by
  cases image
  simp only [packWord, unpackWord, unpack_packBytes]

/-- Every material field of Current is present. Parsing descriptors are
retained too, so equality cannot drop a typed consumer of Word.vector. -/
structure CurrentImage where
  words : Fin 46 → WordImage
  backend : Fin 4 → ByteArray
  header : ByteArray

structure PackedCurrentImage where
  words : Fin 46 → PackedWordImage
  backend : Fin 4 → List Block
  header : List Block

def capture {material : BodyIO.Material} (current : BodyIO.Current material) : CurrentImage :=
  ⟨fun field => captureWord (current.words.get field), current.backend.get, current.header⟩

theorem capture_injective {material : BodyIO.Material} :
    Function.Injective (capture (material := material)) := by
  intro left right same
  have words : left.words = right.words := by
    apply Vector.ext
    intro field withinLeft
    exact captureWord_injective (congrFun (congrArg CurrentImage.words same) ⟨field, withinLeft⟩)
  have backend : left.backend = right.backend := by
    apply Vector.ext
    intro field withinLeft
    exact congrFun (congrArg CurrentImage.backend same) ⟨field, withinLeft⟩
  have header : left.header = right.header := congrArg CurrentImage.header same
  cases left
  cases right
  simp_all [capture]

def packImage (image : CurrentImage) : PackedCurrentImage :=
  ⟨fun field => packWord (image.words field), fun field => packBytes (image.backend field), packBytes image.header⟩

def unpackImage (image : PackedCurrentImage) : CurrentImage :=
  ⟨fun field => unpackWord (image.words field), fun field => unpackBytes (image.backend field), unpackBytes image.header⟩

theorem unpack_packImage (image : CurrentImage) : unpackImage (packImage image) = image := by
  cases image with
  | mk words backend header =>
      simp only [unpackImage, packImage, unpack_packWord, unpack_packBytes]

def imageCodec : Codec CurrentImage PackedCurrentImage :=
  ⟨packImage, unpackImage, unpack_packImage⟩

def packedCurrent {material : BodyIO.Material} (current : BodyIO.Current material) := packImage (capture current)

theorem packedCurrent_injective {material : BodyIO.Material} :
    Function.Injective (packedCurrent (material := material)) :=
  (Function.LeftInverse.injective unpack_packImage).comp capture_injective

open SaturationMonoid.NoIslandNoMagic.Consciousness.Representation

/-- Any Current reader factors through the complete packed image. This is a
readout theorem, never an operational decoder or an authority constructor. -/
noncomputable def currentReader {material : BodyIO.Material} {Output : Type}
    (reader : BodyIO.Current material → Output) :
    Set.range (packedCurrent (material := material)) → Output :=
  FaceKernelExactAt.injectiveRangeFactor packedCurrent_injective reader

theorem currentReader_source {material : BodyIO.Material} {Output : Type}
    (reader : BodyIO.Current material → Output) (current : BodyIO.Current material) :
    currentReader reader ⟨packedCurrent current, current, rfl⟩ = reader current :=
  FaceKernelExactAt.injectiveRangeFactor_commutes packedCurrent_injective reader current

variable (root : BodyIO.IORoot)

/-- The root itself emits. The returned archive holds no original Current. -/
def emitPacked (current : BodyIO.Current root.fixedSource.material) : IO PackedCurrentImage := do
  let generated ← root.emit current
  return packedCurrent generated.next

theorem actual_emit_codec_commutes (current : BodyIO.Current root.fixedSource.material) :
    unpackImage <$> emitPacked root current =
      (fun generated => capture generated.next) <$> root.emit current := by
  simp only [emitPacked, bind_pure_comp, Functor.map_map, packedCurrent, unpack_packImage]

theorem actual_emit_reader_commutes {Output : Type} (reader : CurrentImage → Output)
    (current : BodyIO.Current root.fixedSource.material) :
    (reader ∘ unpackImage) <$> emitPacked root current =
      (fun generated => reader (capture generated.next)) <$> root.emit current := by
  change (fun image => reader (unpackImage image)) <$> emitPacked root current = _
  rw [← Functor.map_map unpackImage reader, actual_emit_codec_commutes, Functor.map_map]

def runNativeTrace : Nat → BodyIO.Current root.fixedSource.material → IO (List (BodyIO.Current root.fixedSource.material))
  | 0, _ => pure []
  | fuel + 1, current => do
      let generated ← root.emit current
      let rest ← runNativeTrace fuel generated.next
      return generated.next :: rest

/-- Each successor invocation receives exactly the previous actual reply.
Only compressed material is retained in the output history. -/
def runPackedTrace : Nat → BodyIO.Current root.fixedSource.material → IO (List PackedCurrentImage)
  | 0, _ => pure []
  | fuel + 1, current => do
      let generated ← root.emit current
      let rest ← runPackedTrace fuel generated.next
      return packedCurrent generated.next :: rest

theorem actual_trace_codec_conjugate (fuel : Nat)
    (current : BodyIO.Current root.fixedSource.material) :
    runPackedTrace root fuel current = List.map packedCurrent <$> runNativeTrace root fuel current := by
  induction fuel generalizing current with
  | zero => simp [runPackedTrace, runNativeTrace]
  | succ fuel previous =>
      simp only [runPackedTrace, runNativeTrace, map_bind, map_pure]
      congr 1
      funext generated
      rw [previous, bind_map_left]
      rfl

theorem actual_trace_decodes (fuel : Nat)
    (current : BodyIO.Current root.fixedSource.material) :
    List.map unpackImage <$> runPackedTrace root fuel current =
      List.map capture <$> runNativeTrace root fuel current := by
  rw [actual_trace_codec_conjugate, Functor.map_map]
  congr 1
  funext trace
  induction trace with
  | nil => rfl
  | cons next rest previous =>
      simp only [List.map_cons, packedCurrent, unpack_packImage, previous]

theorem actual_trace_reader_no_error {Output : Type} (reader : CurrentImage → Output)
    (fuel : Nat) (current : BodyIO.Current root.fixedSource.material) :
    List.map (reader ∘ unpackImage) <$> runPackedTrace root fuel current =
      List.map (reader ∘ capture) <$> runNativeTrace root fuel current := by
  have composed : List.map (reader ∘ unpackImage) = List.map reader ∘ List.map unpackImage := by
    funext trace
    simp only [Function.comp_apply, List.map_map]
  rw [composed]
  change (fun trace => List.map reader (List.map unpackImage trace)) <$> runPackedTrace root fuel current = _
  rw [← Functor.map_map (List.map unpackImage) (List.map reader)]
  rw [actual_trace_decodes, Functor.map_map]
  congr 1
  funext trace
  simp only [List.map_map]

/-- The range witness is Prop-valued and erased. The archive data contain
only the packed complete image, never a saved original Current. -/
def emitPackedRange (current : BodyIO.Current root.fixedSource.material) :
    IO (Set.range (packedCurrent (material := root.fixedSource.material))) := do
  let generated ← root.emit current
  return ⟨packedCurrent generated.next, generated.next, rfl⟩

theorem actual_emit_all_current_readers {Output : Type}
    (reader : BodyIO.Current root.fixedSource.material → Output)
    (current : BodyIO.Current root.fixedSource.material) :
    currentReader reader <$> emitPackedRange root current =
      (fun generated => reader generated.next) <$> root.emit current := by
  simp only [emitPackedRange, bind_pure_comp, Functor.map_map, currentReader_source]

def runPackedRangeTrace : Nat → BodyIO.Current root.fixedSource.material →
    IO (List (Set.range (packedCurrent (material := root.fixedSource.material))))
  | 0, _ => pure []
  | fuel + 1, current => do
      let generated ← root.emit current
      let rest ← runPackedRangeTrace fuel generated.next
      return ⟨packedCurrent generated.next, generated.next, rfl⟩ :: rest

theorem actual_range_trace_conjugate (fuel : Nat)
    (current : BodyIO.Current root.fixedSource.material) :
    runPackedRangeTrace root fuel current =
      List.map (fun next => ⟨packedCurrent next, next, rfl⟩) <$> runNativeTrace root fuel current := by
  induction fuel generalizing current with
  | zero => simp [runPackedRangeTrace, runNativeTrace]
  | succ fuel previous =>
      simp only [runPackedRangeTrace, runNativeTrace, map_bind, map_pure]
      congr 1
      funext generated
      rw [previous, bind_map_left]
      rfl

theorem actual_trace_all_current_readers {Output : Type}
    (reader : BodyIO.Current root.fixedSource.material → Output)
    (fuel : Nat) (current : BodyIO.Current root.fixedSource.material) :
    List.map (currentReader reader) <$> runPackedRangeTrace root fuel current =
      List.map reader <$> runNativeTrace root fuel current := by
  rw [actual_range_trace_conjugate, Functor.map_map]
  congr 1
  funext trace
  induction trace with
  | nil => rfl
  | cons next rest previous => simp only [List.map_cons, currentReader_source, previous]

set_option linter.defProp false in
def completed_codec_ledger_next {current : BodyIO.Current root.fixedSource.material}
    (generated : BodyIO.GeneratedAt root.fixedSource current) :=
  And.intro (unpack_packImage (capture generated.next))
    (And.intro (BodyIO.actual_word_ledger_next root.fixedSource generated)
      (And.intro (show generated.patch = BodyIO.completePatch root.fixedSource generated.occurrence from rfl)
        (And.intro (show generated.ledger = (BodyIO.ledgerCompiler root.fixedSource).compile generated.occurrence from rfl)
          (show ∀ responsibility, (BodyIO.inventory root.fixedSource generated.occurrence.1).forward responsibility =
            BodyIO.entry root.fixedSource current responsibility from BodyIO.all_six_source_entries root.fixedSource generated))))

end RepresentationIO
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
