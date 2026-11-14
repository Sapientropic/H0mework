import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3SourceOperations
import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.SourceRepresentationIO

set_option autoImplicit false
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
namespace C3CompleteInventory
open Lean RepresentationIO
open _root_.SaturationMonoid.NoIslandNoMagic.Consciousness.Representation
local instance : LawfulMonad IO := RepresentationIO.lawfulIO

local instance : DecidableEq WordImage := fun left right =>
  decidable_of_iff (PackedRuntimeIO.WordEqual left right) (PackedRuntimeIO.wordEqual_iff left right)

/-- Full occurrence material, including the latest generated traces and
source-owned context names. Nat clocks and literal growing JSON stay intact. -/
structure Image where
  physical : ContentFullPackedIO.Image
  traces : Vector ByteArray 3
  metadata : Array (String × ByteArray)
  deriving DecidableEq
structure Packet where
  physical : ContentFullPackedIO.Packet
  traces : Vector (List WholeRepresentation.Block) 3
  metadata : Array (String × ByteArray)

def packPhysical (image : ContentFullPackedIO.Image) : ContentFullPackedIO.Packet :=
  ⟨image.words.map packWord,image.backend.map packBytes,packBytes image.header,image.visit⟩
theorem unpack_packPhysical (image : ContentFullPackedIO.Image) :
    ContentFullPackedIO.unpack (packPhysical image)=image := by
  have words : (image.words.map packWord).map unpackWord=image.words := by
    apply Vector.ext
    intro field within
    simp only [Vector.getElem_map,unpack_packWord]
  have backend : (image.backend.map packBytes).map unpackBytes=image.backend := by
    apply Vector.ext
    intro field within
    simp only [Vector.getElem_map,unpack_packBytes]
  cases image
  simp_all only [ContentFullPackedIO.unpack,packPhysical,unpack_packBytes]
def pack (image : Image) : Packet :=
  ⟨packPhysical image.physical,image.traces.map packBytes,image.metadata⟩
def unpack (packet : Packet) : Image :=
  ⟨ContentFullPackedIO.unpack packet.physical,packet.traces.map unpackBytes,packet.metadata⟩
theorem unpack_pack (image : Image) : unpack (pack image)=image := by
  have traces : (image.traces.map packBytes).map unpackBytes=image.traces := by
    apply Vector.ext
    intro field within
    simp only [Vector.getElem_map,unpack_packBytes]
  cases image
  simp_all only [unpack,pack,unpack_packPhysical]
def codec : Codec Image Packet := ⟨pack,unpack,unpack_pack⟩
theorem pack_injective : Function.Injective pack := Function.LeftInverse.injective unpack_pack

inductive Reader where
  | word (field : Fin 59) | backend (field : Fin 4) | header | visit
  | trace (field : Fin 3) | metadata
  deriving DecidableEq
def Output : Reader → Type
  | .word _ => WordImage | .backend _ | .header | .trace _ => ByteArray
  | .visit => Nat | .metadata => Array (String × ByteArray)
def read : (reader : Reader) → Image → Output reader
  | .word field,image => image.physical.words.get field
  | .backend field,image => image.physical.backend.get field
  | .header,image => image.physical.header | .visit,image => image.physical.visit
  | .trace field,image => image.traces.get field | .metadata,image => image.metadata
def consumers : IndependentConsumerSystem Image where
  Consumer := Reader
  Output := Output
  read := read
  positive := ⟨.visit⟩
theorem complete_reads (left right : Image) : consumers.Indistinguishable left right ↔ left=right := by
  constructor
  · intro same
    have words : left.physical.words=right.physical.words := by
      apply Vector.ext
      intro field within
      exact same (.word ⟨field,within⟩)
    have backend : left.physical.backend=right.physical.backend := by
      apply Vector.ext
      intro field within
      exact same (.backend ⟨field,within⟩)
    have traces : left.traces=right.traces := by
      apply Vector.ext
      intro field within
      exact same (.trace ⟨field,within⟩)
    have header : left.physical.header=right.physical.header := same .header
    have visit : left.physical.visit=right.physical.visit := same .visit
    have metadata : left.metadata=right.metadata := same .metadata
    have physical : left.physical=right.physical := by
      have ext : ∀ a b : ContentFullPackedIO.Image,a.words=b.words → a.backend=b.backend →
          a.header=b.header → a.visit=b.visit → a=b := by
        rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ rfl rfl rfl rfl
        rfl
      exact ext _ _ words backend header visit
    cases left
    cases right
    simp_all only [consumers]
  · intro same
    cases same
    intro reader
    rfl
theorem packed_kernel_exact : FaceKernelExactAt consumers pack := by
  intro left right
  rw [complete_reads]
  exact ⟨fun same => pack_injective same,fun same => congrArg pack same⟩
theorem every_registered_reader_unique_factorization (reader : Reader) :
    ∃! factor : Set.range pack → Output reader,
      ∀ image,factor ⟨pack image,image,rfl⟩=read reader image :=
  packed_kernel_exact.everyConsumer_unique_factorization reader

/-- With every actual material reader retained, a candidate cannot merge
different full images. No state finiteness or future result is assumed. -/
theorem minimum_complete_representation {Candidate : Type} (represent : Image → Candidate)
    (reads : (reader : Reader) → Candidate → Output reader)
    (commutes : ∀ reader image,reads reader (represent image)=read reader image) :
    Function.FactorsThrough pack represent := by
  intro left right same
  apply congrArg pack
  apply (complete_reads left right).1
  intro reader
  change read reader left=read reader right
  rw [← commutes reader left,← commutes reader right,same]

def sourceMetadata (source : ContentReentryIO.Source) : Array (String × ByteArray) :=
  #[("installation.json",source.material.installation),("body.mjb",source.material.model),
    ("prior-whole-ledger",source.material.priorLedger),
    (source.material.primitive.capturedPath.toString,source.material.primitive.bytes)] ++
    (source.material.linked.map fun file => (file.capturedPath.toString,file.bytes)).toArray
def fromComputed {source : ContentReentryIO.Source} {current : ContentReentryIO.Current source.material}
    (computed : C3.NormalFormAt source current) : Image :=
  ⟨ContentReentryIO.capture computed.after,⟨#[computed.events,computed.learning,computed.physics],rfl⟩,sourceMetadata source⟩
def fromActual {source : ContentReentryIO.Source} {current : ContentReentryIO.Current source.material}
    (actual : ContentReentryRoot.GeneratedAt source current) : Image :=
  ⟨ContentReentryIO.capture actual.next,⟨#[actual.reply.events,actual.reply.learning,actual.reply.physics],rfl⟩,sourceMetadata source⟩
theorem computed_actual_same_occurrence {source : ContentReentryIO.Source}
    {current : ContentReentryIO.Current source.material} (accepted : C3.AcceptedAt source current)
    : fromComputed accepted.computed=fromActual accepted.original := by
  simp only [fromComputed,fromActual,accepted.whole,accepted.events,accepted.learning,accepted.physics]

def requiredBytes (material : ContentReentryIO.Material) (image : Image) (required : Fin 59) : ByteArray :=
  (image.physical.words.get (material.addresses.get required)).bytes
def requiredValue (material : ContentReentryIO.Material) (image : Image) (required : Fin 59) (index : Nat) : Nat :=
  let word := image.physical.words.get (material.addresses.get required)
  Admission.littleWord word.bytes (word.dataStart+word.width*index) word.width
def interval (material : ContentReentryIO.Material) (image : Image) (offset count : Nat)
    (bounded : offset+count≤59) : Vector ByteArray count :=
  Vector.ofFn fun field => requiredBytes material image ⟨offset+field.val,by omega⟩
def observerReport (source : ContentReentryIO.Source) (image : Image) : ContentReentryClosure.ObserverReport :=
  ⟨interval source.material image 0 14 (by decide) ++ interval source.material image 52 7 (by decide),
    interval source.material image 43 8 (by decide),interval source.material image 39 4 (by decide),
    image.traces.get ⟨0,by decide⟩,image.traces.get ⟨1,by decide⟩⟩
def receiverReport (source : ContentReentryIO.Source) (image : Image) : ContentReentryClosure.ReceiverReport :=
  ⟨interval source.material image 14 25 (by decide),image.traces.get ⟨2,by decide⟩,
    requiredValue source.material image ⟨6,by decide⟩ 0,requiredValue source.material image ⟨34,by decide⟩ 0⟩
private theorem interval_from_actual {source : ContentReentryIO.Source}
    {current : ContentReentryIO.Current source.material} (actual : ContentReentryRoot.GeneratedAt source current)
    (offset count : Nat) (bounded : offset+count≤59) :
    interval source.material (fromActual actual) offset count bounded=ContentReentryClosure.intervalBytes actual.next offset count bounded := by
  apply Vector.ext
  intro field within
  simp only [interval,requiredBytes,fromActual,ContentReentryIO.capture,ContentReentryClosure.intervalBytes,
    ContentReentryIO.wordAt,Vector.getElem_ofFn,Vector.get,Vector.toArray_map,Array.getElem_map,RepresentationIO.captureWord]
  rfl
theorem original_observer_from_complete {source : ContentReentryIO.Source}
    {current : ContentReentryIO.Current source.material} (actual : ContentReentryRoot.GeneratedAt source current) :
    observerReport source (fromActual actual)=ContentReentryClosure.observerRead actual := by
  simp only [observerReport,ContentReentryClosure.observerRead,ContentReentryClosure.neuralRead,interval_from_actual]
  rfl
theorem original_receiver_from_complete {source : ContentReentryIO.Source}
    {current : ContentReentryIO.Current source.material} (actual : ContentReentryRoot.GeneratedAt source current) :
    receiverReport source (fromActual actual)=ContentReentryClosure.receivedRead actual := by
  rw [receiverReport,interval_from_actual]
  congr 1
  · simp only [requiredValue,fromActual,ContentReentryIO.capture,ContentReentryIO.Current.tick,
      ContentReentryIO.tickAt,ContentReentryIO.wordAt,Vector.get,Vector.toArray_map,Array.getElem_map,RepresentationIO.captureWord,Admission.NpyVector.word]
    simp only [Nat.mul_zero,Nat.add_zero]
    rfl
  · simp only [requiredValue,fromActual,ContentReentryIO.capture,ContentReentryIO.physicsTick,
      ContentReentryIO.wordAt,Vector.get,Vector.toArray_map,Array.getElem_map,RepresentationIO.captureWord,Admission.NpyVector.word]
    simp only [Nat.mul_zero,Nat.add_zero]
    rfl
theorem codec_preserves_original_consumers {source : ContentReentryIO.Source}
    {current : ContentReentryIO.Current source.material} (accepted : C3.AcceptedAt source current) :
    observerReport source (unpack (pack (fromComputed accepted.computed)))=ContentReentryClosure.observerRead accepted.original ∧
    receiverReport source (unpack (pack (fromComputed accepted.computed)))=ContentReentryClosure.receivedRead accepted.original := by
  rw [unpack_pack,computed_actual_same_occurrence]
  exact ⟨original_observer_from_complete accepted.original,original_receiver_from_complete accepted.original⟩

abbrev Letter := BodyFullIO.Operation
def letters : List Letter := [.neural,.damage,.repair]
theorem letters_complete (letter : Letter) : letter ∈ letters := by cases letter <;> simp [letters]

/-- The registered operation is checked at its original source incidence;
wrong operation words take the original effectful error branch. -/
def action (source : ContentReentryIO.Source) (letter : Letter) (image : Image) : IO Image := do
  if image.metadata != sourceMetadata source then throw (IO.userError "C3 inventory changes installed source material/authority")
  let nonce ← IO.monoNanosNow
  let path := source.material.directory/("C3-inventory-input-"++toString nonce)
  ContentFullPackedIO.writeImage image.physical path
  let current ← ContentReentryIO.readCurrent source.material path
  if ContentReentryIO.capture current != image.physical then throw (IO.userError "C3 inventory decoder changes full current")
  if BodyFullIO.operationAt current.visit != letter then throw (IO.userError "operation not admitted at this source incidence")
  return fromActual (← ContentReentryRoot.emit source current)

theorem every_registered_word_zero_error (source : ContentReentryIO.Source) (word : List Letter) (image : Image) :
    unpack <$> runEffect (fun letter => codec.liftEffect (action source letter)) word (pack image) =
      runEffect (action source) word image :=
  decoded_effect_words codec (action source) word image

set_option linter.defProp false in
def complete_model_original_ledger_next {source : ContentReentryIO.Source}
    {current : ContentReentryIO.Current source.material} (accepted : C3.AcceptedAt source current) :=
  And.intro (computed_actual_same_occurrence accepted)
    (And.intro (unpack_pack (fromComputed accepted.computed))
      (And.intro (ContentReentryRoot.actual_target source accepted.original)
        (show ∀ r,(accepted.original.patch.toLedgerWriteEvolution.destination
          (ContentReentryRoot.entry source current r)).1=ContentReentryRoot.entry source accepted.original.next r from
          ContentReentryRoot.actual_six_rows source accepted.original)))

end C3CompleteInventory
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
