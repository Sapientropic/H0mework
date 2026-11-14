import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3NativeCodecSeal

set_option autoImplicit false
namespace FlyCNS.C3NativeCodec
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS
open C3FiniteOccurrence

abbrev Key {boundary : Boundary} (context : Seal boundary) := C3NativePrecision.Key boundary context.anchor

def errorTag : ByteArray := ⟨#[1]⟩

/-- The success tag is the low byte of one eight-byte little-endian word;
seven bytes contain the source-bounded visit. Errors retain full UTF8. -/
def encode {boundary : Boundary} (context : Seal boundary) : Key context → ByteArray
  | .inl address => (C3Reachable.counter (address.val*256)).bytes
  | .inr why => errorTag++why.toUTF8

def readWord (bytes : ByteArray) : Nat := (C3Integer.Word.mk 8 bytes).bits 0 |>.toNat

def parse {boundary : Boundary} (context : Seal boundary) (bytes : ByteArray) : Except String (Key context) := do
  if bytes.size=0 then throw "empty source key"
  if (bytes.get! 0).toNat=0 then
    if bytes.size≠8 then throw "source success key must have eight bytes"
    let visit:=readWord bytes/256
    if within:visit<C3NativePrecision.stateBound boundary context.anchor then
      let key : Key context := .inl ⟨visit,within⟩
      if _canonical:encode context key=bytes then return key
      else throw "source success key is not canonical"
    else throw "source visit exceeds its generated physical word bound"
  else if (bytes.get! 0).toNat=1 then
    match String.fromUTF8? (bytes.extract 1 bytes.size) with
    | none => throw "source error is not complete UTF8"
    | some why =>
      let key : Key context := .inr why
      if _canonical:encode context key=bytes then return key
      else throw "source error key is not canonical"
  else throw "source key tag is not registered"

theorem counter_size (n : Nat) : (C3Reachable.counter n).bytes.size=8 := by
  simp [C3Reachable.counter,C3Raw.signed,Array.forIn_eq_foldlM,List.range'_succ,List.foldl,
    ByteArray.push,ByteArray.size]

theorem counter_tag (n : Nat) : ((C3Reachable.counter (n*256)).bytes.get! 0).toNat=0 := by
  simp [C3Reachable.counter,C3Raw.signed,Array.forIn_eq_foldlM,List.range'_succ,List.foldl,
    ByteArray.push,ByteArray.get!]
  change n*256%256=0
  exact Nat.mul_mod_left n 256

private theorem get_data (bytes : ByteArray) (i : Nat) : bytes.get! i=bytes.data[i]! := by
  cases bytes
  rfl

theorem error_tag (why : String) : ((errorTag++why.toUTF8).get! 0).toNat=1 := by
  rw [get_data,ByteArray.data_append]
  change ((#[1]++why.toUTF8.data)[0]!).toNat=1
  simp

theorem error_nonempty (why : String) : (errorTag++why.toUTF8).size≠0 := by
  rw [ByteArray.size_append]
  change 1+why.toUTF8.size≠0
  omega

theorem error_payload (why : String) :
    (errorTag++why.toUTF8).extract 1 (errorTag++why.toUTF8).size=why.toUTF8 := by
  apply ByteArray.extract_append_eq_right
  · rfl
  · exact ByteArray.size_append

theorem utf8_roundtrip (why : String) : String.fromUTF8? why.toUTF8=some why := by
  change String.fromUTF8? why.toByteArray=some why
  unfold String.fromUTF8?
  rw [dif_pos why.isValidUTF8]
  rfl

theorem parse_encode {boundary : Boundary} (context : Seal boundary) (key : Key context) :
    parse context (encode context key)=.ok key := by
  cases key with
  | inl address =>
    have size:=counter_size (address.val*256)
    have tag:=counter_tag address.val
    have read:=C3Reachable.counter_bits (address.val*256) (sealed_payload_bound context address)
    change readWord (C3Reachable.counter (address.val*256)).bytes=address.val*256 at read
    simp [parse,encode,size,tag,read,Nat.mul_div_cancel _ (by decide : 0<256),address.isLt,pure,Except.pure]
  | inr why =>
    simp only [parse,encode,error_nonempty,error_tag,one_ne_zero,if_false,if_true,error_payload,utf8_roundtrip]
    simp [pure,Except.pure]

theorem encode_parse {boundary : Boundary} {context : Seal boundary} {bytes : ByteArray} {key : Key context}
    (paid : parse context bytes=.ok key) : encode context key=bytes := by
  unfold parse at paid
  dsimp only at paid
  simp only [bind,pure,Except.bind,Except.pure,C3NativeByteBound.throw_error] at paid
  split at paid
  · contradiction
  · split at paid
    · split at paid
      · contradiction
      · split at paid
        · split at paid
          · rename_i canonical
            cases paid
            exact canonical
          · contradiction
        · contradiction
    · split at paid
      · split at paid
        · contradiction
        · split at paid
          · rename_i canonical
            cases paid
            exact canonical
          · contradiction
      · contradiction

theorem encode_injective {boundary : Boundary} (context : Seal boundary) : Function.Injective (encode context) := by
  intro left right same
  have parsed:=congrArg (parse context) same
  rw [parse_encode,parse_encode] at parsed
  exact Except.ok.inj parsed

theorem success_size {boundary : Boundary} (context : Seal boundary)
    (address : Fin (C3NativePrecision.stateBound boundary context.anchor)) :
    (encode context (.inl address)).size=8 := counter_size _

end FlyCNS.C3NativeCodec
