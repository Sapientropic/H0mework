import H0mework.Versions.R26b91feb.ReleaseMaterials.Scratch.FlyCNS.C3PublishedInvocation
import Mathlib.Tactic

set_option autoImplicit false
namespace FlyCNS.C3NativeByteBound
open SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot.FlyCNS

theorem byte_bound (bytes : ByteArray) (index : Nat) : Admission.byteNat bytes index<256 := by
  unfold Admission.byteNat
  split
  · exact UInt8.toNat_lt _
  · decide

theorem little_bound (bytes : ByteArray) (start width : Nat) : Admission.littleWord bytes start width<256^width := by
  induction width with
  | zero => simp [Admission.littleWord]
  | succ width previous =>
    have b:=byte_bound bytes (start+width)
    have scaled:=Nat.mul_le_mul_right (256^width) (show Admission.byteNat bytes (start+width)≤255 by omega)
    simp only [Admission.littleWord,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil,Nat.pow_succ] at *
    omega

theorem word_bound {bytes : ByteArray} (vector : Admission.NpyVector bytes) (index : Nat) :
    vector.word index<256^vector.width := little_bound _ _ _

theorem throw_error {α : Type} (why : String) : (throw why : Except String α)=.error why := rfl

set_option maxHeartbeats 1000000 in
theorem parser_width {bytes : ByteArray} {dtype : String} {width : Nat} {vector : Admission.NpyVector bytes}
    (paid:Admission.parseNpyVector bytes dtype width=.ok vector) : vector.width=width := by
  unfold Admission.parseNpyVector at paid
  dsimp only at paid
  generalize (List.range 6).any (fun index => Admission.byteNat bytes index !=
    ([147,78,85,77,80,89] : List Nat)[index]?.getD 0)=magic at paid
  generalize Admission.byteNat bytes 6=version at paid
  generalize Admission.byteNat bytes 7=minor at paid
  generalize Admission.littleWord bytes 8 (if version=1 then 2 else 4)=length at paid
  simp only [bind,pure,Except.bind,Except.pure,throw_error] at paid
  split at paid
  · cases paid
  · split at paid
    · cases paid
    · split at paid
      · cases paid
      · split at paid
        · split at paid
          · cases paid
          · split at paid
            · rename_i text encoding
              generalize Admission.parseHeaderCount text dtype=result at paid
              cases result with
              | error why => cases paid
              | ok count =>
                dsimp only at paid
                split at paid
                · cases paid;rfl
                · cases paid
            · cases paid
        · split at paid
          · split at paid
            · cases paid
            · split at paid
              · cases paid
              · split at paid
                · rename_i text encoding
                  generalize Admission.parseHeaderCount text dtype=result at paid
                  cases result with
                  | error why => cases paid
                  | ok count =>
                    dsimp only at paid
                    split at paid
                    · cases paid;rfl
                    · cases paid
                · cases paid
          · cases paid


theorem word_parser_width {layout : BodyIO.FieldLayout} {bytes : ByteArray} {word : BodyIO.Word}
    (paid:BodyIO.parseWord layout bytes=.ok word) : word.vector.width=layout.width := by
  unfold BodyIO.parseWord at paid
  simp only [bind,pure,Except.bind,Except.pure] at paid
  cases h:Admission.parseNpyVector bytes layout.dtype layout.width with
  | error why => simp only [h] at paid;contradiction
  | ok vector => simp only [h] at paid;cases paid;exact parser_width h

end FlyCNS.C3NativeByteBound
