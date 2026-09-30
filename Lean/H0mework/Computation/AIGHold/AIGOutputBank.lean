import Std.Sat.AIG.RefVec

/-!
# One literal restoring stage for every original output port

The bank appends one declaration per port, including repeated references.
No Boolean simplifier or sharing cache may merge these physical stages. The
empty metadata cache is valid for the actual extended declaration array.
-/

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
namespace Cells.Storage

open Std.Sat

variable {α : Type} [DecidableEq α] [Hashable α] {width : Nat}

def aigOutputBankDecls (entry : AIG.RefVecEntry α width) : Array (AIG.Decl α) :=
  entry.aig.decls ++ Array.ofFn (fun index : Fin width =>
    let ref := entry.vec.get index.val index.isLt
    .gate (.mk ref.gate ref.invert) (.mk 0 true))

@[simp] theorem aigOutputBankDecls_size (entry : AIG.RefVecEntry α width) :
    (aigOutputBankDecls entry).size = entry.aig.decls.size + width := by
  simp only [aigOutputBankDecls, Array.size_append, Array.size_ofFn]

theorem aigOutputBankDecls_old (entry : AIG.RefVecEntry α width) (index : Nat)
    (old : index < entry.aig.decls.size) :
    (aigOutputBankDecls entry)[index]'(by rw [aigOutputBankDecls_size]; omega) =
      entry.aig.decls[index] :=
  Array.getElem_append_left old

theorem aigOutputBankDecls_new (entry : AIG.RefVecEntry α width) (index : Fin width) :
    (aigOutputBankDecls entry)[entry.aig.decls.size + index.val]'
        (by rw [aigOutputBankDecls_size]; omega) =
      .gate (.mk (entry.vec.get index.val index.isLt).gate
        (entry.vec.get index.val index.isLt).invert) (.mk 0 true) := by
  simp only [aigOutputBankDecls, Array.getElem_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, Array.getElem_ofFn]

theorem aigOutputBankDecls_isDAG (entry : AIG.RefVecEntry α width) :
    AIG.IsDAG α (aigOutputBankDecls entry) := by
  intro index left right bound declaration
  by_cases old : index < entry.aig.decls.size
  · rw [aigOutputBankDecls_old entry index old] at declaration
    exact entry.aig.hdag old declaration
  · have indexBound : index - entry.aig.decls.size < width := by
      rw [aigOutputBankDecls_size] at bound
      omega
    have added := aigOutputBankDecls_new entry ⟨index - entry.aig.decls.size, indexBound⟩
    have address : entry.aig.decls.size + (index - entry.aig.decls.size) = index := by omega
    simp only [address] at added
    rw [added] at declaration
    obtain ⟨rfl, rfl⟩ := AIG.Decl.gate.inj declaration
    simp only [AIG.Fanin.gate_mk]
    have faninBound := (entry.vec.get (index - entry.aig.decls.size) indexBound).hgate
    have nonempty := entry.aig.hzero
    constructor <;> omega

def aigOutputBankGraph (entry : AIG.RefVecEntry α width) : AIG α where
  decls := aigOutputBankDecls entry
  cache := AIG.Cache.empty
  hdag := aigOutputBankDecls_isDAG entry
  hzero := by rw [aigOutputBankDecls_size]; have := entry.aig.hzero; omega
  hconst := by
    rw [aigOutputBankDecls_old entry 0 entry.aig.hzero]
    exact entry.aig.hconst

def aigOutputBank (entry : AIG.RefVecEntry α width) : AIG.RefVecEntry α width where
  aig := aigOutputBankGraph entry
  vec :=
    { refs := Vector.ofFn (fun index : Fin width => AIG.Fanin.mk (entry.aig.decls.size + index.val) false)
      hrefs := by
        intro index bound
        simp only [Vector.getElem_ofFn, AIG.Fanin.gate_mk]
        change entry.aig.decls.size + index < (aigOutputBankDecls entry).size
        rw [aigOutputBankDecls_size]
        omega }

theorem aigOutputBank_size (entry : AIG.RefVecEntry α width) :
    (aigOutputBank entry).aig.decls.size = entry.aig.decls.size + width :=
  aigOutputBankDecls_size entry

theorem aigOutputBank_ref_gate (entry : AIG.RefVecEntry α width) (index : Fin width) :
    ((aigOutputBank entry).vec.get index.val index.isLt).gate = entry.aig.decls.size + index.val := by
  simp only [aigOutputBank, AIG.RefVec.get, Vector.getElem_ofFn, AIG.Fanin.gate_mk]

theorem aigOutputBank_ref_invert (entry : AIG.RefVecEntry α width) (index : Fin width) :
    ((aigOutputBank entry).vec.get index.val index.isLt).invert = false := by
  simp only [aigOutputBank, AIG.RefVec.get, Vector.getElem_ofFn, AIG.Fanin.invert_mk]

theorem aigOutputBank_decl (entry : AIG.RefVecEntry α width) (index : Fin width) :
    (aigOutputBank entry).aig.decls[((aigOutputBank entry).vec.get index.val index.isLt).gate]'
        ((aigOutputBank entry).vec.get index.val index.isLt).hgate =
      .gate (.mk (entry.vec.get index.val index.isLt).gate
        (entry.vec.get index.val index.isLt).invert) (.mk 0 true) := by
  simpa only [aigOutputBank, aigOutputBankGraph, AIG.RefVec.get,
    Vector.getElem_ofFn, AIG.Fanin.gate_mk] using
    aigOutputBankDecls_new entry index

theorem aigOutputBank_prefix (entry : AIG.RefVecEntry α width) :
    AIG.IsPrefix entry.aig.decls (aigOutputBank entry).aig.decls where
  size_le := by rw [aigOutputBank_size]; omega
  idx_eq := fun index bound => aigOutputBankDecls_old entry index bound

theorem aigOutputBank_refs_injective (entry : AIG.RefVecEntry α width) :
    Function.Injective (fun index : Fin width => (aigOutputBank entry).vec.get index.val index.isLt) := by
  intro left right same
  have addresses := congrArg AIG.Ref.gate same
  rw [aigOutputBank_ref_gate, aigOutputBank_ref_gate] at addresses
  apply Fin.ext
  omega

theorem aigOutputBank_denote (entry : AIG.RefVecEntry α width) (index : Fin width) (assign : α → Bool) :
    AIG.denote assign ⟨(aigOutputBank entry).aig, (aigOutputBank entry).vec.get index.val index.isLt⟩ =
      AIG.denote assign ⟨entry.aig, entry.vec.get index.val index.isLt⟩ := by
  have literal := aigOutputBank_decl entry index
  change AIG.denote assign ⟨(aigOutputBank entry).aig,
    ⟨((aigOutputBank entry).vec.get index.val index.isLt).gate,
      ((aigOutputBank entry).vec.get index.val index.isLt).invert,
      ((aigOutputBank entry).vec.get index.val index.isLt).hgate⟩⟩ = _
  rw [AIG.denote_idx_gate literal]
  simp only [AIG.Fanin.gate_mk, AIG.Fanin.invert_mk, aigOutputBank_ref_invert, Bool.xor_false]
  rw [AIG.denote_idx_false (aigOutputBank entry).aig.hconst, Bool.and_true]
  exact AIG.denote.eq_of_isPrefix ⟨entry.aig, entry.vec.get index.val index.isLt⟩
    (aigOutputBank entry).aig (aigOutputBank_prefix entry)

end Cells.Storage
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Canonical.Coupling.Physical
