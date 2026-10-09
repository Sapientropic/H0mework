import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CanonicalChain

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1800000
namespace CPS1MaterialIncidence
noncomputable section
open CPS1PhosphorylExchange CPS1ElectronicSource CPS1AtomicDynamics
open scoped BigOperators InnerProductSpace Matrix

variable {frame : CPS1Recycling.Frame} {cursor : CPS1ReactiveNuclear.SourceCursor frame}
  {priorRaw : CPS1SameEventFunction.Classical.Raw}
  {before : CPS1SameEventFunction.Classical.Current cursor priorRaw}
  {step : CPS1SameEventFunction.Classical.NativeStep before priorRaw.time}
  {raw : Raw} {source : Common before step raw}

def pairCreates {current : NativeCurrent source} :
    List (AddressedBasisIndex current × AddressedBasisIndex current) → List (SourceCARSymbol current) :=
  List.map (fun pair => SourceCARSymbol.creating pair.1)

def pairAnnihilates {current : NativeCurrent source} :
    List (AddressedBasisIndex current × AddressedBasisIndex current) → List (SourceCARSymbol current) :=
  List.map (fun pair => SourceCARSymbol.annihilating pair.2)

def pairInterleaved {current : NativeCurrent source} :
    List (AddressedBasisIndex current × AddressedBasisIndex current) → List (SourceCARSymbol current)
  | [] => []
  | pair :: rest => [SourceCARSymbol.creating pair.1,SourceCARSymbol.annihilating pair.2] ++ pairInterleaved rest

def pairGrouped {current : NativeCurrent source} (pairs : List (AddressedBasisIndex current × AddressedBasisIndex current)) :
    List (SourceCARSymbol current) := pairCreates pairs ++ pairAnnihilates pairs

private theorem pair_interleaved_eq_flatMap {current : NativeCurrent source}
    (pairs : List (AddressedBasisIndex current × AddressedBasisIndex current)) :
    pairInterleaved pairs = pairs.flatMap (fun pair =>
      [SourceCARSymbol.creating pair.1,SourceCARSymbol.annihilating pair.2]) := by
  induction pairs with
  | nil => rfl
  | cons pair rest ih => simp [pairInterleaved,ih]

theorem pair_interleaved_eq_canonical {current : NativeCurrent source}
    (previous after : AtomConfiguration current) :
    pairInterleaved (canonicalPairing current previous after) =
      canonicalCARWord current previous after := by
  unfold canonicalCARWord
  exact pair_interleaved_eq_flatMap (canonicalPairing current previous after)

theorem pair_mode_cross (current : NativeCurrent source)
    (previous after : AtomConfiguration current)
    {added : AddressedBasisIndex current} {removed : AddressedBasisIndex current}
    (addedHeld : added ∈ canonicalAdded current previous after)
    (removedHeld : removed ∈ canonicalRemoved current previous after) :
    removed ≠ added := by
  unfold canonicalAdded at addedHeld
  unfold canonicalRemoved at removedHeld
  rw [Finset.mem_toList] at addedHeld removedHeld
  have addedParts := Finset.mem_sdiff.mp addedHeld
  have removedParts := Finset.mem_sdiff.mp removedHeld
  intro same
  subst added
  exact removedParts.2 addedParts.1

theorem pair_mode_cross_list (current : NativeCurrent source)
    (previous after : AtomConfiguration current)
    {pairs : List (AddressedBasisIndex current × AddressedBasisIndex current)}
    (addedHeld : ∀ pair ∈ pairs, pair.1 ∈ canonicalAdded current previous after)
    (removedHeld : ∀ pair ∈ pairs, pair.2 ∈ canonicalRemoved current previous after) :
    ∀ pair ∈ pairs, ∀ other ∈ pairs, pair.2 ≠ other.1 := by
  intro pair pairHeld other otherHeld
  exact pair_mode_cross current previous after
    (addedHeld other otherHeld) (removedHeld pair pairHeld)

private theorem zip_mem_components {α β : Type} [DecidableEq α] [DecidableEq β]
    {xs : List α} {ys : List β} {pair : α × β}
    (held : pair ∈ xs.zip ys) : pair.1 ∈ xs ∧ pair.2 ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at held
  | cons x xs ih =>
      cases ys with
      | nil => simp at held
      | cons y ys =>
          simp only [List.zip_cons_cons,List.mem_cons] at held ⊢
          rcases held with head | rest
          · cases head
            exact ⟨Or.inl rfl, Or.inl rfl⟩
          · exact ⟨Or.inr (ih rest).1, Or.inr (ih rest).2⟩

/-- Appending a fixed suffix to a generated swap chain preserves its count. -/
theorem carSwapChain_append {current : NativeCurrent source}
    {first last : List (SourceCARSymbol current)} {swaps : Nat}
    (chain : CARSwapChain first last swaps) (suffix : List (SourceCARSymbol current)) :
    CARSwapChain (first ++ suffix) (last ++ suffix) swaps := by
  induction chain with
  | refl word => simpa using CARSwapChain.refl (word ++ suffix)
  | @swap pre first second middle different =>
      simpa only [List.append_assoc] using
        (CARSwapChain.swap pre first second (middle ++ suffix) different)
  | trans chainFirst chainLast ihFirst ihLast =>
      exact CARSwapChain.trans ihFirst ihLast

private theorem pair_chain_aux {current : NativeCurrent source}
    (pairs : List (AddressedBasisIndex current × AddressedBasisIndex current))
    (cross : ∀ pair ∈ pairs, ∀ other ∈ pairs, pair.2 ≠ other.1) :
    ∃ swaps, CARSwapChain (pairInterleaved pairs) (pairGrouped pairs) swaps := by
  induction pairs with
  | nil => exact ⟨0,by simp [pairInterleaved,pairGrouped]; exact CARSwapChain.refl []⟩
  | cons pair rest ih =>
      have restCross : ∀ p ∈ rest, ∀ q ∈ rest, p.2 ≠ q.1 := by
        intro p hp q hq
        exact cross p (List.mem_cons_of_mem _ hp) q (List.mem_cons_of_mem _ hq)
      obtain ⟨restSwaps,restChain⟩ := ih restCross
      have pairToRest : ∀ other ∈ pairCreates rest,
          (SourceCARSymbol.annihilating pair.2).mode ≠ other.mode := by
        intro other otherHeld
        change other ∈ rest.map (fun q => SourceCARSymbol.creating q.1) at otherHeld
        obtain ⟨q,qHeld,rfl⟩ := List.mem_map.mp otherHeld
        exact cross pair List.mem_cons_self q (List.mem_cons_of_mem _ qHeld)
      obtain ⟨moveSwaps,moveChain⟩ := carSwapChain_move_right
        (SourceCARSymbol.annihilating pair.2) (pairCreates rest) pairToRest
      have restWithPrefix := carSwapChain_prepend
        [SourceCARSymbol.creating pair.1,SourceCARSymbol.annihilating pair.2] restChain
      have movedWithSuffix := carSwapChain_append moveChain (pairAnnihilates rest)
      have movedWithPrefix := carSwapChain_prepend
        [SourceCARSymbol.creating pair.1] movedWithSuffix
      refine ⟨moveSwaps+restSwaps,?_⟩
      simpa [pairInterleaved,pairGrouped,pairCreates,pairAnnihilates,List.append_assoc,
        Nat.add_comm] using
        (CARSwapChain.trans restWithPrefix movedWithPrefix)

theorem canonical_pair_chain (current : NativeCurrent source)
    (previous after : AtomConfiguration current) :
    ∃ swaps, CARSwapChain
      (canonicalCARWord current previous after)
      (pairGrouped (canonicalPairing current previous after)) swaps := by
  have chain := pair_chain_aux (canonicalPairing current previous after) (by
    intro pair pairHeld other otherHeld
    apply pair_mode_cross current previous after
    · unfold canonicalPairing at otherHeld
      have components := zip_mem_components otherHeld
      exact components.1
    · unfold canonicalPairing at pairHeld
      have components := zip_mem_components pairHeld
      exact components.2)
  have eqIC := pair_interleaved_eq_canonical (source:=source) (current:=current) previous after
  rw [eqIC] at chain
  exact chain

end
end CPS1MaterialIncidence
