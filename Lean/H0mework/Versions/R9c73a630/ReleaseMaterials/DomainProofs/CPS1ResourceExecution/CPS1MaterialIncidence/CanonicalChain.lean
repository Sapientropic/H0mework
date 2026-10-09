import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CanonicalTransport

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

/-- Prefixing preserves a generated swap chain and its exact swap count. -/
theorem carSwapChain_prepend {current : NativeCurrent source}
    (pre : List (SourceCARSymbol current))
    {first last : List (SourceCARSymbol current)} {swaps : Nat}
    (chain : CARSwapChain first last swaps) :
    CARSwapChain (pre ++ first) (pre ++ last) swaps := by
  induction chain with
  | refl word => simpa using CARSwapChain.refl (pre ++ word)
  | @swap oldPre first second suffix different =>
      simpa only [List.append_assoc] using
        (CARSwapChain.swap (pre ++ oldPre) first second suffix different)
  | trans chainFirst chainLast ihFirst ihLast =>
      exact CARSwapChain.trans ihFirst ihLast

/-- Every symbol can be moved to the right across a list of distinct modes. -/
theorem carSwapChain_move_right {current : NativeCurrent source}
    (symbol : SourceCARSymbol current) (tail : List (SourceCARSymbol current))
    (different : ∀ other ∈ tail, symbol.mode ≠ other.mode) :
    ∃ swaps, CARSwapChain ([symbol] ++ tail) (tail ++ [symbol]) swaps := by
  induction tail with
  | nil => exact ⟨0,by simpa using CARSwapChain.refl [symbol]⟩
  | cons head rest ih =>
      have headDifferent : symbol.mode ≠ head.mode := different head List.mem_cons_self
      have restDifferent : ∀ other ∈ rest, symbol.mode ≠ other.mode := by
        intro other held
        exact different other (List.mem_cons_of_mem _ held)
      obtain ⟨swaps,tailChain⟩ := ih restDifferent
      have movedTail := carSwapChain_prepend [head] tailChain
      refine ⟨swaps+1,?_⟩
      have first := CARSwapChain.swap [] symbol head rest headDifferent
      simpa [List.append_assoc,List.cons_append,Nat.add_comm] using
        (CARSwapChain.trans first movedTail)

end
end CPS1MaterialIncidence
