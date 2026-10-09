import H0mework.Versions.R9c73a630.ReleaseMaterials.DomainProofs.CPS1ResourceExecution.CPS1MaterialIncidence.CanonicalOperatorSquare

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

theorem source_car_context_swap {current : NativeCurrent source}
    (pre suffix : List (SourceCARSymbol current))
    (first second : SourceCARSymbol current)
    (different : first.mode ≠ second.mode) :
    evaluateCARWord (pre ++ [first,second] ++ suffix) =
      -(evaluateCARWord (pre ++ [second,first] ++ suffix)) := by
  apply LinearMap.ext
  intro state
  rw [List.append_assoc,List.append_assoc,evaluate_car_word_append,
    evaluate_car_word_append,evaluate_car_word_append,evaluate_car_word_append]
  rw [source_car_adjacent_swap first second different]
  simp only [LinearMap.comp_apply,LinearMap.neg_apply]
  rw [map_neg]

theorem carSwapSign_add_transport (left right : Nat) :
    carSwapSign (left+right) = carSwapSign left * carSwapSign right := by
  simp only [carSwapSign,pow_add]

theorem car_swap_chain_operator_transport {current : NativeCurrent source}
    {first last : List (SourceCARSymbol current)} {swaps : Nat}
    (chain : CARSwapChain first last swaps) :
    evaluateCARWord last = carSwapSign swaps • evaluateCARWord first := by
  induction chain with
  | refl word => simp [carSwapSign]
  | @swap pre first second suffix different =>
      have h := source_car_context_swap pre suffix second first (Ne.symm different)
      calc
        evaluateCARWord (pre ++ [second,first] ++ suffix) =
            -evaluateCARWord (pre ++ [first,second] ++ suffix) := h
        _ = carSwapSign 1 • evaluateCARWord (pre ++ [first,second] ++ suffix) := by
          rw [carSwapSign,pow_one]
          exact (neg_one_smul ℂ _).symm
  | trans chainFirst chainLast ihFirst ihLast =>
      have step := ihLast
      rw [ihFirst] at step
      rw [smul_smul] at step
      rw [← carSwapSign_add_transport] at step
      simpa [Nat.add_comm] using step

end
end CPS1MaterialIncidence
