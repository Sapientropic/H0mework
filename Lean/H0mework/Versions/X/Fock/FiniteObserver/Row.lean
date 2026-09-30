import H0mework.Versions.X.Fock.FiniteObserver.Observer

set_option autoImplicit false

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace SourceFiniteObserverCalculation

def rowResponse (bound scale sourceBound phase : Nat) (row : Fin (sourceBound + 1) → ℚ)
    (actor : Fin (bound + 1)) : ℚ :=
  (∑ source, if source.val + 1 + phase = (actor.val + 1) * scale - 1 then row source else 0) +
    (∑ source, row source) + (((actor.val + 1) * scale : Nat) : ℚ) *
      (∑ source, row source * ((source.val + 1 + phase + 1 : Nat) : ℚ))

def rowCalculate (bound scale sourceBound phase : Nat) (row : Fin (sourceBound + 1) → ℚ) : Fin (bound + 1) → ℚ :=
  solve bound scale (rowResponse bound scale sourceBound phase row)

noncomputable section

def rowWord (bound phase : Nat) (row : Fin (bound + 1) → ℚ) : Nat →₀ ℚ :=
  ∑ source, Finsupp.single (source.val + 1 + phase) (row source)

theorem row_word_source (bound : Nat) (row : Fin (bound + 1) → ℚ) :
    rowWord bound 0 row = SourceConditionalNativeKeys.word bound row := by
  simp only [rowWord, Nat.add_zero, SourceConditionalNativeKeys.word, LinearMap.coe_mk, AddHom.coe_mk,
    SourceConditionalNativeKeys.source_single, Finsupp.smul_single, smul_eq_mul, mul_one]

theorem row_response_source (bound scale sourceBound phase : Nat) (row : Fin (sourceBound + 1) → ℚ)
    (actor : Fin (bound + 1)) :
    rowResponse bound scale sourceBound phase row actor = response bound scale (rowWord sourceBound phase row) actor := by
  classical
  simp only [rowResponse, response, rowWord, Finsupp.finsetSum_apply, Finsupp.single_apply,
    map_sum, SourceSuccessorBoundary.mass_single, word_clock_single, SourceClockModel.rawClock,
    Int.cast_add, Int.cast_natCast, Int.cast_one, Nat.cast_add, Nat.cast_one]

theorem row_calculate_source (bound scale sourceBound phase : Nat) (row : Fin (sourceBound + 1) → ℚ) :
    rowCalculate bound scale sourceBound phase row = calculate bound scale (rowWord sourceBound phase row) := by
  unfold rowCalculate calculate
  congr 1
  funext actor
  exact row_response_source _ _ _ _ _ _

theorem row_word_next (bound phase : Nat) (row : Fin (bound + 1) → ℚ) :
    rowWord bound (phase + 1) row = SourceSuccessorBoundary.push ℚ (rowWord bound phase row) := by
  simp only [rowWord, map_sum, SourceSuccessorBoundary.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    Nat.succ_eq_add_one, Nat.add_assoc]

theorem embed_push (word : Nat →₀ ℚ) :
    SourceConditionalRationalStream.embedWord (SourceSuccessorBoundary.push ℚ word) =
      SourceSuccessorBoundary.push ℂ (SourceConditionalRationalStream.embedWord word) := by
  induction word using Finsupp.induction with
  | zero => simp
  | @single_add index scalar word notMem nonzero previous =>
    simp only [map_add]
    rw [previous]
    simp only [SourceSuccessorBoundary.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, embed_single]

theorem row_word_time (bound phase : Nat) (row : Fin (bound + 1) → ℚ) :
    SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (rowWord bound phase row)) =
      SourceCopyTimeModel.time phase
        (SourceJointClockGraph.read (SourceConditionalRationalStream.embedWord (SourceConditionalNativeKeys.word bound row))) := by
  induction phase with
  | zero => rw [row_word_source]; rfl
  | succ phase previous =>
    rw [row_word_next, embed_push, ← SourceJointClockGraph.action_source, previous]
    change SourceJointClockGraph.action ((SourceJointClockGraph.action ^ phase) _) = (SourceJointClockGraph.action ^ (phase + 1)) _
    rw [pow_succ']
    rfl

end
end SourceFiniteObserverCalculation
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
