import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralFold
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCacheProgramConsumers

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralFeed
open PreparationVacuumLiteralAdmission PreparationVacuumNumericSource PreparationVacuumArenaRows
open PreparationVacuumDAGSemantic PreparationVacuumCanonicalMoyal PreparationVacuumEngineBudget
open PreparationVacuumEngineSource PreparationVacuumEngineSmooth PreparationVacuumArenaBudget PreparationVacuumClockSymbol
open PreparationVacuumMoyalNormalization PreparationVacuumCentralBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open PreparationVacuumSourceCacheProgram PreparationVacuumSourceCacheRules PreparationVacuumClockBudget
open scoped BigOperators Topology

def LowerSourceOnly {k : ℕ} (e : ArenaExpression k) : Prop :=
  ArenaExpression.rec (motive_1:=fun _=>Prop) (motive_2:=fun _=>Prop)
    (fun _=>True) (fun d _=>d.val<2) (fun _ _=>True)
    (fun _ _ _ left right=>left∧right) (fun _ _ word=>word)
    (fun _ _ left right=>left∧right) True (fun _ _ head tail=>head∧tail) e

theorem compiled_source_only_lower (n : ℕ) (j : Fin 13) :
    LowerSourceOnly (compile (erase (sourceTerm n j))) := by
  cases n with
  | zero=>rw [source_zero_erasure];trivial
  | succ n=>
    cases n with
    | zero=>rw [source_first_erasure];change (1 : ℕ)<2;decide
    | succ n=>
      cases n with
      | zero=>
        rw [source_second_erasure]
        by_cases h : j=0 <;> simp [h,compile,compilePrimitive,LowerSourceOnly]
      | succ n=>rw [source_later_erasure];trivial

def literalEnergyArray (k : ℕ) : PreparationVacuumCentralBudget.ArrayBound :=
  literalExpressionArray (moyalNormalizedEnergy k)

def literalClockArray (k : ℕ) (a : Fin 4) : PreparationVacuumCentralBudget.ArrayBound :=
  literalExpressionArray (normalizedClockExpression k a)

def literalFiveArrays (k : ℕ) (i : Fin 5) : PreparationVacuumCentralBudget.ArrayBound :=
  Fin.lastCases (literalEnergyArray k) (fun a=>literalClockArray (k-1) a) i

def actualFiveSymbols (k : ℕ) (i : Fin 5) : PreparationVacuumCanonicalMoyal.Symbol :=
  Fin.lastCases (sourceEngineEnergy k) (fun a=>sourceEngine k a (Fin.last k)) i

theorem source_five_admitted (k : ℕ) (i : Fin 5) :
    Dominates (sourceFiveArrays k i) (literalFiveArrays k i) := by
  induction i using Fin.lastCases with
  | last=>simpa only [sourceFiveArrays,literalFiveArrays,Fin.lastCases_last,sourceEnergyArray,literalEnergyArray] using source_expression_admitted (moyalNormalizedEnergy k)
  | cast a=>simpa only [sourceFiveArrays,literalFiveArrays,Fin.lastCases_castSucc,sourceClockCoefficientArray,literalClockArray] using source_expression_admitted (normalizedClockExpression (k-1) a)

theorem literal_five_nonnegative (k : ℕ) (i : Fin 5) : Nonnegative (literalFiveArrays k i) := by
  intro m
  exact (sourceFiveArrays_nonnegative k i m).trans (source_five_admitted k i m)

theorem actual_literal_energy_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) :
    FiniteBound (sourceEngineEnergy k) M (literalEnergyArray k) (z,WithLp.toLp 2 u) :=
  finite_dominate _ _ _ M _ (actual_source_energy_budget z u zbox ubox unit k M)
    (source_expression_admitted (moyalNormalizedEnergy k))

theorem actual_literal_clock_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) (a : Fin 4) :
    FiniteBound (sourceEngine (k+1) a (Fin.last (k+1))) M (literalClockArray k a)
      (z,WithLp.toLp 2 u) :=
  finite_dominate _ _ _ M _ (actual_source_clock_budget z u zbox ubox unit k M a)
    (source_expression_admitted (normalizedClockExpression k a))

-- Python stage k takes energy k and the update clock generated at k-1.
theorem actual_literal_five_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) (positive : 0<k) (i : Fin 5) :
    FiniteBound (actualFiveSymbols k i) M (literalFiveArrays k i) (z,WithLp.toLp 2 u) := by
  cases k with
  | zero=>omega
  | succ k=>
    induction i using Fin.lastCases with
    | last=>simpa only [actualFiveSymbols,literalFiveArrays,Fin.lastCases_last] using
        actual_literal_energy_budget z u zbox ubox unit (k+1) M
    | cast a=>simpa only [actualFiveSymbols,literalFiveArrays,Fin.lastCases_castSucc,Nat.add_sub_cancel_right] using
        actual_literal_clock_budget z u zbox ubox unit k M a

def originalLiteralFiveArrays (labels : CacheLabels 0) (k : ℕ) (i : Fin 5) :
    PreparationVacuumCentralBudget.ArrayBound :=
  Fin.lastCases (literalExpressionArray (originalCacheEnergy labels k))
    (fun a=>literalExpressionArray (originalCacheClock labels k a)) i

theorem original_literal_five_nonnegative (labels : CacheLabels 0) (k : ℕ) (i : Fin 5) :
    Nonnegative (originalLiteralFiveArrays labels k i) := by
  induction i using Fin.lastCases with
  | last=>simpa only [originalLiteralFiveArrays,Fin.lastCases_last] using
      literalExpressionArray_nonnegative (originalCacheEnergy labels k)
  | cast a=>simpa only [originalLiteralFiveArrays,Fin.lastCases_castSucc] using
      literalExpressionArray_nonnegative (originalCacheClock labels k a)

theorem actual_original_literal_energy_budget (labels : CacheLabels 0) (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) :
    FiniteBound (sourceEngineEnergy k) M
      (literalExpressionArray (originalCacheEnergy labels k)) (z,WithLp.toLp 2 u) :=
  finite_dominate _ _ _ M _ (actual_original_energy_budget labels z u zbox ubox unit k M)
    (source_expression_admitted (originalCacheEnergy labels k))

theorem actual_original_literal_clock_budget (labels : CacheLabels 0) (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) (positive : 1≤k) (a : Fin 4) :
    FiniteBound (sourceEngine k a (Fin.last k)) M
      (literalExpressionArray (originalCacheClock labels k a)) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have bound:=actual_literal_expression_budget z u zbox ubox unit (originalCacheClock labels k a) M
  have germ : arenaEvaluate (originalCacheClock labels k a)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngine k a (Fin.last k) x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact originalCacheClock_source labels k positive a x h
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=bound m hm w
  rw [read,realCast_jet _ (sourceEngine_smooth k a (Fin.last k)) m w _ hx,
    Complex.norm_real,Real.norm_eq_abs] at result
  exact result

theorem actual_original_literal_five_budget (labels : CacheLabels 0) (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) (positive : 1≤k) (i : Fin 5) :
    FiniteBound (actualFiveSymbols k i) M (originalLiteralFiveArrays labels k i) (z,WithLp.toLp 2 u) := by
  induction i using Fin.lastCases with
  | last=>simpa only [actualFiveSymbols,originalLiteralFiveArrays,Fin.lastCases_last] using
      actual_original_literal_energy_budget labels z u zbox ubox unit k M
  | cast a=>simpa only [actualFiveSymbols,originalLiteralFiveArrays,Fin.lastCases_castSucc] using
      actual_original_literal_clock_budget labels z u zbox ubox unit k M positive a

end LowEnergy.PreparationVacuumLiteralFeed
