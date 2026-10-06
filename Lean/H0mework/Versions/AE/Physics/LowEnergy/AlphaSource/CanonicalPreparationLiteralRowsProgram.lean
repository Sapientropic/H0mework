import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationLiteralRowsCollect

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumLiteralRows
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaCollect
open PreparationVacuumMoyalNormalization PreparationVacuumArenaRows PreparationVacuumSourceCacheRules
open PreparationVacuumSourceCacheProgram PreparationVacuumClockSymbol PreparationVacuumNumericSource PreparationVacuumEngineSource
open PreparationVacuumEngineSmooth PreparationVacuumCentralBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology
abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound


def rationalSourceMoyal {k : ℕ} (labels : CacheLabels k) (r : ℕ)
    (left right : ArenaExpression k) : ArenaExpression k :=
  if r=0 then rationalExpression labels (arenaProduct left right) else
    originalPairExpansion labels r (rationalRows labels left) (rationalRows labels right)

theorem rationalSourceMoyal_source {k : ℕ} (labels : CacheLabels k) (r : ℕ)
    (left right : ArenaExpression k) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rationalSourceMoyal labels r left right) x=
      complexMoyal r (arenaEvaluate left) (arenaEvaluate right) x := by
  unfold rationalSourceMoyal
  split_ifs with zero
  · subst r
    rw [rationalExpression_source _ _ x hx,arenaProduct_evaluate,complexMoyal_zero]
  · rw [originalPairExpansion_source _ _ _ _ x hx]
    apply moyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,rationalRows_source _ _ y hy]
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,rationalRows_source _ _ y hy]

def rationalNormalize {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) : ArenaExpression k :=
  ArenaExpression.rec (motive_1:=fun _=>ArenaExpression k) (motive_2:=fun _=>List (ArenaExpression k))
    .literal .source .clock (fun r _ _ left right=>rationalSourceMoyal labels r left right)
    (fun c _ word=>rationalExpression labels (.row c word))
    (fun _ _ left right=>rationalExpression labels (.add left right))
    [] (fun _ _ head tail=>head::tail) e

@[simp] theorem rationalNormalize_moyal {k : ℕ} (labels : CacheLabels k) (r : ℕ) (e f : ArenaExpression k) :
    rationalNormalize labels (.moyal r e f)=
      rationalSourceMoyal labels r (rationalNormalize labels e) (rationalNormalize labels f) := rfl

@[simp] theorem rationalNormalize_add {k : ℕ} (labels : CacheLabels k) (e f : ArenaExpression k) :
    rationalNormalize labels (.add e f)=
      rationalExpression labels (.add (rationalNormalize labels e) (rationalNormalize labels f)) := rfl

theorem rationalNormalize_row {k : ℕ} (labels : CacheLabels k) (c : NormalizedCoefficient)
    (word : List (ArenaExpression k)) : rationalNormalize labels (.row c word)=
      rationalExpression labels (.row c (word.map (rationalNormalize labels))) := by
  suffices same : ArenaExpression.rec_1
      (motive_1:=fun _=>ArenaExpression k) (motive_2:=fun _=>List (ArenaExpression k))
      .literal .source .clock (fun r _ _ left right=>rationalSourceMoyal labels r left right)
      (fun c _ word=>rationalExpression labels (.row c word))
      (fun _ _ left right=>rationalExpression labels (.add left right))
      [] (fun _ _ head tail=>head::tail) word=word.map (rationalNormalize labels) by
    exact congrArg (fun word=>rationalExpression labels (.row c word)) same
  induction word with
  | nil=>rfl
  | cons e rest ih=>change rationalNormalize labels e::_=rationalNormalize labels e::rest.map (rationalNormalize labels);rw [ih]

theorem rationalNormalize_source {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) :
    ∀ x∈poleDomain,arenaEvaluate (rationalNormalize labels e) x=arenaEvaluate e x := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>∀ x∈poleDomain,arenaEvaluate (rationalNormalize labels e) x=arenaEvaluate e x)
    (motive_2:=fun word=>∀ x∈poleDomain,
      orderedProduct ((word.map (rationalNormalize labels)).map arenaEvaluate) x=orderedProduct (word.map arenaEvaluate) x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c x _;rfl
  · intro d j x _;rfl
  · intro l a x _;rfl
  · intro r e f he hf x hx
    rw [rationalNormalize_moyal,rationalSourceMoyal_source labels r _ _ x hx,arenaEvaluate_moyal]
    apply moyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact he y hy
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact hf y hy
  · intro c word ih x hx
    rw [rationalNormalize_row,rationalExpression_source _ _ x hx,arenaEvaluate_row,arenaEvaluate_row]
    have same:=ih x hx
    simp only [orderedProduct,List.foldr_map] at same
    simp only [List.foldr_map]
    rw [same]
  · intro e f he hf x hx
    rw [rationalNormalize_add,rationalExpression_source _ _ x hx]
    simp only [arenaEvaluate_add,he x hx,hf x hx]
  · intro x _;rfl
  · intro e word he ih x hx
    simp only [List.map_cons,orderedProduct,List.foldr_cons]
    have same:=ih x hx
    simp only [orderedProduct] at same
    rw [he x hx,same]

def rationalCacheEnergy (labels : CacheLabels 0) (k : ℕ) : ArenaExpression 0 :=
  rationalNormalize labels (arena_energy_expr k)

theorem rationalCacheEnergy_source (labels : CacheLabels 0) (k : ℕ) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rationalCacheEnergy labels k) x=(sourceEngineEnergy k x : ℂ) := by
  rw [rationalCacheEnergy,rationalNormalize_source _ _ x hx]
  exact arena_energy_readback k x hx

def rationalCacheClock (labels : CacheLabels 0) (k : ℕ) (a : Fin 4) : ArenaExpression 0 :=
  rationalNormalize labels (arena_clock_definition_exprs (k-1) a)

theorem rationalCacheClock_source (labels : CacheLabels 0) (k : ℕ) (positive : 1 ≤ k)
    (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (rationalCacheClock labels k a) x=(sourceEngine k a (Fin.last k) x : ℂ) := by
  cases k with
  | zero=>omega
  | succ k=>
    rw [rationalCacheClock,rationalNormalize_source _ _ x hx]
    simpa only [Nat.add_sub_cancel_right] using arena_clock_definition_readback k a x hx

def rationalEnergyArray (labels : CacheLabels 0) (k : ℕ) : ArrayBound :=
  expressionArray sourcePrimitiveArrays (rationalCacheEnergy labels k)

theorem actual_rational_energy_budget (labels : CacheLabels 0) (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) :
    FiniteBound (sourceEngineEnergy k) M (rationalEnergyArray labels k) (z,WithLp.toLp 2 u) := by
  have hx:=PreparationVacuumClockBudget.sourceUnit_admitted z u zbox ubox unit
  have bound:=actual_source_expression_budget z u zbox ubox unit (rationalCacheEnergy labels k) M
  have germ : arenaEvaluate (rationalCacheEnergy labels k)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngineEnergy k x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact rationalCacheEnergy_source labels k x h
  intro m hm w
  have read:=congrArg (fun D=>D (PreparationVacuumCanonicalMoyal.slotDirection∘w))
    ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=bound m hm w
  rw [read,realCast_jet _ (sourceEngineEnergy_smooth k) m w _ hx,Complex.norm_real,Real.norm_eq_abs] at result
  exact result

end LowEnergy.PreparationVacuumLiteralRows
