import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationCacheProgramMoyal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceCacheProgram
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaCollect
open PreparationVacuumMoyalNormalization PreparationVacuumArenaRows PreparationVacuumSourceCacheRules
open PreparationVacuumClockSymbol PreparationVacuumNumericSource PreparationVacuumEngineSource
open PreparationVacuumEngineSmooth PreparationVacuumCentralBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology
abbrev ArrayBound := PreparationVacuumCentralBudget.ArrayBound

def originalNormalize {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) : ArenaExpression k :=
  ArenaExpression.rec (motive_1:=fun _=>ArenaExpression k) (motive_2:=fun _=>List (ArenaExpression k))
    .literal .source .clock (fun r _ _ left right=>originalSourceMoyal labels r left right)
    (fun c _ word=>sourceCacheExpression labels (.row c word))
    (fun _ _ left right=>sourceCacheExpression labels (.add left right))
    [] (fun _ _ head tail=>head::tail) e

@[simp] theorem originalNormalize_moyal {k : ℕ} (labels : CacheLabels k) (r : ℕ) (e f : ArenaExpression k) :
    originalNormalize labels (.moyal r e f)=
      originalSourceMoyal labels r (originalNormalize labels e) (originalNormalize labels f) := rfl

@[simp] theorem originalNormalize_add {k : ℕ} (labels : CacheLabels k) (e f : ArenaExpression k) :
    originalNormalize labels (.add e f)=
      sourceCacheExpression labels (.add (originalNormalize labels e) (originalNormalize labels f)) := rfl

theorem originalNormalize_row {k : ℕ} (labels : CacheLabels k) (c : NormalizedCoefficient)
    (word : List (ArenaExpression k)) : originalNormalize labels (.row c word)=
      sourceCacheExpression labels (.row c (word.map (originalNormalize labels))) := by
  suffices same : ArenaExpression.rec_1
      (motive_1:=fun _=>ArenaExpression k) (motive_2:=fun _=>List (ArenaExpression k))
      .literal .source .clock (fun r _ _ left right=>originalSourceMoyal labels r left right)
      (fun c _ word=>sourceCacheExpression labels (.row c word))
      (fun _ _ left right=>sourceCacheExpression labels (.add left right))
      [] (fun _ _ head tail=>head::tail) word=word.map (originalNormalize labels) by
    exact congrArg (fun word=>sourceCacheExpression labels (.row c word)) same
  induction word with
  | nil=>rfl
  | cons e rest ih=>change originalNormalize labels e::_=originalNormalize labels e::rest.map (originalNormalize labels);rw [ih]

theorem originalNormalize_source {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) :
    ∀ x∈poleDomain,arenaEvaluate (originalNormalize labels e) x=arenaEvaluate e x := by
  refine ArenaExpression.rec
    (motive_1:=fun e=>∀ x∈poleDomain,arenaEvaluate (originalNormalize labels e) x=arenaEvaluate e x)
    (motive_2:=fun word=>∀ x∈poleDomain,
      orderedProduct ((word.map (originalNormalize labels)).map arenaEvaluate) x=orderedProduct (word.map arenaEvaluate) x)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ e
  · intro c x _;rfl
  · intro d j x _;rfl
  · intro l a x _;rfl
  · intro r e f he hf x hx
    rw [originalNormalize_moyal,originalSourceMoyal_source labels r _ _ x hx,arenaEvaluate_moyal]
    apply moyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact he y hy
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      exact hf y hy
  · intro c word ih x hx
    rw [originalNormalize_row,sourceCacheExpression_source _ _ x hx,arenaEvaluate_row,arenaEvaluate_row]
    have same:=ih x hx
    simp only [orderedProduct,List.foldr_map] at same
    simp only [List.foldr_map]
    rw [same]
  · intro e f he hf x hx
    rw [originalNormalize_add,sourceCacheExpression_source _ _ x hx]
    simp only [arenaEvaluate_add,he x hx,hf x hx]
  · intro x _;rfl
  · intro e word he ih x hx
    simp only [List.map_cons,orderedProduct,List.foldr_cons]
    have same:=ih x hx
    simp only [orderedProduct] at same
    rw [he x hx,same]

def originalCacheEnergy (labels : CacheLabels 0) (k : ℕ) : ArenaExpression 0 :=
  originalNormalize labels (arena_energy_expr k)

theorem originalCacheEnergy_source (labels : CacheLabels 0) (k : ℕ) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (originalCacheEnergy labels k) x=(sourceEngineEnergy k x : ℂ) := by
  rw [originalCacheEnergy,originalNormalize_source _ _ x hx]
  exact arena_energy_readback k x hx

def originalCacheClock (labels : CacheLabels 0) (k : ℕ) (a : Fin 4) : ArenaExpression 0 :=
  originalNormalize labels (arena_clock_definition_exprs (k-1) a)

theorem originalCacheClock_source (labels : CacheLabels 0) (k : ℕ) (positive : 1 ≤ k)
    (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (originalCacheClock labels k a) x=(sourceEngine k a (Fin.last k) x : ℂ) := by
  cases k with
  | zero=>omega
  | succ k=>
    rw [originalCacheClock,originalNormalize_source _ _ x hx]
    simpa only [Nat.add_sub_cancel_right] using arena_clock_definition_readback k a x hx

def originalEnergyArray (labels : CacheLabels 0) (k : ℕ) : ArrayBound :=
  expressionArray sourcePrimitiveArrays (originalCacheEnergy labels k)

theorem actual_original_energy_budget (labels : CacheLabels 0) (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) :
    FiniteBound (sourceEngineEnergy k) M (originalEnergyArray labels k) (z,WithLp.toLp 2 u) := by
  have hx:=PreparationVacuumClockBudget.sourceUnit_admitted z u zbox ubox unit
  have bound:=actual_source_expression_budget z u zbox ubox unit (originalCacheEnergy labels k) M
  have germ : arenaEvaluate (originalCacheEnergy labels k)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngineEnergy k x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact originalCacheEnergy_source labels k x h
  intro m hm w
  have read:=congrArg (fun D=>D (PreparationVacuumCanonicalMoyal.slotDirection∘w))
    ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=bound m hm w
  rw [read,realCast_jet _ (sourceEngineEnergy_smooth k) m w _ hx,Complex.norm_real,Real.norm_eq_abs] at result
  exact result

end LowEnergy.PreparationVacuumSourceCacheProgram
