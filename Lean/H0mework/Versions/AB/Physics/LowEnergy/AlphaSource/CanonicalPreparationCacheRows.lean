import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCacheMoyal

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceCacheRules
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaCollect
open PreparationVacuumMoyalNormalization PreparationVacuumArenaRows PreparationVacuumCentralBudget
open PreparationVacuumNumericSource PreparationVacuumClockSymbol PreparationVacuumEngineSource
open PreparationVacuumEngineSmooth
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology

abbrev CacheLabels (k : ℕ) := ArenaExpression k → ℕ×Bool

def sourceLabel {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) : AtomLabel k :=
  ⟨e,(labels e).1,(labels e).2⟩

def canonicalRow {k : ℕ} (labels : CacheLabels k) (row : Row k) : Row k :=
  orderedRow row.coefficient (row.word.map (sourceLabel labels))

theorem canonicalRow_source {k : ℕ} (labels : CacheLabels k) (row : Row k) (x : Phase) :
    rowValue (canonicalRow labels row) x=rowValue row x := by
  rw [canonicalRow,orderedRow_source]
  simp only [rowValue,wordValue,orderedProduct,List.map_map,Function.comp_def,sourceLabel,List.prod_eq_foldr]
  simp only [List.foldr_map]

theorem canonicalRows_source {k : ℕ} (labels : CacheLabels k) (rows : List (Row k)) (x : Phase) :
    rowsValue (rows.map (canonicalRow labels)) x=rowsValue rows x := by
  simp only [rowsValue,List.map_map,Function.comp_def,canonicalRow_source]

theorem zeroCoefficient_value (c : NormalizedCoefficient) (zero : c.numerator=0) (x : Phase) :
    coefficientValue c x=0 := by simp [coefficientValue,zero]

def dropZeroRows {k : ℕ} (rows : List (Row k)) : List (Row k) := by
  classical
  exact rows.filter (fun row=>decide (row.coefficient.numerator≠0))

theorem dropZeroRows_source {k : ℕ} (rows : List (Row k)) (x : Phase) :
    rowsValue (dropZeroRows rows) x=rowsValue rows x := by
  classical
  induction rows with
  | nil=>rfl
  | cons row rest ih=>
    by_cases zero : row.coefficient.numerator=0
    · simp only [dropZeroRows,List.filter_cons,zero,ne_eq,not_true_eq_false,decide_false,Bool.false_eq_true,
        if_false,rowsValue,List.map_cons,List.sum_cons] at ih ⊢
      have value : rowValue row x=0 := by simp only [rowValue,zeroCoefficient_value _ zero,Complex.ofReal_zero,zero_mul]
      rw [value,zero_add]
      exact ih
    · simp only [dropZeroRows,List.filter_cons,zero,ne_eq,not_false_eq_true,decide_true,if_true,
        rowsValue,List.map_cons,List.sum_cons] at ih ⊢
      rw [ih]

def sourceCacheRows {k : ℕ} (labels : CacheLabels k) (rows : List (Row k)) : List (Row k) :=
  dropZeroRows (collectRows (rows.map (canonicalRow labels)))

theorem sourceCacheRows_source {k : ℕ} (labels : CacheLabels k) (rows : List (Row k))
    (x : Phase) (hx : x∈poleDomain) : rowsValue (sourceCacheRows labels rows) x=rowsValue rows x := by
  rw [sourceCacheRows,dropZeroRows_source,collectRows_value _ x hx,canonicalRows_source]

def sourceCacheExpression {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k) : ArenaExpression k :=
  rowsExpression (sourceCacheRows labels (sourceRows e))

theorem sourceCacheExpression_source {k : ℕ} (labels : CacheLabels k) (e : ArenaExpression k)
    (x : Phase) (hx : x∈poleDomain) : arenaEvaluate (sourceCacheExpression labels e) x=arenaEvaluate e x := by
  rw [sourceCacheExpression,rowsExpression_value,sourceCacheRows_source _ _ x hx,sourceRows_value _ x hx]

def cachedEnergyExpression (labels : CacheLabels 0) (k : ℕ) : ArenaExpression 0 :=
  sourceCacheExpression labels (moyalNormalizedEnergy k)

theorem cachedEnergy_source (labels : CacheLabels 0) (k : ℕ) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (cachedEnergyExpression labels k) x=(sourceEngineEnergy k x : ℂ) := by
  rw [cachedEnergyExpression,sourceCacheExpression_source _ _ x hx,moyalNormalizedEnergy_source k x hx]

def cachedEnergyArray (labels : CacheLabels 0) (k : ℕ) : ArrayBound :=
  expressionArray sourcePrimitiveArrays (cachedEnergyExpression labels k)

theorem actual_cached_energy_budget (labels : CacheLabels 0) (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (k M : ℕ) :
    FiniteBound (sourceEngineEnergy k) M (cachedEnergyArray labels k) (z,WithLp.toLp 2 u) := by
  have hx:=PreparationVacuumClockBudget.sourceUnit_admitted z u zbox ubox unit
  have bound:=actual_source_expression_budget z u zbox ubox unit (cachedEnergyExpression labels k) M
  have germ : arenaEvaluate (cachedEnergyExpression labels k)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngineEnergy k x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact cachedEnergy_source labels k x h
  intro m hm w
  have read:=congrArg (fun D=>D (PreparationVacuumCanonicalMoyal.slotDirection∘w))
    ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=bound m hm w
  rw [read,realCast_jet _ (sourceEngineEnergy_smooth k) m w _ hx,Complex.norm_real,Real.norm_eq_abs] at result
  exact result

end LowEnergy.PreparationVacuumSourceCacheRules
