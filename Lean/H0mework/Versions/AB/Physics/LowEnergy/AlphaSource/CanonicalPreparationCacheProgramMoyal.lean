import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationCacheRows

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumSourceCacheProgram
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumArenaCollect
open PreparationVacuumMoyalNormalization PreparationVacuumArenaRows PreparationVacuumSourceCacheRules
open PreparationVacuumClockSymbol
open scoped BigOperators Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase

def originalRowPair {k : ℕ} (labels : CacheLabels k) (r : ℕ) (left right : Row k) : ArenaExpression k :=
  arenaProduct (.literal (rowNumber left*rowNumber right))
    (cachePairCore r (sourceLabel labels (rowOperand left)) (sourceLabel labels (rowOperand right)))

theorem originalRowPair_source {k : ℕ} (labels : CacheLabels k) (r : ℕ) (left right : Row k)
    (x : Phase) (hx : x∈poleDomain) : arenaEvaluate (originalRowPair labels r left right) x=
      complexMoyal r (arenaEvaluate (rowExpression left)) (arenaEvaluate (rowExpression right)) x := by
  rw [row_split left,row_split right,
    moyal_scale_left r _ _ _ (arena_smooth (rowOperand left))
      (contDiffOn_const.mul (arena_smooth (rowOperand right))) x hx,
    moyal_scale_right r _ _ _ (arena_smooth (rowOperand left)) (arena_smooth (rowOperand right)) x hx]
  rw [originalRowPair,arenaProduct_evaluate,cachePairCore_source]
  simp only [sourceLabel,arenaEvaluate_literal,Complex.ofReal_mul,mul_assoc]

def originalRightExpansion {k : ℕ} (labels : CacheLabels k) (r : ℕ) (left : Row k)
    (right : List (Row k)) : ArenaExpression k :=
  right.foldr (fun row out=>.add (originalRowPair labels r left row) out) (.literal 0)

def originalPairExpansion {k : ℕ} (labels : CacheLabels k) (r : ℕ)
    (left right : List (Row k)) : ArenaExpression k :=
  left.foldr (fun row out=>.add (originalRightExpansion labels r row right) out) (.literal 0)

theorem originalRightExpansion_source {k : ℕ} (labels : CacheLabels k) (r : ℕ)
    (left : Row k) (right : List (Row k)) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (originalRightExpansion labels r left right) x=
      complexMoyal r (arenaEvaluate (rowExpression left)) (arenaEvaluate (rowsExpression right)) x := by
  induction right with
  | nil=>simp only [originalRightExpansion,rowsExpression,List.foldr_nil,arenaEvaluate_literal,Complex.ofReal_zero,moyal_zero_right]
  | cons row rest ih=>
    simp only [originalRightExpansion,rowsExpression,List.foldr_cons,arenaEvaluate_add]
    change arenaEvaluate (originalRowPair labels r left row) x+
      arenaEvaluate (originalRightExpansion labels r left rest) x=_
    rw [originalRowPair_source labels r left row x hx,ih]
    exact (moyal_add_right r _ _ _ (arena_smooth _) (arena_smooth _) (arena_smooth _) x hx).symm

theorem originalPairExpansion_source {k : ℕ} (labels : CacheLabels k) (r : ℕ)
    (left right : List (Row k)) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (originalPairExpansion labels r left right) x=
      complexMoyal r (arenaEvaluate (rowsExpression left)) (arenaEvaluate (rowsExpression right)) x := by
  induction left with
  | nil=>simp only [originalPairExpansion,rowsExpression,List.foldr_nil,arenaEvaluate_literal,Complex.ofReal_zero,moyal_zero_left]
  | cons row rest ih=>
    simp only [originalPairExpansion,rowsExpression,List.foldr_cons,arenaEvaluate_add]
    change arenaEvaluate (originalRightExpansion labels r row right) x+
      arenaEvaluate (originalPairExpansion labels r rest right) x=_
    rw [originalRightExpansion_source labels r row right x hx,ih]
    exact (moyal_add_left r _ _ _ (arena_smooth _) (arena_smooth _) (arena_smooth _) x hx).symm

def originalSourceMoyal {k : ℕ} (labels : CacheLabels k) (r : ℕ)
    (left right : ArenaExpression k) : ArenaExpression k :=
  if r=0 then sourceCacheExpression labels (arenaProduct left right) else
    originalPairExpansion labels r (sourceCacheRows labels (sourceRows left)) (sourceCacheRows labels (sourceRows right))

theorem originalSourceMoyal_source {k : ℕ} (labels : CacheLabels k) (r : ℕ)
    (left right : ArenaExpression k) (x : Phase) (hx : x∈poleDomain) :
    arenaEvaluate (originalSourceMoyal labels r left right) x=
      complexMoyal r (arenaEvaluate left) (arenaEvaluate right) x := by
  unfold originalSourceMoyal
  split_ifs with zero
  · subst r
    rw [sourceCacheExpression_source _ _ x hx,arenaProduct_evaluate,complexMoyal_zero]
  · rw [originalPairExpansion_source _ _ _ _ x hx]
    apply moyal_germ
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,sourceCacheRows_source _ _ y hy,sourceRows_value _ y hy]
    · filter_upwards [poleDomain_open.mem_nhds hx] with y hy
      rw [rowsExpression_value,sourceCacheRows_source _ _ y hy,sourceRows_value _ y hy]

end LowEnergy.PreparationVacuumSourceCacheProgram
