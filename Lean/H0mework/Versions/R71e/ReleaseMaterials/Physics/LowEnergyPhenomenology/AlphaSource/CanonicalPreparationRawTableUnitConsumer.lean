import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRawTableStageArrays

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumRawTableBounds
open PreparationVacuumSharedPool PreparationVacuumExecutionGraph PreparationVacuumKernelValues
open PreparationVacuumDAGSemantic PreparationVacuumDAGCoefficient PreparationVacuumLiteralFeed
open PreparationVacuumNumericSource PreparationVacuumSourceSerialization PreparationVacuumArenaRows PreparationVacuumLiteralAdmission
open PreparationVacuumCentralBudget PreparationVacuumArenaBudget PreparationVacuumMoyalBudget
open PreparationVacuumClockBudget PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol
open PreparationVacuumEngineSource PreparationVacuumEngineSmooth PreparationVacuumEngineBudget PreparationVacuumTailSupport
open PreparationVacuumNativeMemo
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology

theorem clockArrays_preserved {small big : ℕ} (h : small ≤ big) (l : Fin (small+1)) (a : Fin 4) :
    clockArrays big (Fin.castLE (Nat.add_le_add_right h 1) l) a=clockArrays small l a := by
  induction h with
  | refl=>rfl
  | @step big h ih=>
    have index : Fin.castLE (Nat.add_le_add_right (Nat.le_succ_of_le h) 1) l=
        (Fin.castLE (Nat.add_le_add_right h 1) l).castSucc := by apply Fin.ext;rfl
    rw [index,clockArrays_previous,ih]

theorem clockArrays_agree {small big : ℕ} (h : small ≤ big) (state : RawArena) (range : ClockRange small state) :
    ClockAgreement state (clockArrays small) (clockArrays big) := by
  intro node member level axis kind
  have lower : level < small := by simpa only [kind,KindClockBelow] using range node member
  have upper : level < big := lt_of_lt_of_le lower h
  simp only [rawNodeBounds,dif_pos lower,dif_pos upper]
  exact (clockArrays_preserved h (Fin.succ ⟨level,lower⟩) axis).symm

theorem installFold_definition_length (k : ℕ) (ids : List ℕ) (axes : List (Fin 4))
    (out : RawClocks × List ℕ × List ℕ × RawRuntime) :
    (axes.foldl (installStep k ids) out).2.2.1.length=out.2.2.1.length+axes.length := by
  induction axes generalizing out with
  | nil=>simp only [List.foldl_nil,List.length_nil,Nat.add_zero]
  | cons a axes ih=>
    rw [List.foldl_cons,ih]
    change (out.2.2.1++[_]).length+axes.length=out.2.2.1.length+(a::axes).length
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

theorem originalInstalled_definition_length (k : ℕ) : (originalInstalledRun k).2.2.1.length=4 := by
  unfold originalInstalledRun
  rw [originalInstall_as_fold,installFold_definition_length]
  simp

theorem originalInstalled_definition_member (k : ℕ) (a : Fin 4) :
    (originalInstalledRun k).2.2.1.getD a.val 0∈(originalInstalledRun k).2.2.1 := by
  have valid : a.val < (originalInstalledRun k).2.2.1.length := by rw [originalInstalled_definition_length];exact a.isLt
  rw [List.getD_eq_getElem _ _ valid]
  exact List.getElem_mem _

theorem definitionArray_final_table (k later : ℕ) (h : k+1 ≤ later) (a : Fin 4) :
    rawTableBounds (clockArrays later) (originalEngine later).runtime.arena (originalFiveId k a.castSucc)=
      definitionArray k (clockArrays k) a := by
  have cached:=actual_installed_definition_values k
  have residual:=actual_residual_cached k k
  have support:=originalInstalled_definition_support k _ (originalInstalled_definition_member k a)
  have installedGrow:=originalInstall_grows k (residualHandles k) (originalEngine k).clocks (originalResidualRun k).2
  rw [originalFive_clock_definition,originalStageRecord_definition_ids,
    rawTableBounds_prefix (clockArrays later) ((originalInstalled_to_final k).trans (originalEngine_extends h))
      cached.1.handles.closed _ (list_getD_handle cached.1.handles cached.2.1 a.val)]
  exact (rawTableBounds_supported_agree (clockArrays k) (clockArrays later) (originalResidualRun k).2.arena
    (originalInstalledRun k).2.2.2.arena installedGrow residual.handles.closed cached.1.handles.closed
    (clockArrays_agree (by omega) _ (originalResidualRun_earlier_clocks k)) _ support).symm

theorem fiveArrays_final_table (k : ℕ) (i : Fin 5) :
    fiveArrays (k+1) i=rawTableBounds (clockArrays (k+1)) (originalEngine (k+1)).runtime.arena (originalFiveId k i) := by
  induction i using Fin.lastCases with
  | last=>rfl
  | cast a=>
    rw [fiveArrays,Fin.lastCases_castSucc,clockArrays_last]
    exact (definitionArray_final_table k (k+1) le_rfl a).symm

theorem clockLookup_definition_fold (level : ℕ) (ids : List ℕ) (axes : List (Fin 4)) (clocks : RawClocks) (n : ℕ) (a : Fin 4) :
    clockLookup (axes.foldl (fun defs axis=>clockInsert defs level axis (ids.getD axis.val 0)) clocks) n a=
      if n=level ∧ a∈axes then ids.getD a.val 0 else clockLookup clocks n a := by
  induction axes generalizing clocks with
  | nil=>simp only [List.foldl_nil,List.not_mem_nil,and_false,if_false]
  | cons axis axes ih=>
    rw [List.foldl_cons,ih,clockLookup_insert]
    by_cases hn : n=level
    · subst n
      by_cases present : a∈axes
      · simp [present]
      · by_cases same : axis=a
        · subst axis;simp [present]
        · simp [present,same,Ne.symm same]
    · simp [hn,Ne.symm hn]

theorem originalEngine_definitions_next (k : ℕ) :
    (originalEngine (k+1)).definitions=(List.finRange 4).foldl
      (fun defs a=>clockInsert defs (k+1) a ((originalInstalledRun k).2.2.1.getD a.val 0)) (originalEngine k).definitions := rfl

theorem actual_definition_lookup (k later : ℕ) (h : k+1 ≤ later) (a : Fin 4) :
    clockLookup (originalEngine later).definitions (k+1) a=originalFiveId k a.castSucc := by
  induction h with
  | refl=>
    rw [originalEngine_definitions_next,clockLookup_definition_fold,if_pos (by simp),
      originalFive_clock_definition,originalStageRecord_definition_ids]
  | @step later h ih=>
    have lower : k+1 ≤ later := h
    have outside : ¬ (k+1=later+1 ∧ a∈List.finRange 4) := by omega
    rw [originalEngine_definitions_next later,clockLookup_definition_fold,if_neg outside]
    exact ih

-- A clock node is resolved to the actual clock_def ID in this same final pool.
-- This is the original reference recursion, not a bound on an expanded tree.
theorem actual_clock_reference_equation (order level : ℕ) (bound : level < order) (a : Fin 4) :
    rawNodeBounds (clockArrays order) (rawTableBounds (clockArrays order) (originalEngine order).runtime.arena) (.clock level a)=
      rawTableBounds (clockArrays order) (originalEngine order).runtime.arena
        (clockLookup (originalEngine order).definitions (level+1) a) := by
  rw [actual_definition_lookup level order (by omega) a,definitionArray_final_table level order (by omega) a]
  simp only [rawNodeBounds,dif_pos bound]
  rw [←clockArrays_last]
  exact clockArrays_preserved (by omega) (Fin.last (level+1)) a

theorem original_stage_bounds_equation (k : ℕ) (i : Fin 5) :
    fiveArrays (k+1) i=rawBoundsStep (clockArrays (k+1)) (originalEngine (k+1)).runtime.arena
      (rawTableBounds (clockArrays (k+1)) (originalEngine (k+1)).runtime.arena) (originalFiveId k i) := by
  rw [fiveArrays_final_table,actual_stage_table_equation]

def originalTableB : ℕ → Fin 5 → ArrayBound := fiveArrays

theorem originalTableB_nonnegative (k : ℕ) (i : Fin 5) (m : ℕ) : 0 ≤ originalTableB k i m :=
  fiveArrays_nonnegative k i m

theorem original_table_unit_inputs (N : ℕ) : UnitEnergyInputs originalTableB N where
  coefficients:=by
    intro z zbox u ubox unit k positive
    cases k with
    | zero=>omega
    | succ k=>exact energyArray_budget z u zbox ubox unit k N

theorem original_table_unit_102 : UnitEnergyInputs originalTableB 102 := original_table_unit_inputs 102

end LowEnergy.PreparationVacuumRawTableBounds
