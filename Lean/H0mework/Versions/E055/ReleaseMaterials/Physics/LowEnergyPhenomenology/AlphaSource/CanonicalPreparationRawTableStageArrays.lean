import H0mework.Versions.E055.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRawTableFold

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
open PreparationVacuumEngineSource PreparationVacuumEngineSmooth PreparationVacuumEngineBudget
open PreparationVacuumNativeMemo
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology

-- The array of each new clock is read from its actual definition handle before
-- extending the clock-reference environment. Energy then uses that extension.
def definitionArray (k : ℕ) (previous : ClockBounds k) (a : Fin 4) : ArrayBound :=
  rawTableBounds previous (originalInstalledRun k).2.2.2.arena ((originalInstalledRun k).2.2.1.getD a.val 0)

def clockArrays (k : ℕ) : ClockBounds k :=
  Nat.rec (motive:=fun k=>ClockBounds k) literalPrimitiveArrays.clock
    (fun k previous=>Fin.lastCases (definitionArray k previous) previous) k

@[simp] theorem clockArrays_last (k : ℕ) (a : Fin 4) :
    clockArrays (k+1) (Fin.last (k+1)) a=definitionArray k (clockArrays k) a := by
  simp only [clockArrays,Fin.lastCases_last]

@[simp] theorem clockArrays_previous (k : ℕ) (l : Fin (k+1)) (a : Fin 4) :
    clockArrays (k+1) l.castSucc a=clockArrays k l a := by
  simp only [clockArrays,Fin.lastCases_castSucc]

def energyArray : ℕ → ArrayBound
  | 0=>constantArray 0
  | k+1=>rawTableBounds (clockArrays (k+1)) (originalEngine (k+1)).runtime.arena (originalFiveId k (Fin.last 4))

def fiveArrays (order : ℕ) (i : Fin 5) : ArrayBound :=
  Fin.lastCases (energyArray order) (fun a=>clockArrays order (Fin.last order) a) i

theorem clockArrays_nonnegative (k : ℕ) : ∀ l a,Nonnegative (clockArrays k l a) := by
  induction k with
  | zero=>exact literal_primitive_nonnegative.clock
  | succ k ih=>
    intro l a
    induction l using Fin.lastCases with
    | last=>rw [clockArrays_last];exact rawTableBounds_nonnegative _ ih _ _
    | cast l=>simpa only [clockArrays_previous] using ih l a

theorem energyArray_nonnegative (order : ℕ) : Nonnegative (energyArray order) := by
  cases order with
  | zero=>intro m;simp [energyArray,constantArray]
  | succ k=>exact rawTableBounds_nonnegative _ (clockArrays_nonnegative (k+1)) _ _

theorem fiveArrays_nonnegative (order : ℕ) (i : Fin 5) : Nonnegative (fiveArrays order i) := by
  induction i using Fin.lastCases with
  | last=>exact energyArray_nonnegative order
  | cast a=>simpa only [fiveArrays,Fin.lastCases_castSucc] using clockArrays_nonnegative order (Fin.last order) a

theorem installed_definition_native (K k : ℕ) (bound : k ≤ K) (a : Fin 4) (x : Phase) (hx : x∈poleDomain) :
    nativePolynomial K (originalInstalledRun k).2.2.2.arena ((originalInstalledRun k).2.2.1.getD a.val 0) x=
      (sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ) := by
  have generated:=originalInstall_definition_values K k (residualHandles k) (originalEngine k).clocks (originalResidualRun k).2
    (actual_residual_cached K k) (actual_residual_handles k)
  have same : (originalInstalledRun k).2.2.1.map (fun id=>nativePolynomial K (originalInstalledRun k).2.2.2.arena id x)=
      (List.finRange 4).map (fun a=>correctionRead K (originalResidualRun k).2.arena (residualHandles k) a x) := generated.2.2 x hx
  rw [native_getD_value K (originalInstalledRun k).2.2.2.arena _ _ generated.1.handles.closed generated.1.handles.initialized a.val x same]
  rw [←List.ofFn_eq_map,List.getD_eq_getElem _ _ (by rw [List.length_ofFn];exact a.isLt),List.getElem_ofFn,
    sourceEngine_generated_normalized k a x hx]
  unfold correctionRead
  simp only [Complex.ofReal_sum,Complex.ofReal_mul]
  apply Finset.sum_congr rfl
  intro b _
  rw [actual_residual_value K k bound b x hx]

theorem source_table_primitives {k : ℕ} (previous : ClockBounds k) (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (N : ℕ) (clockPaid : ∀ l a,FiniteBound (sourceEngine k a l) N (previous l a) (z,WithLp.toLp 2 u)) :
    PrimitiveBounds (tablePrimitives previous) N (z,WithLp.toLp 2 u) := by
  have paid:=literal_primitive_bounds z u zbox ubox unit N
  exact ⟨paid.leaf,clockPaid,paid.central⟩

theorem clockArrays_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (k : ℕ) : ∀ N l a,FiniteBound (sourceEngine k a l) N (clockArrays k l a) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  induction k with
  | zero=>intro N;exact (literal_primitive_bounds z u zbox ubox unit N).clock
  | succ k ih=>
    intro N l a
    induction l using Fin.lastCases with
    | cast l=>
      rw [sourceEngine_preserves,clockArrays_previous]
      exact ih N l a
    | last=>
      rw [clockArrays_last]
      let state:=(originalInstalledRun k).2.2.2.arena
      let id:=(originalInstalledRun k).2.2.1.getD a.val 0
      have bound:=rawTableBounds_budget (clockArrays k) (clockArrays_nonnegative k) state id (z,WithLp.toLp 2 u) hx N
        (source_table_primitives _ z u zbox ubox unit _ (ih _))
      have germ : nativePolynomial k state id=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
          (fun x=>(sourceEngine (k+1) a (Fin.last (k+1)) x : ℂ)) := by
        filter_upwards [poleDomain_open.mem_nhds hx] with x h
        exact installed_definition_native k k le_rfl a x h
      intro m hm w
      have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
      have result:=bound m hm w
      rw [read,realCast_jet _ (sourceEngine_smooth (k+1) a (Fin.last (k+1))) m w _ hx,
        Complex.norm_real,Real.norm_eq_abs] at result
      exact result

theorem energyArray_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (k N : ℕ) : FiniteBound (sourceEngineEnergy (k+1)) N (energyArray (k+1)) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have bound:=rawTableBounds_budget (clockArrays (k+1)) (clockArrays_nonnegative (k+1))
    (originalEngine (k+1)).runtime.arena (originalFiveId k (Fin.last 4)) (z,WithLp.toLp 2 u) hx N
    (source_table_primitives _ z u zbox ubox unit _ (clockArrays_budget z u zbox ubox unit (k+1) _))
  have germ : originalFiveNative k (Fin.last 4)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngineEnergy (k+1) x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact originalFiveNative_energy k x h
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=bound m hm w
  change ‖iteratedFDeriv ℝ m (originalFiveNative k (Fin.last 4)) (z,WithLp.toLp 2 u) (slotDirection∘w)‖ ≤ _ at result
  rw [read,realCast_jet _ (sourceEngineEnergy_smooth (k+1)) m w _ hx,Complex.norm_real,Real.norm_eq_abs] at result
  exact result

theorem fiveArrays_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius) (unit : (∑ i : Fin 100,u i^2)=1)
    (k N : ℕ) (i : Fin 5) : FiniteBound (actualFiveSymbols (k+1) i) N (fiveArrays (k+1) i) (z,WithLp.toLp 2 u) := by
  induction i using Fin.lastCases with
  | last=>exact energyArray_budget z u zbox ubox unit k N
  | cast a=>simpa only [actualFiveSymbols,fiveArrays,Fin.lastCases_castSucc] using clockArrays_budget z u zbox ubox unit (k+1) N (Fin.last (k+1)) a

end LowEnergy.PreparationVacuumRawTableBounds
