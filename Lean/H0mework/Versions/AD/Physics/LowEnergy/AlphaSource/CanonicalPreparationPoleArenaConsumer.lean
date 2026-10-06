import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationPoleCancelCoefficient
import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationUniformEnergyFeed

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumPoleCancellation
open PreparationVacuumDAGCoefficient PreparationVacuumDAGSemantic PreparationVacuumArenaRows
open PreparationVacuumCentralBudget PreparationVacuumCanonicalMoyal PreparationVacuumClockSymbol
open PreparationVacuumClockBudget PreparationVacuumEngineSource PreparationVacuumEngineBudget
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators Topology
abbrev Phase := PreparationVacuumCanonicalMoyal.Phase
abbrev ArrayBound := ℕ → ℝ

def canceledSourceArrays {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) : PrimitiveArrays 0 :=
  { sourceArrays central leaf with central:=fun c=>sourceCoefficientArray central (cancelCoefficient c) }

theorem canceledSourceArrays_nonnegative {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (positive : ∀ d j m,0 ≤ leaf d j m) :
    PrimitiveNonnegative (canceledSourceArrays central leaf) := by
  have original:=sourceArrays_nonnegative central leaf positive
  exact ⟨original.leaf,original.clock,fun c=>original.central (cancelCoefficient c)⟩

theorem actual_canceled_coefficient_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (central : PrimitiveInputs (z,WithLp.toLp 2 u) N) (c : NormalizedCoefficient) :
    FiniteBound (coefficientValue c) N (sourceCoefficientArray central (cancelCoefficient c)) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have germ : coefficientValue (cancelCoefficient c)=ᶠ[𝓝 (z,WithLp.toLp 2 u)] coefficientValue c := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact cancelCoefficient_source c x h
  intro m hm w
  have original:=actual_coefficient_budget z u zbox ubox unit N central (cancelCoefficient c) m hm w
  have read:=(germ.iteratedFDeriv ℝ m).eq_of_nhds
  simpa only [jet,read] using original

theorem canceledSourceArrays_bounds (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (central : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (leaf : Fin 3 → Fin 14 → ArrayBound)
    (bounds : ∀ d j,FiniteBound (originalLeaf d j) N (leaf d j) (z,WithLp.toLp 2 u)) :
    PrimitiveBounds (canceledSourceArrays central leaf) N (z,WithLp.toLp 2 u) := by
  have original:=sourceArrays_bounds z u zbox ubox unit N central leaf bounds
  exact ⟨original.leaf,original.clock,actual_canceled_coefficient_budget z u zbox ubox unit N central⟩

def canceledEnergyArray {x : Phase} {N : ℕ} (central : PrimitiveInputs x N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (k : ℕ) : ArrayBound :=
  expressionArray (canceledSourceArrays central leaf) (arena_energy_expr k)

theorem actual_canceled_energy_budget (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i|≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i|≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (central : PrimitiveInputs (z,WithLp.toLp 2 u) N)
    (leaf : Fin 3 → Fin 14 → ArrayBound) (positive : ∀ d j m,0 ≤ leaf d j m)
    (bounds : ∀ d j,FiniteBound (originalLeaf d j) N (leaf d j) (z,WithLp.toLp 2 u))
    (k M : ℕ) (paid : derivativeDemand (arena_energy_expr k) M≤N) :
    FiniteBound (sourceEngineEnergy k) M (canceledEnergyArray central leaf k) (z,WithLp.toLp 2 u) := by
  have hx:=sourceUnit_admitted z u zbox ubox unit
  have actual:=actual_expression_budget (canceledSourceArrays central leaf)
    (canceledSourceArrays_nonnegative central leaf positive) N _ hx
    (canceledSourceArrays_bounds z u zbox ubox unit N central leaf bounds) (arena_energy_expr k) M paid
  have germ : arenaEvaluate (arena_energy_expr k)=ᶠ[𝓝 (z,WithLp.toLp 2 u)]
      (fun x=>(sourceEngineEnergy k x : ℂ)) := by
    filter_upwards [poleDomain_open.mem_nhds hx] with x h
    exact arena_energy_readback k x h
  intro m hm w
  have read:=congrArg (fun D=>D (slotDirection∘w)) ((germ.iteratedFDeriv ℝ m).eq_of_nhds)
  have result:=actual m hm w
  rw [read,realCast_jet _ (PreparationVacuumEngineSmooth.sourceEngineEnergy_smooth k) m w _ hx,
    Complex.norm_real,Real.norm_eq_abs] at result
  exact result

end LowEnergy.PreparationVacuumPoleCancellation
