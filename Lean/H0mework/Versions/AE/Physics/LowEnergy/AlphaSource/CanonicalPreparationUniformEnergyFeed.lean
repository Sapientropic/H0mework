import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationUniformPrincipalLeaves

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumUniformFeed
open PreparationVacuumPrincipalBudget PreparationVacuumCentralBudget PreparationVacuumClockBudget
open PreparationVacuumClockJacobian PreparationVacuumClockSymbol PreparationVacuumDAGCoefficient
open PreparationVacuumCanonicalMoyal PreparationVacuumEngineBudget PreparationVacuumArenaRows
open PreparationVacuumDAGSemantic PreparationVacuumEngineSource
open CanonicalPreparationCutoff CanonicalPreparationSquareCutoff
open scoped BigOperators ContDiff Topology

-- Only degree0/1 is returned by the lower-leaf payer: degree2 is generated above.
structure LowerInputs (x : Phase) (N : ℕ) where
  array : Fin 2 → Fin 14 → ArrayBound
  nonnegative : ∀ d j m,0 ≤ array d j m
  bounds : ∀ d j,FiniteBound (originalLeaf (Fin.castSucc d) j) N (array d j) x

def fullLeafArrays {x : Phase} {N : ℕ} (lower : LowerInputs x N) (d : Fin 3) (j : Fin 14) : ArrayBound :=
  Fin.lastCases (principalLeafArray j) (fun e=>lower.array e j) d

theorem fullLeafArrays_nonnegative {x : Phase} {N : ℕ} (lower : LowerInputs x N)
    (d : Fin 3) (j : Fin 14) (m : ℕ) : 0 ≤ fullLeafArrays lower d j m := by
  refine Fin.lastCases ?_ (fun e=>?_) d
  · exact principalLeafArray_nonnegative j m
  · simpa only [fullLeafArrays,Fin.lastCases_castSucc] using lower.nonnegative e j m

theorem fullLeafArrays_bounds (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (coefficients : CoefficientInputs (z,WithLp.toLp 2 u) N)
    (lower : LowerInputs (z,WithLp.toLp 2 u) N) (d : Fin 3) (j : Fin 14) :
    FiniteBound (originalLeaf d j) N (fullLeafArrays lower d j) (z,WithLp.toLp 2 u) := by
  refine Fin.lastCases ?_ (fun e=>?_) d
  · exact actual_principalLeaf_budget _ (sourceUnit_admitted z u zbox ubox unit) zbox unit N coefficients j
  · simpa only [fullLeafArrays,Fin.lastCases_castSucc] using lower.bounds e j

def actualEnergyArray (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (coefficients : CoefficientInputs (z,WithLp.toLp 2 u) N)
    (lower : LowerInputs (z,WithLp.toLp 2 u) N) (k : ℕ) : ArrayBound :=
  generatedEnergyArray (actualCentralInputs z u zbox ubox unit N coefficients) (fullLeafArrays lower) k

def actualClockArray (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (coefficients : CoefficientInputs (z,WithLp.toLp 2 u) N)
    (lower : LowerInputs (z,WithLp.toLp 2 u) N) (k : ℕ) (a : Fin 4) : ArrayBound :=
  generatedClockArray (actualCentralInputs z u zbox ubox unit N coefficients) (fullLeafArrays lower) k a

theorem actual_energy_source_feed (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (coefficients : CoefficientInputs (z,WithLp.toLp 2 u) N)
    (lower : LowerInputs (z,WithLp.toLp 2 u) N) (k m : ℕ)
    (paid : derivativeDemand (arena_energy_expr k) m≤N) :
    FiniteBound (sourceEngineEnergy k) m
      (actualEnergyArray z u zbox ubox unit N coefficients lower k) (z,WithLp.toLp 2 u) :=
  actual_generated_energy_budget z u zbox ubox unit N
    (actualCentralInputs z u zbox ubox unit N coefficients) (fullLeafArrays lower)
    (fullLeafArrays_nonnegative lower) (fullLeafArrays_bounds z u zbox ubox unit N coefficients lower) k m paid

theorem actual_clock_source_feed (z u : FlatConfiguration)
    (zbox : ∀ i,|z i-flatSource i| ≤ sourceRadius)
    (ubox : ∀ i,|u i-sourceUnitMomentum i| ≤ sourceRadius)
    (unit : (∑ i : Fin 100,u i^2)=1) (N : ℕ)
    (coefficients : CoefficientInputs (z,WithLp.toLp 2 u) N)
    (lower : LowerInputs (z,WithLp.toLp 2 u) N) (k m : ℕ) (a : Fin 4)
    (paid : derivativeDemand (arena_clock_definition_exprs k a) m≤N) :
    FiniteBound (sourceEngine (k+1) a (Fin.last (k+1))) m
      (actualClockArray z u zbox ubox unit N coefficients lower k a) (z,WithLp.toLp 2 u) :=
  actual_generated_clock_budget z u zbox ubox unit N
    (actualCentralInputs z u zbox ubox unit N coefficients) (fullLeafArrays lower)
    (fullLeafArrays_nonnegative lower) (fullLeafArrays_bounds z u zbox ubox unit N coefficients lower) k m a paid

end LowEnergy.PreparationVacuumUniformFeed
