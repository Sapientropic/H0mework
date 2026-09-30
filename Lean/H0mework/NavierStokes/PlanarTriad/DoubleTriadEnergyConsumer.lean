import H0mework.NavierStokes.PlanarTriad.DoubleTriadNestedResidualTransport

/-!
# Two adjacent scale traces and their energy consumers

This module reads the two native traces of the connected double triad without
merging their responsibilities:

* the `P₅ → P₂` trace is paired with the `P₂` kinetic-energy differential;
* the `full → P₅` trace is paired with the `P₅` kinetic-energy differential.

The componentwise energy map commutes with both keeps on the complete
three-component residual carrier.  At the fixed source

```text
(1, 1, -1, 1/2)
```

the actual path generates adjacent fluxes `1/5` and `2/25`.  Independent
shell-energy budgets then show positive middle- and upper-shell energy rates
at viscosity `1/100`.  Positivity and kernel escape are conclusions, not
producer fields.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadEnergyConsumer

noncomputable section

open AffineRelaxation
open ResidualProjection
open TwoDimensionalVorticityDoubleTriadActual
open TwoDimensionalVorticityDoubleTriadNestedResidualTransport

local instance doubleTriadScaleQuiverLocal :
    Quiver DoubleTriadState :=
  doubleTriadScaleQuiver

/-! ## Actual kinetic-energy differentials and conservation checks -/

def doubleTriadLowKineticEnergy
    (state : DoubleTriadState) : ℚ :=
  state 0 ^ 2 + state 1 ^ 2 / 2

def doubleTriadMiddleKineticEnergy
    (state : DoubleTriadState) : ℚ :=
  state 0 ^ 2 + state 1 ^ 2 / 2 + state 2 ^ 2 / 5

def doubleTriadFullKineticEnergy
    (state : DoubleTriadState) : ℚ :=
  state 0 ^ 2 + state 1 ^ 2 / 2 +
    state 2 ^ 2 / 5 + state 3 ^ 2 / 10

def doubleTriadLowEnergyDifferential
    (state : DoubleTriadState) :
    DoubleTriadState →ₗ[ℚ] ℚ where
  toFun tangent :=
    2 * state 0 * tangent 0 + state 1 * tangent 1
  map_add' := by
    intro left right
    simp
    ring
  map_smul' := by
    intro scalar tangent
    simp
    ring

def doubleTriadMiddleEnergyDifferential
    (state : DoubleTriadState) :
    DoubleTriadState →ₗ[ℚ] ℚ where
  toFun tangent :=
    2 * state 0 * tangent 0 +
      state 1 * tangent 1 +
        (2 / 5 : ℚ) * state 2 * tangent 2
  map_add' := by
    intro left right
    simp
    ring
  map_smul' := by
    intro scalar tangent
    simp
    ring

def doubleTriadFullEnergyDifferential
    (state : DoubleTriadState) :
    DoubleTriadState →ₗ[ℚ] ℚ where
  toFun tangent :=
    2 * state 0 * tangent 0 +
      state 1 * tangent 1 +
        (2 / 5 : ℚ) * state 2 * tangent 2 +
          (1 / 5 : ℚ) * state 3 * tangent 3
  map_add' := by
    intro left right
    simp
    ring
  map_smul' := by
    intro scalar tangent
    simp
    ring

theorem doubleTriadFullKineticEnergy_add_smul
    (state tangent : DoubleTriadState) (step : ℚ) :
    doubleTriadFullKineticEnergy (state + step • tangent) =
      doubleTriadFullKineticEnergy state +
        step * doubleTriadFullEnergyDifferential state tangent +
        step ^ 2 * doubleTriadFullKineticEnergy tangent := by
  simp [doubleTriadFullKineticEnergy,
    doubleTriadFullEnergyDifferential]
  ring

theorem doubleTriadNonlinear_fullEnergyRate_zero
    (state : DoubleTriadState) :
    doubleTriadFullEnergyDifferential state
        (doubleTriadNonlinearGenerator state) = 0 := by
  rw [doubleTriadNonlinearGenerator_coordinates]
  simp [doubleTriadFullEnergyDifferential]
  ring

def doubleTriadFullEnstrophyDifferential
    (state : DoubleTriadState) :
    DoubleTriadState →ₗ[ℚ] ℚ where
  toFun tangent :=
    2 * state 0 * tangent 0 +
      2 * state 1 * tangent 1 +
        2 * state 2 * tangent 2 +
          2 * state 3 * tangent 3
  map_add' := by
    intro left right
    simp
    ring
  map_smul' := by
    intro scalar tangent
    simp
    ring

theorem doubleTriadNonlinear_fullEnstrophyRate_zero
    (state : DoubleTriadState) :
    doubleTriadFullEnstrophyDifferential state
        (doubleTriadNonlinearGenerator state) = 0 := by
  rw [doubleTriadNonlinearGenerator_coordinates]
  simp [doubleTriadFullEnstrophyDifferential]
  ring

/-! ## The two native fluxes -/

/-- Flux from the `P₂` band into the middle `|k|²=5` pair. -/
def doubleTriadMiddleFlux
    (ν : ℚ) (state : DoubleTriadState) : ℚ :=
  -doubleTriadLowEnergyDifferential state
    (doubleTriadMiddleTrace ν state)

/-- Flux from the `P₅` band into the upper `|k|²=10` pair. -/
def doubleTriadUpperFlux
    (ν : ℚ) (state : DoubleTriadState) : ℚ :=
  -doubleTriadMiddleEnergyDifferential state
    (doubleTriadUpperTrace ν state)

theorem doubleTriadMiddleFlux_eq
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadMiddleFlux ν state =
      -(state 0 * state 1 * state 2) / 5 := by
  rw [doubleTriadMiddleFlux,
    doubleTriadMiddleTrace_coordinates]
  simp [doubleTriadLowEnergyDifferential]
  ring

theorem doubleTriadUpperFlux_eq
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadUpperFlux ν state =
      -(4 * state 0 * state 2 * state 3) / 25 := by
  rw [doubleTriadUpperFlux,
    doubleTriadUpperTrace_coordinates]
  simp [doubleTriadMiddleEnergyDifferential]
  ring

def doubleTriadDirectLowFlux
    (ν : ℚ) (state : DoubleTriadState) : ℚ :=
  -doubleTriadLowEnergyDifferential state
    (doubleTriadDirectLowCommutator ν state)

theorem doubleTriadDirectLowFlux_telescope
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadDirectLowFlux ν state =
      doubleTriadMiddleFlux ν state -
        doubleTriadLowEnergyDifferential state
          (doubleTriadLowPass
            (doubleTriadUpperTrace ν state)) := by
  rw [doubleTriadDirectLowFlux,
    doubleTriadDirectLowCommutator_telescope,
    map_add, doubleTriadMiddleFlux]
  ring

/-! ## Independent shell-energy consumers -/

def doubleTriadMiddleShellEnergyRate
    (state tangent : DoubleTriadState) : ℚ :=
  (2 / 5 : ℚ) * state 2 * tangent 2

def doubleTriadUpperShellEnergyRate
    (state tangent : DoubleTriadState) : ℚ :=
  (1 / 5 : ℚ) * state 3 * tangent 3

/-- The middle adjacent trace is consumed by the actual `P₅` shell budget. -/
theorem doubleTriadMiddleShellEnergy_afterMiddlePass_exact_budget
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadMiddleShellEnergyRate state
        (doubleTriadNavierStokesGalerkinGenerator ν
          (doubleTriadMiddlePass state)) =
      doubleTriadMiddleFlux ν state -
        2 * ν * state 2 ^ 2 := by
  rw [doubleTriadMiddleFlux_eq]
  simp [doubleTriadMiddleShellEnergyRate,
    doubleTriadMiddlePass,
    doubleTriadNavierStokesGalerkinGenerator,
    doubleTriadNonlinearGenerator_coordinates,
    doubleTriadViscousGenerator]
  ring

/-- The upper adjacent trace is consumed by the actual top-shell budget. -/
theorem doubleTriadUpperShellEnergy_exact_budget
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadUpperShellEnergyRate state
        (doubleTriadNavierStokesGalerkinGenerator ν state) =
      doubleTriadUpperFlux ν state -
        2 * ν * state 3 ^ 2 := by
  rw [doubleTriadUpperFlux_eq]
  simp [doubleTriadUpperShellEnergyRate,
    doubleTriadNavierStokesGalerkinGenerator,
    doubleTriadNonlinearGenerator_coordinates,
    doubleTriadViscousGenerator]
  ring

theorem doubleTriadLowEnergy_afterMiddlePass_exact_budget
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadLowEnergyDifferential state
        (doubleTriadNavierStokesGalerkinGenerator ν
          (doubleTriadMiddlePass state)) =
      -doubleTriadMiddleFlux ν state -
        2 * ν * (state 0 ^ 2 + state 1 ^ 2) := by
  rw [doubleTriadMiddleFlux_eq]
  simp [doubleTriadLowEnergyDifferential,
    doubleTriadMiddlePass,
    doubleTriadNavierStokesGalerkinGenerator,
    doubleTriadNonlinearGenerator_coordinates,
    doubleTriadViscousGenerator]
  ring

theorem doubleTriadMiddleEnergy_exact_budget
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadMiddleEnergyDifferential state
        (doubleTriadNavierStokesGalerkinGenerator ν state) =
      -doubleTriadUpperFlux ν state -
        2 * ν *
          (state 0 ^ 2 + state 1 ^ 2 + state 2 ^ 2) := by
  rw [doubleTriadUpperFlux_eq]
  simp [doubleTriadMiddleEnergyDifferential,
    doubleTriadNavierStokesGalerkinGenerator,
    doubleTriadNonlinearGenerator_coordinates,
    doubleTriadViscousGenerator]
  ring

theorem doubleTriadFullEnergy_exact_budget
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadFullEnergyDifferential state
        (doubleTriadNavierStokesGalerkinGenerator ν state) =
      -2 * ν *
        (state 0 ^ 2 + state 1 ^ 2 +
          state 2 ^ 2 + state 3 ^ 2) := by
  simp [doubleTriadFullEnergyDifferential,
    doubleTriadNavierStokesGalerkinGenerator,
    doubleTriadNonlinearGenerator_coordinates,
    doubleTriadViscousGenerator]
  ring

/-! ## Whole-carrier energy transport -/

abbrev DoubleTriadNestedEnergyLedger := ℚ × ℚ × ℚ

def doubleTriadEnergyMiddleKeep :
    DoubleTriadNestedEnergyLedger →ₗ[ℚ]
      DoubleTriadNestedEnergyLedger where
  toFun ledger := (ledger.1, ledger.2.1, 0)
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro scalar ledger
    ext <;> simp

def doubleTriadEnergyLowKeep :
    DoubleTriadNestedEnergyLedger →ₗ[ℚ]
      DoubleTriadNestedEnergyLedger where
  toFun ledger := (ledger.1, 0, 0)
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro scalar ledger
    ext <;> simp

/-- Componentwise physical energy-work readout.  It retains the upper trace
on its native `P₅` energy differential. -/
def doubleTriadNestedEnergyMap
    (state : DoubleTriadState) :
    DoubleTriadNestedLedger →ₗ[ℚ]
      DoubleTriadNestedEnergyLedger where
  toFun ledger :=
    (doubleTriadLowEnergyDifferential state ledger.1,
      doubleTriadLowEnergyDifferential state ledger.2.1,
      doubleTriadMiddleEnergyDifferential state ledger.2.2)
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro scalar ledger
    ext <;> simp

theorem doubleTriadNestedEnergyMap_middleKeep_commutes
    (state : DoubleTriadState)
    (ledger : DoubleTriadNestedLedger) :
    doubleTriadNestedEnergyMap state
        (doubleTriadMiddleKeep ledger) =
      doubleTriadEnergyMiddleKeep
        (doubleTriadNestedEnergyMap state ledger) := by
  ext <;>
    simp [doubleTriadNestedEnergyMap,
      doubleTriadMiddleKeep, doubleTriadEnergyMiddleKeep]

theorem doubleTriadNestedEnergyMap_lowKeep_commutes
    (state : DoubleTriadState)
    (ledger : DoubleTriadNestedLedger) :
    doubleTriadNestedEnergyMap state
        (doubleTriadLowKeep ledger) =
      doubleTriadEnergyLowKeep
        (doubleTriadNestedEnergyMap state ledger) := by
  ext <;>
    simp [doubleTriadNestedEnergyMap,
      doubleTriadLowKeep, doubleTriadEnergyLowKeep]

def doubleTriadEnergyEdgeKeep
    {source target : DoubleTriadState}
    (edge : DoubleTriadScaleEdge source target) :
    DoubleTriadNestedEnergyLedger →ₗ[ℚ]
      DoubleTriadNestedEnergyLedger :=
  match edge with
  | .middle => doubleTriadEnergyMiddleKeep
  | .low => doubleTriadEnergyLowKeep

/-- Energy readout of the same actual scale quiver, fixed at the concrete
source event used below. -/
def canonicalDoubleTriadEnergyPathTransport
    (ν : ℚ) :
    PathIndexedResidualTransport ℚ
      DoubleTriadNestedEnergyLedger DoubleTriadState where
  residual := fun state =>
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
      (doubleTriadNestedResidual ν state)
  edgeKeep := doubleTriadEnergyEdgeKeep
  edge_residual_transport := by
    intro source target edge
    change DoubleTriadScaleEdge source target at edge
    cases edge with
    | middle =>
        change
          doubleTriadNestedEnergyMap canonicalDoubleTriadSource
              (doubleTriadNestedResidual ν
                (doubleTriadMiddlePass source)) =
            doubleTriadEnergyMiddleKeep
              (doubleTriadNestedEnergyMap
                canonicalDoubleTriadSource
                (doubleTriadNestedResidual ν source))
        rw [doubleTriadNestedResidual_middlePass]
        exact
          doubleTriadNestedEnergyMap_middleKeep_commutes
            canonicalDoubleTriadSource _
    | low =>
        change
          doubleTriadNestedEnergyMap canonicalDoubleTriadSource
              (doubleTriadNestedResidual ν
                (doubleTriadLowPass source)) =
            doubleTriadEnergyLowKeep
              (doubleTriadNestedEnergyMap
                canonicalDoubleTriadSource
                (doubleTriadNestedResidual ν source))
        rw [doubleTriadNestedResidual_lowPass]
        exact
          doubleTriadNestedEnergyMap_lowKeep_commutes
            canonicalDoubleTriadSource _

/-- U2: the energy readout is a concrete morphism on the complete residual
carrier and the same native scale path. -/
def canonicalDoubleTriadEnergyPathMorphism
    (ν : ℚ) :
    PathIndexedResidualTransport.Morphism
      (doubleTriadNestedPathTransport ν)
      (canonicalDoubleTriadEnergyPathTransport ν) where
  quiverMap := Prefunctor.id DoubleTriadState
  carrierMap :=
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
  residual_naturality := by
    intro state
    rfl
  edge_keep_naturality := by
    intro source target edge ledger
    change DoubleTriadScaleEdge source target at edge
    cases edge with
    | middle =>
        exact
          doubleTriadNestedEnergyMap_middleKeep_commutes
            canonicalDoubleTriadSource ledger
    | low =>
        exact
          doubleTriadNestedEnergyMap_lowKeep_commutes
            canonicalDoubleTriadSource ledger

theorem canonicalDoubleTriadEnergyPathMorphism_mapPath
    (ν : ℚ)
    {source target : DoubleTriadState}
    (path : Quiver.Path source target) :
    (canonicalDoubleTriadEnergyPathMorphism ν).mapPath path =
      path := by
  change (Prefunctor.id DoubleTriadState).mapPath path = path
  exact Prefunctor.mapPath_id path

theorem canonicalDoubleTriadEnergy_pathTrace_naturality
    (ν : ℚ)
    {source target : DoubleTriadState}
    (path : Quiver.Path source target) :
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
        ((doubleTriadNestedPathTransport ν).pathTrace path) =
      (canonicalDoubleTriadEnergyPathTransport ν).pathTrace path := by
  have naturality :=
    (canonicalDoubleTriadEnergyPathMorphism ν).pathTrace_naturality
      path
  rw [canonicalDoubleTriadEnergyPathMorphism_mapPath] at naturality
  exact naturality

/-! ## Premise-free two-scale calibration -/

theorem canonicalDoubleTriad_middleTrace :
    doubleTriadMiddleTrace (1 / 100)
        canonicalDoubleTriadSource =
      ![(3 / 10 : ℚ), (-4 / 5 : ℚ), 0, 0] := by
  rw [doubleTriadMiddleTrace_coordinates]
  funext mode
  fin_cases mode <;> norm_num

theorem canonicalDoubleTriad_upperTrace :
    doubleTriadUpperTrace (1 / 100)
        canonicalDoubleTriadSource =
      ![(1 / 20 : ℚ), 0, (9 / 20 : ℚ), 0] := by
  rw [doubleTriadUpperTrace_coordinates]
  funext mode
  fin_cases mode <;> norm_num

@[simp] theorem canonicalDoubleTriad_upperTrace_zero :
    doubleTriadUpperTrace (1 / 100)
        canonicalDoubleTriadSource 0 = 1 / 20 := by
  rw [canonicalDoubleTriad_upperTrace]
  rfl

@[simp] theorem canonicalDoubleTriad_upperTrace_one :
    doubleTriadUpperTrace (1 / 100)
        canonicalDoubleTriadSource 1 = 0 := by
  rw [canonicalDoubleTriad_upperTrace]
  rfl

@[simp] theorem canonicalDoubleTriad_upperTrace_two :
    doubleTriadUpperTrace (1 / 100)
        canonicalDoubleTriadSource 2 = 9 / 20 := by
  rw [canonicalDoubleTriad_upperTrace]
  rfl

@[simp] theorem canonicalDoubleTriad_upperTrace_three :
    doubleTriadUpperTrace (1 / 100)
        canonicalDoubleTriadSource 3 = 0 := by
  rw [canonicalDoubleTriad_upperTrace]
  rfl

theorem canonicalDoubleTriad_middleFlux :
    doubleTriadMiddleFlux (1 / 100)
      canonicalDoubleTriadSource = 1 / 5 := by
  norm_num [doubleTriadMiddleFlux_eq,
    canonicalDoubleTriadSource_zero,
    canonicalDoubleTriadSource_one,
    canonicalDoubleTriadSource_two]

theorem canonicalDoubleTriad_upperFlux :
    doubleTriadUpperFlux (1 / 100)
      canonicalDoubleTriadSource = 2 / 25 := by
  norm_num [doubleTriadUpperFlux_eq,
    canonicalDoubleTriadSource_zero,
    canonicalDoubleTriadSource_two,
    canonicalDoubleTriadSource_three]

theorem canonicalDoubleTriad_directLowFlux :
    doubleTriadDirectLowFlux (1 / 100)
      canonicalDoubleTriadSource = 1 / 10 := by
  rw [doubleTriadDirectLowFlux_telescope,
    canonicalDoubleTriad_middleFlux,
    canonicalDoubleTriad_upperTrace]
  norm_num [doubleTriadLowEnergyDifferential,
    doubleTriadLowPass]

theorem canonicalDoubleTriad_middlePath_energyTrace :
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
        ((doubleTriadNestedPathTransport (1 / 100)).pathTrace
          (doubleTriadMiddlePath canonicalDoubleTriadSource)) =
      ((0 : ℚ), 0, (-2 / 25 : ℚ)) := by
  rw [doubleTriadMiddlePath_trace]
  norm_num [doubleTriadNestedEnergyMap,
    doubleTriadLowEnergyDifferential,
    doubleTriadMiddleEnergyDifferential]

theorem canonicalDoubleTriad_lowAfterMiddlePath_energyTrace :
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
        ((doubleTriadNestedPathTransport (1 / 100)).pathTrace
          (doubleTriadLowPath
            (doubleTriadMiddlePass canonicalDoubleTriadSource))) =
      ((0 : ℚ), (-1 / 5 : ℚ), 0) := by
  rw [doubleTriadLowAfterMiddlePath_trace,
    canonicalDoubleTriad_middleTrace]
  norm_num [doubleTriadNestedEnergyMap,
    doubleTriadLowEnergyDifferential,
    doubleTriadMiddleEnergyDifferential]

theorem canonicalDoubleTriad_twoScalePath_energyTrace :
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
        ((doubleTriadNestedPathTransport (1 / 100)).pathTrace
          (doubleTriadTwoScalePath canonicalDoubleTriadSource)) =
      ((0 : ℚ), (-1 / 5 : ℚ), (-2 / 25 : ℚ)) := by
  rw [doubleTriadTwoScalePath_trace,
    canonicalDoubleTriad_middleTrace]
  norm_num [doubleTriadNestedEnergyMap,
    doubleTriadLowEnergyDifferential,
    doubleTriadMiddleEnergyDifferential]

def doubleTriadMiddleEnergyObserver :
    DoubleTriadNestedEnergyLedger →ₗ[ℚ] ℚ where
  toFun ledger := ledger.2.1
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar ledger
    rfl

def doubleTriadUpperEnergyObserver :
    DoubleTriadNestedEnergyLedger →ₗ[ℚ] ℚ where
  toFun ledger := ledger.2.2
  map_add' := by
    intro left right
    rfl
  map_smul' := by
    intro scalar ledger
    rfl

/-- U3 for the lower edge: the actual generated trace avoids its physical
energy observer kernel. -/
theorem canonicalDoubleTriad_lowTrace_avoids_energyKernel :
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
          ((doubleTriadNestedPathTransport (1 / 100)).pathTrace
            (doubleTriadLowPath
              (doubleTriadMiddlePass canonicalDoubleTriadSource))) ∉
      LinearMap.ker doubleTriadMiddleEnergyObserver := by
  intro inKernel
  have observedZero := LinearMap.mem_ker.mp inKernel
  rw [canonicalDoubleTriad_lowAfterMiddlePath_energyTrace] at observedZero
  norm_num [doubleTriadMiddleEnergyObserver] at observedZero

/-- U3 for the upper edge, on its native `P₅` energy carrier. -/
theorem canonicalDoubleTriad_upperTrace_avoids_energyKernel :
    doubleTriadNestedEnergyMap canonicalDoubleTriadSource
          ((doubleTriadNestedPathTransport (1 / 100)).pathTrace
            (doubleTriadMiddlePath canonicalDoubleTriadSource)) ∉
      LinearMap.ker doubleTriadUpperEnergyObserver := by
  intro inKernel
  have observedZero := LinearMap.mem_ker.mp inKernel
  rw [canonicalDoubleTriad_middlePath_energyTrace] at observedZero
  norm_num [doubleTriadUpperEnergyObserver] at observedZero

theorem canonicalDoubleTriad_middleShellEnergyRate :
    doubleTriadMiddleShellEnergyRate canonicalDoubleTriadSource
        (doubleTriadNavierStokesGalerkinGenerator (1 / 100)
          (doubleTriadMiddlePass canonicalDoubleTriadSource)) =
      9 / 50 := by
  rw [doubleTriadMiddleShellEnergy_afterMiddlePass_exact_budget,
    canonicalDoubleTriad_middleFlux]
  norm_num

theorem canonicalDoubleTriad_upperShellEnergyRate :
    doubleTriadUpperShellEnergyRate canonicalDoubleTriadSource
        (doubleTriadNavierStokesGalerkinGenerator (1 / 100)
          canonicalDoubleTriadSource) =
      3 / 40 := by
  rw [doubleTriadUpperShellEnergy_exact_budget,
    canonicalDoubleTriad_upperFlux]
  norm_num

theorem canonicalDoubleTriad_middleShellEnergyRate_pos :
    0 <
      doubleTriadMiddleShellEnergyRate canonicalDoubleTriadSource
        (doubleTriadNavierStokesGalerkinGenerator (1 / 100)
          (doubleTriadMiddlePass canonicalDoubleTriadSource)) := by
  rw [canonicalDoubleTriad_middleShellEnergyRate]
  norm_num

theorem canonicalDoubleTriad_upperShellEnergyRate_pos :
    0 <
      doubleTriadUpperShellEnergyRate canonicalDoubleTriadSource
        (doubleTriadNavierStokesGalerkinGenerator (1 / 100)
          canonicalDoubleTriadSource) := by
  rw [canonicalDoubleTriad_upperShellEnergyRate]
  norm_num

/-! ## Zero and direction controls -/

@[simp] theorem zeroOuterDoubleTriad_upperTrace :
    doubleTriadUpperTrace (1 / 100)
      zeroOuterDoubleTriadSource = 0 := by
  rw [doubleTriadUpperTrace_coordinates]
  funext mode
  fin_cases mode <;> norm_num

theorem zeroOuterDoubleTriad_upperFlux :
    doubleTriadUpperFlux (1 / 100)
      zeroOuterDoubleTriadSource = 0 := by
  norm_num [doubleTriadUpperFlux_eq,
    zeroOuterDoubleTriadSource_zero,
    zeroOuterDoubleTriadSource_two,
    zeroOuterDoubleTriadSource_three]

theorem zeroOuterDoubleTriad_middleFlux :
    doubleTriadMiddleFlux (1 / 100)
      zeroOuterDoubleTriadSource = 1 / 5 := by
  norm_num [doubleTriadMiddleFlux_eq,
    zeroOuterDoubleTriadSource_zero,
    zeroOuterDoubleTriadSource_one,
    zeroOuterDoubleTriadSource_two]

@[simp] theorem zeroMiddleDoubleTriad_middleTrace :
    doubleTriadMiddleTrace (1 / 100)
      zeroMiddleDoubleTriadSource = 0 := by
  rw [doubleTriadMiddleTrace_coordinates]
  funext mode
  fin_cases mode <;> norm_num

theorem zeroMiddleDoubleTriad_upperTrace :
    doubleTriadUpperTrace (1 / 100)
        zeroMiddleDoubleTriadSource =
      ![(0 : ℚ), 0, (9 / 20 : ℚ), 0] := by
  rw [doubleTriadUpperTrace_coordinates]
  funext mode
  fin_cases mode <;> norm_num

theorem zeroMiddleDoubleTriad_middleFlux :
    doubleTriadMiddleFlux (1 / 100)
      zeroMiddleDoubleTriadSource = 0 := by
  norm_num [doubleTriadMiddleFlux_eq,
    zeroMiddleDoubleTriadSource_zero,
    zeroMiddleDoubleTriadSource_one,
    zeroMiddleDoubleTriadSource_two]

theorem zeroMiddleDoubleTriad_upperFlux :
    doubleTriadUpperFlux (1 / 100)
      zeroMiddleDoubleTriadSource = 0 := by
  norm_num [doubleTriadUpperFlux_eq,
    zeroMiddleDoubleTriadSource_zero,
    zeroMiddleDoubleTriadSource_two,
    zeroMiddleDoubleTriadSource_three]

theorem backscatterOuterDoubleTriad_upperFlux :
    doubleTriadUpperFlux (1 / 100)
      backscatterOuterDoubleTriadSource = -2 / 25 := by
  norm_num [doubleTriadUpperFlux_eq,
    backscatterOuterDoubleTriadSource_zero,
    backscatterOuterDoubleTriadSource_two,
    backscatterOuterDoubleTriadSource_three]

theorem backscatterOuterDoubleTriad_middleFlux :
    doubleTriadMiddleFlux (1 / 100)
      backscatterOuterDoubleTriadSource = 1 / 5 := by
  norm_num [doubleTriadMiddleFlux_eq,
    backscatterOuterDoubleTriadSource_zero,
    backscatterOuterDoubleTriadSource_one,
    backscatterOuterDoubleTriadSource_two]

theorem backscatterMiddleDoubleTriad_middleFlux :
    doubleTriadMiddleFlux (1 / 100)
      backscatterMiddleDoubleTriadSource = -1 / 5 := by
  norm_num [doubleTriadMiddleFlux_eq,
    backscatterMiddleDoubleTriadSource_zero,
    backscatterMiddleDoubleTriadSource_one,
    backscatterMiddleDoubleTriadSource_two]

theorem backscatterMiddleDoubleTriad_upperFlux :
    doubleTriadUpperFlux (1 / 100)
      backscatterMiddleDoubleTriadSource = 2 / 25 := by
  norm_num [doubleTriadUpperFlux_eq,
    backscatterMiddleDoubleTriadSource_zero,
    backscatterMiddleDoubleTriadSource_two,
    backscatterMiddleDoubleTriadSource_three]

/-- Premise-free U1--U4 two-scale checkpoint. -/
theorem canonicalDoubleTriadTwoScaleTransferCheckpoint :
    (doubleTriadNestedPathTransport (1 / 100)).residual
          (doubleTriadLowPass
            (doubleTriadMiddlePass canonicalDoubleTriadSource)) =
        (doubleTriadNestedPathTransport (1 / 100)).pathKeep
          (doubleTriadTwoScalePath canonicalDoubleTriadSource)
          ((doubleTriadNestedPathTransport (1 / 100)).residual
            canonicalDoubleTriadSource) ∧
      doubleTriadNestedEnergyMap canonicalDoubleTriadSource
            ((doubleTriadNestedPathTransport (1 / 100)).pathTrace
              (doubleTriadLowPath
                (doubleTriadMiddlePass
                  canonicalDoubleTriadSource))) ∉
        LinearMap.ker doubleTriadMiddleEnergyObserver ∧
      doubleTriadNestedEnergyMap canonicalDoubleTriadSource
            ((doubleTriadNestedPathTransport (1 / 100)).pathTrace
              (doubleTriadMiddlePath canonicalDoubleTriadSource)) ∉
        LinearMap.ker doubleTriadUpperEnergyObserver ∧
      doubleTriadMiddleFlux (1 / 100)
          canonicalDoubleTriadSource = 1 / 5 ∧
      doubleTriadUpperFlux (1 / 100)
          canonicalDoubleTriadSource = 2 / 25 ∧
      0 <
        doubleTriadMiddleShellEnergyRate canonicalDoubleTriadSource
          (doubleTriadNavierStokesGalerkinGenerator (1 / 100)
            (doubleTriadMiddlePass canonicalDoubleTriadSource)) ∧
      0 <
        doubleTriadUpperShellEnergyRate canonicalDoubleTriadSource
          (doubleTriadNavierStokesGalerkinGenerator (1 / 100)
            canonicalDoubleTriadSource) := by
  exact
    ⟨doubleTriadTwoScalePath_actual_update
        (1 / 100) canonicalDoubleTriadSource,
      canonicalDoubleTriad_lowTrace_avoids_energyKernel,
      canonicalDoubleTriad_upperTrace_avoids_energyKernel,
      canonicalDoubleTriad_middleFlux,
      canonicalDoubleTriad_upperFlux,
      canonicalDoubleTriad_middleShellEnergyRate_pos,
      canonicalDoubleTriad_upperShellEnergyRate_pos⟩

end

end TwoDimensionalVorticityDoubleTriadEnergyConsumer
end SaturationMonoid.NavierStokes
