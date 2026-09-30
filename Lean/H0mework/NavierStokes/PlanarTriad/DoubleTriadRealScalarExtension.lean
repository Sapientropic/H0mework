import H0mework.NavierStokes.PlanarTriad.DoubleTriadEnergyConsumer

/-!
# Faithful real extension of the two-scale vorticity chain

The complete double-triad convolution and both adjacent scale traces were
proved first over `ℚ`.  This module performs the canonical coefficientwise
extension

```text
Fin 4 → ℚ  ⟶  Fin 4 → ℝ
```

and proves concrete commutation for the actual Galerkin generator, both sharp
cutoffs, both native traces, and both energy fluxes.  The real polynomial
vector field used by the ODE layer is therefore tied to the machine-expanded
rational producer; it is not a same-named replacement model.
-/

namespace SaturationMonoid.NavierStokes
namespace TwoDimensionalVorticityDoubleTriadRealScalarExtension

noncomputable section

open TwoDimensionalVorticityDoubleTriadActual
open TwoDimensionalVorticityDoubleTriadNestedResidualTransport
open TwoDimensionalVorticityDoubleTriadEnergyConsumer

local instance doubleTriadScaleQuiverLocal :
    Quiver DoubleTriadState :=
  doubleTriadScaleQuiver

abbrev RealDoubleTriadState := Fin 4 → ℝ

/-- Coefficientwise rational-to-real extension. -/
def doubleTriadRealify :
    DoubleTriadState →ₗ[ℚ] RealDoubleTriadState where
  toFun state mode := (state mode : ℝ)
  map_add' := by
    intro left right
    funext mode
    simp
  map_smul' := by
    intro scalar state
    funext mode
    simp [Rat.smul_def]

theorem doubleTriadRealify_injective :
    Function.Injective doubleTriadRealify := by
  intro left right equalImages
  funext mode
  have coordinateEquality := congrFun equalImages mode
  change ((left mode : ℚ) : ℝ) =
    ((right mode : ℚ) : ℝ) at coordinateEquality
  exact_mod_cast coordinateEquality

/-! ## Real actual generator -/

def realDoubleTriadNonlinearGenerator
    (state : RealDoubleTriadState) : RealDoubleTriadState :=
  ![(-3 / 10 : ℝ) * state 1 * state 2 +
      (-1 / 10 : ℝ) * state 2 * state 3,
    (4 / 5 : ℝ) * state 0 * state 2,
    (-1 / 2 : ℝ) * state 0 * state 1 +
      (9 / 10 : ℝ) * state 0 * state 3,
    (-4 / 5 : ℝ) * state 0 * state 2]

def realDoubleTriadViscousGenerator
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadState :=
  ![-ν * state 0, -(2 * ν) * state 1,
    -(5 * ν) * state 2, -(10 * ν) * state 3]

def realDoubleTriadNavierStokesGalerkinGenerator
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadState :=
  realDoubleTriadNonlinearGenerator state +
    realDoubleTriadViscousGenerator ν state

theorem doubleTriadRealify_nonlinearGenerator
    (state : DoubleTriadState) :
    doubleTriadRealify (doubleTriadNonlinearGenerator state) =
      realDoubleTriadNonlinearGenerator
        (doubleTriadRealify state) := by
  rw [doubleTriadNonlinearGenerator_coordinates]
  funext mode
  fin_cases mode <;>
    norm_num [doubleTriadRealify,
      realDoubleTriadNonlinearGenerator]

theorem doubleTriadRealify_viscousGenerator
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadRealify
        (doubleTriadViscousGenerator ν state) =
      realDoubleTriadViscousGenerator
        (ν : ℝ) (doubleTriadRealify state) := by
  funext mode
  fin_cases mode <;>
    norm_num [doubleTriadRealify,
      doubleTriadViscousGenerator,
      realDoubleTriadViscousGenerator]

/-- The real vector field is the faithful scalar extension of the complete
eight-mode rational convolution producer. -/
theorem doubleTriadRealify_galerkinGenerator
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadRealify
        (doubleTriadNavierStokesGalerkinGenerator ν state) =
      realDoubleTriadNavierStokesGalerkinGenerator
        (ν : ℝ) (doubleTriadRealify state) := by
  rw [doubleTriadNavierStokesGalerkinGenerator,
    map_add, doubleTriadRealify_nonlinearGenerator,
    doubleTriadRealify_viscousGenerator]
  rfl

/-! ## Real nested sharp filters and traces -/

def realDoubleTriadMiddlePass :
    RealDoubleTriadState →ₗ[ℝ] RealDoubleTriadState where
  toFun state := ![state 0, state 1, state 2, 0]
  map_add' := by
    intro left right
    funext mode
    fin_cases mode <;> simp
  map_smul' := by
    intro scalar state
    funext mode
    fin_cases mode <;> simp

def realDoubleTriadLowPass :
    RealDoubleTriadState →ₗ[ℝ] RealDoubleTriadState where
  toFun state := ![state 0, state 1, 0, 0]
  map_add' := by
    intro left right
    funext mode
    fin_cases mode <;> simp
  map_smul' := by
    intro scalar state
    funext mode
    fin_cases mode <;> simp

@[simp] theorem realDoubleTriadMiddlePass_idempotent
    (state : RealDoubleTriadState) :
    realDoubleTriadMiddlePass
        (realDoubleTriadMiddlePass state) =
      realDoubleTriadMiddlePass state := by
  funext mode
  fin_cases mode <;> rfl

@[simp] theorem realDoubleTriadLowPass_idempotent
    (state : RealDoubleTriadState) :
    realDoubleTriadLowPass (realDoubleTriadLowPass state) =
      realDoubleTriadLowPass state := by
  funext mode
  fin_cases mode <;> rfl

@[simp] theorem realDoubleTriadLowPass_middlePass
    (state : RealDoubleTriadState) :
    realDoubleTriadLowPass (realDoubleTriadMiddlePass state) =
      realDoubleTriadLowPass state := by
  funext mode
  fin_cases mode <;> rfl

theorem doubleTriadRealify_middlePass
    (state : DoubleTriadState) :
    doubleTriadRealify (doubleTriadMiddlePass state) =
      realDoubleTriadMiddlePass
        (doubleTriadRealify state) := by
  funext mode
  fin_cases mode <;>
    norm_num [doubleTriadRealify, doubleTriadMiddlePass,
      realDoubleTriadMiddlePass]

theorem doubleTriadRealify_lowPass
    (state : DoubleTriadState) :
    doubleTriadRealify (doubleTriadLowPass state) =
      realDoubleTriadLowPass
        (doubleTriadRealify state) := by
  funext mode
  fin_cases mode <;>
    norm_num [doubleTriadRealify, doubleTriadLowPass,
      realDoubleTriadLowPass]

def realDoubleTriadBaseClosure
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadState :=
  realDoubleTriadLowPass
    (realDoubleTriadNavierStokesGalerkinGenerator ν
      (realDoubleTriadLowPass state))

def realDoubleTriadMiddleTrace
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadState :=
  realDoubleTriadLowPass
      (realDoubleTriadNavierStokesGalerkinGenerator ν
        (realDoubleTriadMiddlePass state)) -
    realDoubleTriadBaseClosure ν state

def realDoubleTriadUpperTrace
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadState :=
  realDoubleTriadMiddlePass
      (realDoubleTriadNavierStokesGalerkinGenerator ν state) -
    realDoubleTriadMiddlePass
      (realDoubleTriadNavierStokesGalerkinGenerator ν
        (realDoubleTriadMiddlePass state))

theorem realDoubleTriadMiddleTrace_coordinates
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddleTrace ν state =
      ![(-3 / 10 : ℝ) * state 1 * state 2,
        (4 / 5 : ℝ) * state 0 * state 2, 0, 0] := by
  funext mode
  fin_cases mode <;>
    simp [realDoubleTriadMiddleTrace,
      realDoubleTriadBaseClosure,
      realDoubleTriadMiddlePass, realDoubleTriadLowPass,
      realDoubleTriadNavierStokesGalerkinGenerator,
      realDoubleTriadNonlinearGenerator,
      realDoubleTriadViscousGenerator]

theorem realDoubleTriadUpperTrace_coordinates
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadUpperTrace ν state =
      ![(-1 / 10 : ℝ) * state 2 * state 3, 0,
        (9 / 10 : ℝ) * state 0 * state 3, 0] := by
  funext mode
  fin_cases mode <;>
    simp [realDoubleTriadUpperTrace,
      realDoubleTriadMiddlePass,
      realDoubleTriadNavierStokesGalerkinGenerator,
      realDoubleTriadNonlinearGenerator,
      realDoubleTriadViscousGenerator]

theorem doubleTriadRealify_baseClosure
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadRealify
        (doubleTriadBaseClosure ν state) =
      realDoubleTriadBaseClosure
        (ν : ℝ) (doubleTriadRealify state) := by
  rw [doubleTriadBaseClosure,
    doubleTriadRealify_lowPass,
    doubleTriadRealify_galerkinGenerator,
    doubleTriadRealify_lowPass]
  rfl

theorem doubleTriadRealify_middleTrace
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadRealify
        (doubleTriadMiddleTrace ν state) =
      realDoubleTriadMiddleTrace
        (ν : ℝ) (doubleTriadRealify state) := by
  rw [doubleTriadMiddleTrace, map_sub,
    doubleTriadRealify_lowPass,
    doubleTriadRealify_galerkinGenerator,
    doubleTriadRealify_middlePass,
    doubleTriadRealify_baseClosure]
  rfl

theorem doubleTriadRealify_upperTrace
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadRealify
        (doubleTriadUpperTrace ν state) =
      realDoubleTriadUpperTrace
        (ν : ℝ) (doubleTriadRealify state) := by
  rw [doubleTriadUpperTrace, map_sub,
    doubleTriadRealify_middlePass,
    doubleTriadRealify_galerkinGenerator,
    doubleTriadRealify_middlePass,
    doubleTriadRealify_galerkinGenerator,
    doubleTriadRealify_middlePass]
  rfl

/-! ## Faithful extension of the complete residual carrier -/

abbrev RealDoubleTriadNestedLedger :=
  RealDoubleTriadState × RealDoubleTriadState ×
    RealDoubleTriadState

/-- Coefficientwise extension of all three residual responsibilities. -/
def doubleTriadNestedLedgerRealify :
    DoubleTriadNestedLedger →ₗ[ℚ]
      RealDoubleTriadNestedLedger where
  toFun ledger :=
    (doubleTriadRealify ledger.1,
      doubleTriadRealify ledger.2.1,
      doubleTriadRealify ledger.2.2)
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro scalar ledger
    ext <;> simp

theorem doubleTriadNestedLedgerRealify_injective :
    Function.Injective doubleTriadNestedLedgerRealify := by
  intro left right equalImages
  apply Prod.ext
  · apply doubleTriadRealify_injective
    exact congrArg Prod.fst equalImages
  · apply Prod.ext
    · apply doubleTriadRealify_injective
      exact congrArg (fun ledger => ledger.2.1) equalImages
    · apply doubleTriadRealify_injective
      exact congrArg (fun ledger => ledger.2.2) equalImages

def realDoubleTriadMiddleKeep :
    RealDoubleTriadNestedLedger →ₗ[ℝ]
      RealDoubleTriadNestedLedger where
  toFun ledger := (ledger.1, ledger.2.1, 0)
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro scalar ledger
    ext <;> simp

def realDoubleTriadLowKeep :
    RealDoubleTriadNestedLedger →ₗ[ℝ]
      RealDoubleTriadNestedLedger where
  toFun ledger := (ledger.1, 0, 0)
  map_add' := by
    intro left right
    ext <;> simp
  map_smul' := by
    intro scalar ledger
    ext <;> simp

theorem doubleTriadNestedLedgerRealify_middleKeep
    (ledger : DoubleTriadNestedLedger) :
    doubleTriadNestedLedgerRealify
        (doubleTriadMiddleKeep ledger) =
      realDoubleTriadMiddleKeep
        (doubleTriadNestedLedgerRealify ledger) := by
  ext <;>
    simp [doubleTriadNestedLedgerRealify,
      doubleTriadMiddleKeep, realDoubleTriadMiddleKeep]

theorem doubleTriadNestedLedgerRealify_lowKeep
    (ledger : DoubleTriadNestedLedger) :
    doubleTriadNestedLedgerRealify
        (doubleTriadLowKeep ledger) =
      realDoubleTriadLowKeep
        (doubleTriadNestedLedgerRealify ledger) := by
  ext <;>
    simp [doubleTriadNestedLedgerRealify,
      doubleTriadLowKeep, realDoubleTriadLowKeep]

def realDoubleTriadNestedResidual
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadNestedLedger :=
  (realDoubleTriadBaseClosure ν state,
    realDoubleTriadMiddleTrace ν state,
    realDoubleTriadUpperTrace ν state)

theorem doubleTriadNestedLedgerRealify_residual
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadNestedLedgerRealify
        (doubleTriadNestedResidual ν state) =
      realDoubleTriadNestedResidual
        (ν : ℝ) (doubleTriadRealify state) := by
  simp [doubleTriadNestedLedgerRealify,
    doubleTriadNestedResidual,
    realDoubleTriadNestedResidual,
    doubleTriadRealify_baseClosure,
    doubleTriadRealify_middleTrace,
    doubleTriadRealify_upperTrace]

theorem realDoubleTriadBaseClosure_coordinates
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadBaseClosure ν state =
      ![-ν * state 0, -(2 * ν) * state 1, 0, 0] := by
  funext mode
  fin_cases mode <;>
    simp [realDoubleTriadBaseClosure,
      realDoubleTriadLowPass,
      realDoubleTriadNavierStokesGalerkinGenerator,
      realDoubleTriadNonlinearGenerator,
      realDoubleTriadViscousGenerator]

theorem realDoubleTriadBaseClosure_middlePass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadBaseClosure ν
        (realDoubleTriadMiddlePass state) =
      realDoubleTriadBaseClosure ν state := by
  rw [realDoubleTriadBaseClosure_coordinates,
    realDoubleTriadBaseClosure_coordinates]
  funext mode
  fin_cases mode <;> rfl

theorem realDoubleTriadBaseClosure_lowPass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadBaseClosure ν
        (realDoubleTriadLowPass state) =
      realDoubleTriadBaseClosure ν state := by
  rw [realDoubleTriadBaseClosure_coordinates,
    realDoubleTriadBaseClosure_coordinates]
  funext mode
  fin_cases mode <;> rfl

theorem realDoubleTriadMiddleTrace_middlePass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddleTrace ν
        (realDoubleTriadMiddlePass state) =
      realDoubleTriadMiddleTrace ν state := by
  rw [realDoubleTriadMiddleTrace_coordinates,
    realDoubleTriadMiddleTrace_coordinates]
  funext mode
  fin_cases mode <;> rfl

@[simp] theorem realDoubleTriadMiddleTrace_lowPass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddleTrace ν
        (realDoubleTriadLowPass state) = 0 := by
  rw [realDoubleTriadMiddleTrace_coordinates]
  funext mode
  fin_cases mode <;>
    simp [realDoubleTriadLowPass]

@[simp] theorem realDoubleTriadUpperTrace_middlePass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadUpperTrace ν
        (realDoubleTriadMiddlePass state) = 0 := by
  rw [realDoubleTriadUpperTrace_coordinates]
  funext mode
  fin_cases mode <;>
    simp [realDoubleTriadMiddlePass]

@[simp] theorem realDoubleTriadUpperTrace_lowPass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadUpperTrace ν
        (realDoubleTriadLowPass state) = 0 := by
  rw [realDoubleTriadUpperTrace_coordinates]
  funext mode
  fin_cases mode <;>
    simp [realDoubleTriadLowPass]

/-- Arbitrary real states obey the first actual scale-update law, including
states on a non-rational local ODE trajectory. -/
theorem realDoubleTriadNestedResidual_middlePass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadNestedResidual ν
        (realDoubleTriadMiddlePass state) =
      realDoubleTriadMiddleKeep
        (realDoubleTriadNestedResidual ν state) := by
  simp [realDoubleTriadNestedResidual,
    realDoubleTriadMiddleKeep,
    realDoubleTriadBaseClosure_middlePass,
    realDoubleTriadMiddleTrace_middlePass]

/-- Arbitrary real states obey the second actual scale-update law. -/
theorem realDoubleTriadNestedResidual_lowPass
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadNestedResidual ν
        (realDoubleTriadLowPass state) =
      realDoubleTriadLowKeep
        (realDoubleTriadNestedResidual ν state) := by
  simp [realDoubleTriadNestedResidual,
    realDoubleTriadLowKeep,
    realDoubleTriadBaseClosure_lowPass]

def realDoubleTriadNestedLedgerAssemble :
    RealDoubleTriadNestedLedger →ₗ[ℝ]
      RealDoubleTriadState where
  toFun ledger :=
    ledger.1 + ledger.2.1 +
      realDoubleTriadLowPass ledger.2.2
  map_add' := by
    intro left right
    simp
    abel
  map_smul' := by
    intro scalar ledger
    simp [smul_add]

theorem doubleTriadNestedLedgerRealify_assemble
    (ledger : DoubleTriadNestedLedger) :
    doubleTriadRealify
        (doubleTriadNestedLedgerAssemble ledger) =
      realDoubleTriadNestedLedgerAssemble
        (doubleTriadNestedLedgerRealify ledger) := by
  simp [doubleTriadNestedLedgerAssemble,
    realDoubleTriadNestedLedgerAssemble,
    doubleTriadNestedLedgerRealify,
    doubleTriadRealify_lowPass]

theorem realDoubleTriadNestedResidual_assembles_lowProjectedGenerator
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadNestedLedgerAssemble
        (realDoubleTriadNestedResidual ν state) =
      realDoubleTriadLowPass
        (realDoubleTriadNavierStokesGalerkinGenerator
          ν state) := by
  simp [realDoubleTriadNestedLedgerAssemble,
    realDoubleTriadNestedResidual,
    realDoubleTriadBaseClosure,
    realDoubleTriadMiddleTrace,
    realDoubleTriadUpperTrace, map_sub]

def realDoubleTriadDirectLowCommutator
    (ν : ℝ) (state : RealDoubleTriadState) :
    RealDoubleTriadState :=
  realDoubleTriadLowPass
      (realDoubleTriadNavierStokesGalerkinGenerator ν state) -
    realDoubleTriadBaseClosure ν state

theorem realDoubleTriadDirectLowCommutator_telescope
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadDirectLowCommutator ν state =
      realDoubleTriadMiddleTrace ν state +
        realDoubleTriadLowPass
          (realDoubleTriadUpperTrace ν state) := by
  simp [realDoubleTriadDirectLowCommutator,
    realDoubleTriadMiddleTrace,
    realDoubleTriadUpperTrace,
    realDoubleTriadBaseClosure, map_sub]

theorem doubleTriadRealify_directLowCommutator
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadRealify
        (doubleTriadDirectLowCommutator ν state) =
      realDoubleTriadDirectLowCommutator
        (ν : ℝ) (doubleTriadRealify state) := by
  rw [doubleTriadDirectLowCommutator,
    map_sub, doubleTriadRealify_lowPass,
    doubleTriadRealify_galerkinGenerator,
    doubleTriadRealify_baseClosure]
  rfl

/-- The rational typed path trace survives as the corresponding real
three-component trace value. -/
theorem doubleTriadTwoScalePath_trace_realify
    (ν : ℚ) (state : DoubleTriadState) :
    doubleTriadNestedLedgerRealify
        ((doubleTriadNestedPathTransport ν).pathTrace
          (doubleTriadTwoScalePath state)) =
      (0,
        realDoubleTriadMiddleTrace
          (ν : ℝ) (doubleTriadRealify state),
        realDoubleTriadUpperTrace
          (ν : ℝ) (doubleTriadRealify state)) := by
  rw [doubleTriadTwoScalePath_trace]
  simp [doubleTriadNestedLedgerRealify,
    doubleTriadRealify_middleTrace,
    doubleTriadRealify_upperTrace]

/-- The actual typed rational write-back, after faithful scalar extension,
assembles to the real direct low commutator.  This retains source-path
provenance without inventing a field-change path morphism. -/
theorem doubleTriadTwoScale_writtenMemory_realAssembly
    (ν : ℚ) (state : DoubleTriadState) :
    realDoubleTriadNestedLedgerAssemble
        (doubleTriadNestedLedgerRealify
          ((doubleTriadNestedPathTransport ν).pathWriteBack
            (doubleTriadTwoScalePath state)).2) =
      realDoubleTriadDirectLowCommutator
        (ν : ℝ) (doubleTriadRealify state) := by
  rw [← doubleTriadNestedLedgerRealify_assemble,
    doubleTriadTwoScale_writtenMemory_assembles_directCommutator,
    doubleTriadRealify_directLowCommutator]

/-! ## Real energy readouts and adjacent fluxes -/

def realDoubleTriadLowEnergyDifferential
    (state : RealDoubleTriadState)
    (tangent : RealDoubleTriadState) : ℝ :=
  2 * state 0 * tangent 0 + state 1 * tangent 1

def realDoubleTriadMiddleEnergyDifferential
    (state : RealDoubleTriadState)
    (tangent : RealDoubleTriadState) : ℝ :=
  2 * state 0 * tangent 0 +
    state 1 * tangent 1 +
      (2 / 5 : ℝ) * state 2 * tangent 2

def realDoubleTriadMiddleFlux
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  -realDoubleTriadLowEnergyDifferential state
    (realDoubleTriadMiddleTrace ν state)

def realDoubleTriadUpperFlux
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  -realDoubleTriadMiddleEnergyDifferential state
    (realDoubleTriadUpperTrace ν state)

def realDoubleTriadDirectLowFlux
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  -realDoubleTriadLowEnergyDifferential state
    (realDoubleTriadDirectLowCommutator ν state)

theorem realDoubleTriadMiddleFlux_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddleFlux ν state =
      -(state 0 * state 1 * state 2) / 5 := by
  rw [realDoubleTriadMiddleFlux,
    realDoubleTriadMiddleTrace_coordinates]
  simp [realDoubleTriadLowEnergyDifferential]
  ring

theorem realDoubleTriadUpperFlux_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadUpperFlux ν state =
      -(4 * state 0 * state 2 * state 3) / 25 := by
  rw [realDoubleTriadUpperFlux,
    realDoubleTriadUpperTrace_coordinates]
  simp [realDoubleTriadMiddleEnergyDifferential]
  ring

theorem realDoubleTriadDirectLowFlux_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadDirectLowFlux ν state =
      -(state 0 * state 1 * state 2) / 5 +
        state 0 * state 2 * state 3 / 5 := by
  rw [realDoubleTriadDirectLowFlux,
    realDoubleTriadDirectLowCommutator_telescope]
  simp [realDoubleTriadLowEnergyDifferential,
    realDoubleTriadMiddleTrace_coordinates,
    realDoubleTriadUpperTrace_coordinates,
    realDoubleTriadLowPass]
  ring

theorem doubleTriadRealify_middleFlux
    (ν : ℚ) (state : DoubleTriadState) :
    realDoubleTriadMiddleFlux
        (ν : ℝ) (doubleTriadRealify state) =
      (doubleTriadMiddleFlux ν state : ℝ) := by
  rw [realDoubleTriadMiddleFlux_eq,
    doubleTriadMiddleFlux_eq]
  simp [doubleTriadRealify]

theorem doubleTriadRealify_upperFlux
    (ν : ℚ) (state : DoubleTriadState) :
    realDoubleTriadUpperFlux
        (ν : ℝ) (doubleTriadRealify state) =
      (doubleTriadUpperFlux ν state : ℝ) := by
  rw [realDoubleTriadUpperFlux_eq,
    doubleTriadUpperFlux_eq]
  simp [doubleTriadRealify]

theorem doubleTriadRealify_directLowFlux
    (ν : ℚ) (state : DoubleTriadState) :
    realDoubleTriadDirectLowFlux
        (ν : ℝ) (doubleTriadRealify state) =
      (doubleTriadDirectLowFlux ν state : ℝ) := by
  rw [realDoubleTriadDirectLowFlux_eq]
  rw [doubleTriadDirectLowFlux_telescope]
  rw [doubleTriadMiddleFlux_eq,
    doubleTriadUpperTrace_coordinates]
  simp [doubleTriadLowEnergyDifferential,
    doubleTriadLowPass, doubleTriadRealify]
  ring

/-- Middle-shell rate in the `P₅`-filtered branch.  This is the native
consumer for the lower scale edge, not the full-trajectory derivative of
the middle shell. -/
def realDoubleTriadMiddleFilteredShellEnergyRate
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  (2 / 5 : ℝ) * state 2 *
    (realDoubleTriadNavierStokesGalerkinGenerator ν
      (realDoubleTriadMiddlePass state) 2)

/-- Actual middle-shell derivative along the full Galerkin vector field. -/
def realDoubleTriadMiddleShellActualEnergyRate
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  (2 / 5 : ℝ) * state 2 *
    (realDoubleTriadNavierStokesGalerkinGenerator ν state 2)

def realDoubleTriadUpperShellEnergyRate
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  (1 / 5 : ℝ) * state 3 *
    (realDoubleTriadNavierStokesGalerkinGenerator ν state 3)

def realDoubleTriadFullEnergyRate
    (ν : ℝ) (state : RealDoubleTriadState) : ℝ :=
  2 * state 0 *
        (realDoubleTriadNavierStokesGalerkinGenerator ν state 0) +
    state 1 *
        (realDoubleTriadNavierStokesGalerkinGenerator ν state 1) +
      (2 / 5 : ℝ) * state 2 *
        (realDoubleTriadNavierStokesGalerkinGenerator ν state 2) +
        (1 / 5 : ℝ) * state 3 *
          (realDoubleTriadNavierStokesGalerkinGenerator ν state 3)

theorem realDoubleTriadMiddleFilteredShellEnergyRate_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddleFilteredShellEnergyRate ν state =
      realDoubleTriadMiddleFlux ν state -
        2 * ν * state 2 ^ 2 := by
  rw [realDoubleTriadMiddleFlux_eq]
  simp [realDoubleTriadMiddleFilteredShellEnergyRate,
    realDoubleTriadMiddlePass,
    realDoubleTriadNavierStokesGalerkinGenerator,
    realDoubleTriadNonlinearGenerator,
    realDoubleTriadViscousGenerator]
  ring

/-- The actual middle-shell budget receives the direct `P₂` flux and pays
the upper `P₅` flux.  It is not the filtered-branch rate. -/
theorem realDoubleTriadMiddleShellActualEnergyRate_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadMiddleShellActualEnergyRate ν state =
      realDoubleTriadDirectLowFlux ν state -
        realDoubleTriadUpperFlux ν state -
          2 * ν * state 2 ^ 2 := by
  rw [realDoubleTriadDirectLowFlux_eq,
    realDoubleTriadUpperFlux_eq]
  simp [realDoubleTriadMiddleShellActualEnergyRate,
    realDoubleTriadNavierStokesGalerkinGenerator,
    realDoubleTriadNonlinearGenerator,
    realDoubleTriadViscousGenerator]
  ring

theorem realDoubleTriadUpperShellEnergyRate_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadUpperShellEnergyRate ν state =
      realDoubleTriadUpperFlux ν state -
        2 * ν * state 3 ^ 2 := by
  rw [realDoubleTriadUpperFlux_eq]
  simp [realDoubleTriadUpperShellEnergyRate,
    realDoubleTriadNavierStokesGalerkinGenerator,
    realDoubleTriadNonlinearGenerator,
    realDoubleTriadViscousGenerator]
  ring

theorem realDoubleTriadFullEnergyRate_eq
    (ν : ℝ) (state : RealDoubleTriadState) :
    realDoubleTriadFullEnergyRate ν state =
      -2 * ν *
        (state 0 ^ 2 + state 1 ^ 2 +
          state 2 ^ 2 + state 3 ^ 2) := by
  simp [realDoubleTriadFullEnergyRate,
    realDoubleTriadNavierStokesGalerkinGenerator,
    realDoubleTriadNonlinearGenerator,
    realDoubleTriadViscousGenerator]
  ring

/-! ## Canonical real source -/

def realCanonicalDoubleTriadSource : RealDoubleTriadState :=
  ![1, 1, -1, 1 / 2]

@[simp] theorem realCanonicalDoubleTriadSource_zero :
    realCanonicalDoubleTriadSource 0 = 1 := by rfl

@[simp] theorem realCanonicalDoubleTriadSource_one :
    realCanonicalDoubleTriadSource 1 = 1 := by rfl

@[simp] theorem realCanonicalDoubleTriadSource_two :
    realCanonicalDoubleTriadSource 2 = -1 := by rfl

@[simp] theorem realCanonicalDoubleTriadSource_three :
    realCanonicalDoubleTriadSource 3 = 1 / 2 := by rfl

theorem doubleTriadRealify_canonicalSource :
    doubleTriadRealify canonicalDoubleTriadSource =
      realCanonicalDoubleTriadSource := by
  funext mode
  fin_cases mode
  · norm_num [doubleTriadRealify]
  · norm_num [doubleTriadRealify]
  · change ((-1 : ℚ) : ℝ) = (-1 : ℝ)
    norm_num
  · change (((1 / 2 : ℚ) : ℝ)) = (1 / 2 : ℝ)
    norm_num

theorem realCanonicalDoubleTriad_middleFlux :
    realDoubleTriadMiddleFlux (1 / 100)
      realCanonicalDoubleTriadSource = 1 / 5 := by
  norm_num [realDoubleTriadMiddleFlux_eq]

theorem realCanonicalDoubleTriad_upperFlux :
    realDoubleTriadUpperFlux (1 / 100)
      realCanonicalDoubleTriadSource = 2 / 25 := by
  norm_num [realDoubleTriadUpperFlux_eq]

theorem realCanonicalDoubleTriad_directLowFlux :
    realDoubleTriadDirectLowFlux (1 / 100)
      realCanonicalDoubleTriadSource = 1 / 10 := by
  norm_num [realDoubleTriadDirectLowFlux_eq]

theorem realCanonicalDoubleTriad_middleFilteredShellEnergyRate :
    realDoubleTriadMiddleFilteredShellEnergyRate (1 / 100)
      realCanonicalDoubleTriadSource = 9 / 50 := by
  rw [realDoubleTriadMiddleFilteredShellEnergyRate_eq,
    realCanonicalDoubleTriad_middleFlux]
  norm_num

theorem realCanonicalDoubleTriad_middleShellActualEnergyRate :
    realDoubleTriadMiddleShellActualEnergyRate (1 / 100)
      realCanonicalDoubleTriadSource = 0 := by
  rw [realDoubleTriadMiddleShellActualEnergyRate_eq,
    realCanonicalDoubleTriad_directLowFlux,
    realCanonicalDoubleTriad_upperFlux]
  norm_num

theorem realCanonicalDoubleTriad_upperShellEnergyRate :
    realDoubleTriadUpperShellEnergyRate (1 / 100)
      realCanonicalDoubleTriadSource = 3 / 40 := by
  rw [realDoubleTriadUpperShellEnergyRate_eq,
    realCanonicalDoubleTriad_upperFlux]
  norm_num

theorem realCanonicalDoubleTriad_fullEnergyRate :
    realDoubleTriadFullEnergyRate (1 / 100)
      realCanonicalDoubleTriadSource = -13 / 200 := by
  rw [realDoubleTriadFullEnergyRate_eq]
  norm_num

end

end TwoDimensionalVorticityDoubleTriadRealScalarExtension
end SaturationMonoid.NavierStokes
