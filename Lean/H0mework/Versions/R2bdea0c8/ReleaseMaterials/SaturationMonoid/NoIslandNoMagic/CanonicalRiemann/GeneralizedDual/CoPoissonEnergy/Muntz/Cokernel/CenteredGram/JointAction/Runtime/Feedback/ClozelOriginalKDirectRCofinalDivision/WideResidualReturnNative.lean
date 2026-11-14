import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.WideResidualReturn
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.ActualSourceAction

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 175000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn

open BurnolPhysicalState RootInquiryCompletion SourceOperationEffects SourceOperationExecution
open OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open RootGeneratedDebtActivationJointSource.OwnerFree
namespace Eval
export RootGeneratedDebtActivationJointSource.OwnerFree.Consumer
  (value value_source trace paid_history original_material relation_boundary)
end Eval

attribute [local instance] OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory.SecondConductorStock.SingleSlot.wideInner

local instance nativeNormed : NormedSpace ℂ Wide := wideInner.toNormedSpace

private inductive Stage
  | births | prices | graphs

@[reducible] private def Value (n : Nat) : Stage → Type
  | .births => (BurnolL2 × BurnolL2) × (BurnolL2 × BurnolL2)
  | .prices => PriceBank n
  | .graphs => Wide × Wide × Wide

private instance valueGroup (n : Nat) (stage : Stage) : AddCommGroup (Value n stage) := by
  cases stage <;> exact inferInstanceAs (AddCommGroup _)

private abbrev Var (_ : Stage) := Unit
local notation "Born" => Stage.births
local notation "Bank" => Stage.prices
local notation "Graphs" => Stage.graphs

private def seed {n : Nat} (decode : PriceBank n →ₗ[ℂ] Wide) : Value n Bank →+ Value n Graphs :=
  decode.toAddMonoidHom.prod 0

private def clockStep (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) {n : Nat} :
    Value n Graphs →+ Value n Graphs :=
  let linear := Geom.clock (advanceWide c zero) (sourceDamping c)
  let drive : Wide →L[ℂ] Wide := Geom.driveScale (sourceDamping c) • ContinuousLinearMap.id ℂ Wide
  let first := AddMonoidHom.fst Wide (Wide × Wide)
  let current := (AddMonoidHom.fst Wide Wide).comp (AddMonoidHom.snd Wide (Wide × Wide))
  first.prod ((linear.toAddMonoidHom.comp current + drive.toAddMonoidHom.comp first).prod 0)

private def writeStep (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) {n : Nat} :
    Value n Graphs →+ Value n Graphs :=
  let first := AddMonoidHom.fst Wide (Wide × Wide)
  let current := (AddMonoidHom.fst Wide Wide).comp (AddMonoidHom.snd Wide (Wide × Wide))
  first.prod (current.prod ((advanceWide c zero).toAddMonoidHom.comp current))

private def program (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0) {n : Nat}
    (read : Value n Born →+ Value n Bank) (decode : PriceBank n →ₗ[ℂ] Wide) :
    Nat → Expr (Value n) Var Graphs
  | 0 => .linear (seed decode) (.linear read (.var (s := Born) ()))
  | m+1 => .linear (clockStep c zero) (program c zero read decode m)

private theorem program_source (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    {n : Nat} (read : Value n Born →+ Value n Bank) (decode : PriceBank n →ₗ[ℂ] Wide)
    (env : Env (Value n) Var) (m : Nat) :
    let data := decode (read (env Born ()))
    (program c zero read decode m).eval env =
      (data,Geom.finite (advanceWide c zero) (sourceDamping c) m data,(0 : Wide)) := by
  let data := decode (read (env Born ()))
  induction m with
  | zero =>
    change (data,(0 : Wide),(0 : Wide)) = (data,Geom.finite (advanceWide c zero) (sourceDamping c) 0 data,0)
    rw [Geom.finite_zero, zero_apply]
  | succ m previous =>
    change clockStep c zero ((program c zero read decode m).eval env) = _
    rw [previous]
    refine Prod.ext ?_ ?_
    · rfl
    · refine Prod.ext ?_ ?_
      · have next := congrArg (fun act : Wide →L[ℂ] Wide => act data)
          (Geom.finite_succ (advanceWide c zero) (sourceDamping c) m)
        exact next.symm
      · rfl

private theorem program_charge (c : BurnolCompletedMellinCoordinate) (zero : riemannZeta c.value = 0)
    {n : Nat} (read : Value n Born →+ Value n Bank) (decode : PriceBank n →ₗ[ℂ] Wide) (m : Nat) :
    remaining (program c zero read decode m) = 3+m := by
  induction m with
  | zero => rfl
  | succ m previous => simp only [program, remaining, previous, Nat.add_succ]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth ordinal : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "authority" => OriginalKDirectRCofinalCalculatedSource.calculationRoot observation nontrivial half depth ordinal
local notation "origin" => OriginalKDirectRCofinalCalculatedSource.calculationCurrent observation nontrivial half depth ordinal
local notation "bank" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "priceAt" => sample observation nontrivial half depth
local notation "decode" => decoder observation nontrivial half depth
local notation "fit" => currentFit observation nontrivial half depth ordinal

private def priceDelta (n : Nat) : Value n Born →ₗ[ℂ] PriceBank n :=
  let first := LinearMap.fst ℂ BurnolL2 BurnolL2
  (priceAt n).comp (first.comp (LinearMap.snd ℂ _ _) - first.comp (LinearMap.fst ℂ _ _))

private def births (n : Nat) : Env (Value n) Var
  | .births, _ => (bank ordinal,bank (ordinal+1))
  | .prices, _ => 0
  | .graphs, _ => 0

/-- Each endpoint comes from its own literal Division slot. The finite programme reads their price difference. -/
def reader (n m : Nat)
    (_actual : (authority).toLedgerRoot.source.source.toRootSource.actual.OccurrenceAt origin) :
    Raw (Value := Value n) (Var := Var) (sort := Graphs) :=
  ⟨births observation nontrivial half depth ordinal n,
    .linear (writeStep c observation.mathlibZero)
      (program c observation.mathlibZero (priceDelta observation nontrivial half depth n).toAddMonoidHom (decode n) m)⟩

local notation "read" => reader observation nontrivial half depth ordinal

def paid (n m : Nat) : Wide × Wide × Wide := Eval.value authority origin (read n m)

theorem paid_source (n m : Nat) :
    paid observation nontrivial half depth ordinal n m =
      (decode n (priceAt n ((bank (ordinal+1)).1-(bank ordinal).1)),fit n m,
        advanceWide c observation.mathlibZero (fit n m)) := by
  unfold paid
  rw [Eval.value_source]
  let readPrices := (priceDelta observation nontrivial half depth n).toAddMonoidHom
  let env := births observation nontrivial half depth ordinal n
  change writeStep c observation.mathlibZero ((program c observation.mathlibZero readPrices (decode n) m).eval env) = _
  have computed := program_source c observation.mathlibZero readPrices (decode n) env m
  exact congrArg (writeStep c observation.mathlibZero (n := n)) computed

theorem paid_steps (n m : Nat) : (Eval.trace authority origin (read n m)).length = 4+m := by
  rw [Eval.paid_history]
  let readPrices := (priceDelta observation nontrivial half depth n).toAddMonoidHom
  change remaining (program c observation.mathlibZero readPrices (decode n) m)+1 = _
  have count := program_charge c observation.mathlibZero readPrices (decode n) m
  exact (congrArg (· + 1) count).trans (by omega)

run_cmd Lean.modifyEnv fun env =>
  Lean.LibrarySuggestions.nameDenyListExt.addEntry env "actual_paid_graph_return"

theorem actual_paid_graph_return (n m : Nat) :
    type_of% (paid_source observation nontrivial half depth ordinal n m) ∧
    type_of% (paid_steps observation nontrivial half depth ordinal n m) ∧
    type_of% (Eval.original_material authority origin (read n m)) ∧
    type_of% (Eval.relation_boundary (R := ℤ) authority origin (read n m)) ∧
    type_of% (Relations.boundary_in_inventory authority origin (read n m)
      (Calculation.targetRuntime authority origin (read n m))) ∧
    type_of% (Calculation.target_factorizes authority origin (read n m)) :=
  ⟨paid_source observation nontrivial half depth ordinal n m,
    paid_steps observation nontrivial half depth ordinal n m,
    Eval.original_material authority origin (read n m),
    Eval.relation_boundary (R := ℤ) authority origin (read n m),
    Relations.boundary_in_inventory authority origin (read n m)
      (Calculation.targetRuntime authority origin (read n m)),
    Calculation.target_factorizes authority origin (read n m)⟩

end WideResidualReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
