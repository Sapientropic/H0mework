import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse
import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondStockCayleyGrowth
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.DivisionEffectPrice

open BurnolPhysicalState HilbertInventory HilbertInventory.SecondConductorStock
open HilbertInventory.SecondConductorStock.SingleSlot
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped InnerProductSpace

open private closedStockNormed from
  H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SecondStockCayleyGrowth
open private cotests price_read from
  H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner closedStockNormed

local instance wideNormed : NormedSpace ℂ Wide := wideInner.toNormedSpace

namespace Cayley
export SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse
  (cayley inverse inverseBudget inverse_effect inverse_norm)
end Cayley

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "d" => sourceDamping c
local notation "native" => advanceWide c observation.mathlibZero
local notation "A" => advance c observation.mathlibZero
local notation "u" => Cayley.cayley native d
local notation "U" => liftedCayley c observation.mathlibZero
local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "graph" => DivisionPriceStream.graph observation nontrivial half depth
local notation "capture" => DivisionPriceStream.capture observation nontrivial half depth
local notation "nextOf" => DivisionPriceStream.advance observation nontrivial half depth
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "tests" => cotests observation nontrivial half depth

private theorem whole_cayley (x : Wide) : toWhole (u x) = U (toWhole x) := by
  have wrote : toWhole (native x) = A (toWhole x) := rfl
  change toWhole (x+(d : ℂ) • native x) = toWhole x+(d : ℂ) • A (toWhole x)
  simp only [map_add,map_smul,wrote]

private theorem whole_power (n : Nat) (x : Wide) :
    toWhole ((u^n) x) = (U^n) (toWhole x) := by
  induction n with
  | zero => simp only [pow_zero,one_apply_eq_self]
  | succ n earlier =>
    rw [pow_succ' u n,mul_apply_eq_comp,whole_cayley observation half,earlier,
      pow_succ' U n,mul_apply_eq_comp]

private theorem growth (n : Nat) : ‖u^n‖ ≤ ((n : ℝ)+1)*linearBudget c := by
  have nonnegative : 0 ≤ ((n : ℝ)+1)*linearBudget c :=
    mul_nonneg (by positivity) (linearBudget_nonnegative c)
  apply ContinuousLinearMap.opNorm_le_bound (𝕜 := ℂ) (𝕜₂ := ℂ) (σ₁₂ := RingHom.id ℂ) _ nonnegative
  intro x
  change ‖toWhole ((u^n) x)‖ ≤ ((n : ℝ)+1)*linearBudget c*‖toWhole x‖
  rw [whole_power observation half]
  exact lifted_power_bound c observation.mathlibZero n (toWhole x)

/-- The actual increment has a bounded inverse on the original complete Γ² graph. -/
def effectInverse : Wide →L[ℂ] Wide := Cayley.inverse native d

local notation "inverse" => effectInverse observation half

theorem inverse_equations :
    inverse * (native-1) = 1 ∧ (native-1) * inverse = 1 :=
  Cayley.inverse_effect native (sourceDamping_pos c) (growth observation half)

theorem inverse_bound : ‖inverse‖ ≤ Cayley.inverseBudget d (linearBudget c) :=
  Cayley.inverse_norm native (sourceDamping_pos c) (growth observation half)

/-- The native write generates the complete change observed by the original prices. -/
def effect (data : Data) : Data := capture ((native-1) (graph data))

local notation "effectAt" => effect observation nontrivial half depth

theorem effect_prices (data : Data) : (effectAt data).val = (nextOf data).val - data.val := by
  funext i
  let x := graph data
  have out : priceAt ((native-1) x) i = inner ℂ (tests i) (native x-x) :=
    congrFun (price_read observation nontrivial half depth ((native-1) x)) i
  have forward : (nextOf data).val i = inner ℂ (tests i) (native x) :=
    congrFun (price_read observation nontrivial half depth (native x)) i
  have current : data.val i = inner ℂ (tests i) x :=
    (congrFun (DivisionPriceStream.prices_graph observation nontrivial half depth data) i).symm.trans
      (congrFun (price_read observation nontrivial half depth x) i)
  exact out.trans ((inner_sub_right (tests i) (native x) x).trans
    (congrArg₂ (· - ·) forward.symm current.symm))

def recover (data : Data) : Data := capture (inverse (graph data))

local notation "recoverAt" => recover observation nontrivial half depth

theorem recover_effect (data : Data) : recoverAt (effectAt data) = data := by
  let x := graph data
  have graphEffect : graph (effectAt data) = (native-1) x :=
    DivisionPriceStream.graph_capture observation nontrivial half depth _
  have paid : inverse ((native-1) x) = x :=
    congrArg (fun op : Wide →L[ℂ] Wide => op x) (inverse_equations observation half).1
  exact ((congrArg (fun y => capture (inverse y)) graphEffect).trans (congrArg capture paid)).trans
    (Subtype.ext (DivisionPriceStream.prices_graph observation nontrivial half depth data))

theorem effect_recover (data : Data) : effectAt (recoverAt data) = data := by
  let y := graph data
  have graphRecovered : graph (recoverAt data) = inverse y :=
    DivisionPriceStream.graph_capture observation nontrivial half depth _
  have paid : (native-1) (inverse y) = y :=
    congrArg (fun op : Wide →L[ℂ] Wide => op y) (inverse_equations observation half).2
  exact ((congrArg (fun x => capture ((native-1) x)) graphRecovered).trans (congrArg capture paid)).trans
    (Subtype.ext (DivisionPriceStream.prices_graph observation nontrivial half depth data))

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.DivisionEffectPrice
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
