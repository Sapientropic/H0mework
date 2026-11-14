import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Operator.CayleyEffectInverse.FiniteGrowth
import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage.LinearReadback
import H0mework.Versions.R1abd7da9.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionEffectPrice
import H0mework.Versions.R2bdea0c8.ReleaseMaterials.SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage.PrefixEnergy

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 150000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace WideResidualReturn

open BurnolPhysicalState Filter
open OriginalKFiniteOrderRelease.PositionGapCayley
open HilbertInventory HilbertInventory.SecondConductorStock HilbertInventory.SecondConductorStock.SingleSlot
open OutsideLogRank.ParameterSource.FixedRead.ResidualProbe
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open SourceGeneratedFiniteGram
open scoped InnerProductSpace Topology

namespace Geom
export SourceGeneratedActionObservationHistory.OperatorRecurrence.CayleyEffectInverse
  (cayley clock retention driveScale finite finite_succ finite_zero noisyBudget inverse finite_noisy_error
    inverse_norm inverseBudget inverse_effect linear_retention_tendsto)
end Geom
namespace PriceStream
export DivisionPriceStream (Stream prices capture graph graph_capture advance)
end PriceStream

open private cotests price_read from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner

attribute [local instance] DivisionEffectPrice.wideNormed

abbrev PriceBank (n : Nat) := Coordinates (Fin n)

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "d" => sourceDamping c
local notation "native" => advanceWide c observation.mathlibZero
local notation "stock" => actualWide observation nontrivial half depth
local notation "bank" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth
local notation "cov" => cotests observation nontrivial half depth
local notation "Data" => PriceStream.Stream observation nontrivial half depth
local notation "capture" => PriceStream.capture observation nontrivial half depth
local notation "graph" => PriceStream.graph observation nontrivial half depth
local notation "price" => PriceStream.prices observation nontrivial half depth
local notation "height" => DenseDivisionPrice.height observation nontrivial half depth

def readAt (i : Nat) : BurnolL2 →ₗ[ℂ] ℂ :=
  (innerSL ℂ (burnolCompletedMellinRieszVector
    (PhysicalPriceCountable.coordinate (height i)) : BurnolL2)).toLinearMap

def sample (n : Nat) : BurnolL2 →ₗ[ℂ] PriceBank n where
  toFun field := WithLp.toLp 2 fun i : Fin n => readAt observation nontrivial half depth i.val field
  map_add' x y := by
    ext i
    change readAt observation nontrivial half depth i.val (x+y) =
      readAt observation nontrivial half depth i.val x+readAt observation nontrivial half depth i.val y
    rw [map_add]
  map_smul' a x := by
    ext i
    change readAt observation nontrivial half depth i.val (a • x) =
      a • readAt observation nontrivial half depth i.val x
    rw [map_smul]

theorem sample_source (ordinal n : Nat) :
    sample observation nontrivial half depth n (bank ordinal).1 =
      PrefixImage.sample (price (stock ordinal)) n := by
  ext i
  change readAt observation nontrivial half depth i.val (bank ordinal).1 = price (stock ordinal) i.val
  have paid := congrFun (price_read observation nontrivial half depth (stock ordinal)) i.val
  have read := covector_read (DenseDivisionPrice.address observation nontrivial half depth i.val) (stock ordinal)
  have actual := actual_observation observation nontrivial half depth ordinal
  rw [actual] at read
  exact (paid.trans read).symm

def decoder (n : Nat) : PriceBank n →ₗ[ℂ] Wide :=
  PrefixReadback.inverseLinear fun i : Fin n => cov i.val

def difference (ordinal : Nat) : Data :=
  DivisionEffectPrice.effect observation nontrivial half depth (capture (stock ordinal))

theorem difference_source (ordinal n : Nat) :
    sample observation nontrivial half depth n ((bank (ordinal+1)).1-(bank ordinal).1) =
      PrefixImage.sample (difference observation nontrivial half depth ordinal).val n := by
  have prices := DivisionEffectPrice.effect_prices observation nontrivial half depth (capture (stock ordinal))
  have later := (DivisionPriceStream.actual_current_and_next observation nontrivial half depth ordinal).2.2.1
  rw [later] at prices
  rw [map_sub, sample_source, sample_source]
  ext i
  exact (congrFun prices i.val).symm

theorem difference_graph (ordinal : Nat) :
    graph (difference observation nontrivial half depth ordinal) = (native-1) (stock ordinal) := by
  unfold difference DivisionEffectPrice.effect
  rw [PriceStream.graph_capture, PriceStream.graph_capture]

/-- A finite read from the exact price bank followed by the same finite Cayley inverse. -/
def recovery (n m : Nat) : PriceBank n →ₗ[ℂ] Wide :=
  (Geom.finite native d m).toLinearMap.comp (decoder observation nontrivial half depth n)

def currentFit (ordinal n m : Nat) : Wide :=
  recovery observation nontrivial half depth n m
    (sample observation nontrivial half depth n ((bank (ordinal+1)).1-(bank ordinal).1))

local notation "fit" => currentFit observation nontrivial half depth

/-- The complete graph synthesized by the paid Gram inverse of the actual price prefix. -/
def observedGraph (ordinal n : Nat) : Wide :=
  PrefixImage.approximate cov (difference observation nontrivial half depth ordinal).val n

theorem finite_source (ordinal n m : Nat) :
    fit ordinal n m =
      Geom.finite native d m (observedGraph observation nontrivial half depth ordinal n) := by
  let data := difference observation nontrivial half depth ordinal
  let op : Wide →L[ℂ] Wide := Geom.finite native d m
  let decode := decoder observation nontrivial half depth n
  let observed := sample observation nontrivial half depth n ((bank (ordinal+1)).1-(bank ordinal).1)
  have bankSource : observed = PrefixImage.sample data.val n :=
    difference_source observation nontrivial half depth ordinal n
  have ready : decode (PrefixImage.sample data.val n) = PrefixImage.approximate cov data.val n :=
    PrefixReadback.inverseLinear_apply (fun i : Fin n => cov i.val) (PrefixImage.sample data.val n)
  exact congrArg op ((congrArg decode bankSource).trans ready)

/-- Exact closure energy of the unpaid observations in the original graph. -/
def observedError (ordinal n : Nat) : ℝ :=
  let data := difference observation nontrivial half depth ordinal
  Real.sqrt (PrefixImage.remainingEnergy cov data n)

theorem observed_error_eq (ordinal n : Nat) :
    let data := difference observation nontrivial half depth ordinal
    observedError observation nontrivial half depth ordinal n =
      ‖graph data-observedGraph observation nontrivial half depth ordinal n‖ := by
  let data := difference observation nontrivial half depth ordinal
  let datum : Wide := graph data
  let projection : Wide := observedGraph observation nontrivial half depth ordinal n
  have energy : ‖datum-projection‖^2 = PrefixImage.remainingEnergy cov data n :=
    PrefixImage.error_squared cov data n
  exact (congrArg Real.sqrt energy).symm.trans (Real.sqrt_sq (norm_nonneg _))

/-- Complete graph budget for a specified pair of finite cutoffs. -/
def errorBudget (ordinal n m : Nat) : ℝ :=
  Geom.noisyBudget d (linearBudget c) m ‖graph (difference observation nontrivial half depth ordinal)‖
    (observedError observation nontrivial half depth ordinal n)


end WideResidualReturn
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
