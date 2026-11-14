import SaturationMonoid.GenericFoundation.Scalar.Feature.FiniteGram.PrefixImage.PrefixEnergy
import SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.FiniteDivisionPriceWrite

open BurnolPhysicalState HilbertInventory HilbertInventory.SecondConductorStock.SingleSlot
open SourceGeneratedFiniteGram.PrefixImage
open scoped InnerProductSpace lp

open private cotests price_read from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.DivisionPriceStream
open private fullRead from SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.SingleSlotPriceInverse

attribute [local instance] HilbertInventory.SecondConductorStock.SingleSlot.wideInner

local instance wideNormed : NormedSpace ℂ Wide := wideInner.toNormedSpace

local instance fieldStockNormed : NormedSpace ℂ WholeFieldStock :=
  WithLp.instProdNormedSpace (𝕜 := ℂ) (α := ℓ²(Nat, ℂ)) (β := PositionFieldᗮ) (p := 2)

local instance wholeStockNormed : NormedSpace ℂ WholeBranchStock := Prod.normedSpace

local instance outputNormed : NormedSpace ℂ (Wide × WholeBranchStock) := Prod.normedSpace

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "native" => advanceWide c observation.mathlibZero
local notation "tests" => cotests observation nontrivial half depth
local notation "Data" => DivisionPriceStream.Stream observation nontrivial half depth
local notation "decoded" => DivisionPriceStream.graph observation nontrivial half depth
local notation "nextOf" => DivisionPriceStream.advance observation nontrivial half depth
local notation "priceAt" => DivisionPriceStream.prices observation nontrivial half depth
local notation "relations" => DenseDivisionPrice.relationStock observation half

private def relationRead : Wide →L[ℂ] WholeBranchStock :=
  ((wholeCoordinates c).toLinearIsometry.toContinuousLinearMap.prod OriginalKCombPhysicalAction.physicalRemainder).comp
    (fullRead.comp unitGap.subtypeL)

private def writer : Wide →L[ℂ] (Wide × WholeBranchStock) :=
  ContinuousLinearMap.prod native ((relationRead observation half).comp native)

local notation "writeAt" => writer observation half

private def priceWriter (i : Nat) : Wide →L[ℂ] ℂ := (innerSL ℂ (tests i)).comp native

local notation "quoteAt" => priceWriter observation nontrivial half depth

/-- The finite prefix is acted on once, then its actual written graph gives the next K prices. -/
def write (data : Data) (n : Nat) : (Wide × WholeBranchStock) × (Nat → ℂ) :=
  let written := writeAt (approximate tests data.val n)
  (written,priceAt written.1)

local notation "finite" => write observation nontrivial half depth

set_option backward.isDefEq.respectTransparency false in
theorem whole_bound (data : Data) (n : Nat) :
    ‖(decoded (nextOf data),relations (decoded (nextOf data))) - (finite data n).1‖ ≤
      ‖writeAt‖ * Real.sqrt (remainingEnergy tests data n) := by
  have wrote : (decoded (nextOf data),relations (decoded (nextOf data))) =
      (native (decoded data),advanceStock c (relations (decoded data))) :=
    DivisionPriceStream.exact_write observation nontrivial half depth data
  have relation : (writeAt (decoded data)).2 = advanceStock c (relations (decoded data)) :=
    (DenseDivisionPrice.relation_advance observation nontrivial half (decoded data)).symm
  have same : (decoded (nextOf data),relations (decoded (nextOf data))) = writeAt (decoded data) :=
    wrote.trans (Prod.ext rfl relation.symm)
  rw [same]
  exact @output_bound Wide
    (inferInstanceAs (NormedAddCommGroup Wide)) wideInner
    (inferInstanceAs (CompleteSpace Wide)) (Wide × WholeBranchStock)
    (inferInstanceAs (NormedAddCommGroup (Wide × WholeBranchStock))) outputNormed
    tests data n writeAt

theorem price_bound (data : Data) (n i : Nat) :
    ‖(nextOf data).val i - (finite data n).2 i‖ ≤
      ‖quoteAt i‖ * Real.sqrt (remainingEnergy tests data n) := by
  have current : (nextOf data).val i = quoteAt i (decoded data) :=
    congrFun (price_read observation nontrivial half depth (native (decoded data))) i
  have written : (finite data n).2 i = quoteAt i (approximate tests data.val n) := by
    change priceAt (native (approximate tests data.val n)) i = _
    exact congrFun (price_read observation nontrivial half depth (native (approximate tests data.val n))) i
  rw [current,written]
  exact output_bound tests data n (quoteAt i)

/-- The tolerance selects a finite prefix from its energy gap before the native write runs. -/
def writeWithin (data : Data) (ε : ℝ) (positive : 0 < ε) :=
  finite data (firstWithin tests data ε positive)

set_option backward.isDefEq.respectTransparency false in
theorem write_within_bound (data : Data) (ε : ℝ) (positive : 0 < ε) :
    let paid := writeWithin observation nontrivial half depth data ε positive
    ‖(decoded (nextOf data),relations (decoded (nextOf data))) - paid.1‖ ≤ ‖writeAt‖ * ε ∧
      ∀ i, ‖(nextOf data).val i - paid.2 i‖ ≤ ‖quoteAt i‖ * ε := by
  let n := firstWithin tests data ε positive
  have exactError : Real.sqrt (remainingEnergy tests data n) =
      ‖decoded data - approximate tests data.val n‖ := by
    have squared := error_squared tests data n
    change ‖decoded data - approximate tests data.val n‖^2 = _ at squared
    exact (congrArg Real.sqrt squared).symm.trans (Real.sqrt_sq (norm_nonneg _))
  have within : Real.sqrt (remainingEnergy tests data n) ≤ ε :=
    exactError.trans_le (first_within tests data ε positive).1.le
  exact ⟨(whole_bound observation nontrivial half depth data n).trans
    (mul_le_mul_of_nonneg_left within (ContinuousLinearMap.opNorm_nonneg (𝕜 := ℂ) (𝕜₂ := ℂ) (σ₁₂ := RingHom.id ℂ) writeAt)),fun i =>
    (price_bound observation nontrivial half depth data n i).trans
      (mul_le_mul_of_nonneg_left within (ContinuousLinearMap.opNorm_nonneg (𝕜 := ℂ) (𝕜₂ := ℂ) (σ₁₂ := RingHom.id ℂ) (quoteAt i)))⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.FiniteDivisionPriceWrite
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
