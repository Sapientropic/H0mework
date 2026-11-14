import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PhysicalPriceCountable
import H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.EmittedPaJointProbe

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CofinalPaCommonProbe

open BurnolPhysicalState
open scoped InnerProductSpace
open EmittedPaInnovation
open private retained physical_novel from H0mework.Versions.R11a01424.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.EmittedPaInnovation

namespace Fit
export SourceGeneratedFiniteGram.Projection (coefficients synthesis)
end Fit

variable {n : Nat}

private def projectedFit (columns : Fin (n+1) → BurnolPaAmbientCarrier) (tests : Fin n → ℝ) :
    Record.Values n :=
  Fit.coefficients (fun j : Fin n => WithLp.toLp 2 (fun i : Fin n =>
      PhysicalPriceCountable.price (tests i) (columns j.castSucc)))
    (WithLp.toLp 2 (fun i : Fin n => PhysicalPriceCountable.price (tests i) (columns (Fin.last n))))

/-- The real K addresses fit the already paid old columns of this physical row. -/
def fieldResidual (columns : Fin (n+1) → BurnolPaAmbientCarrier) (tests : Fin n → ℝ) :
    BurnolPaAmbientCarrier :=
  columns (Fin.last n) - Fit.synthesis (retained columns) (projectedFit columns tests)

private theorem residual_live {columns : Fin (n+1) → BurnolPaAmbientCarrier}
    (rank : LinearIndependent ℂ columns) (tests : Fin n → ℝ) : fieldResidual columns tests ≠ 0 := by
  intro silent
  exact physical_novel rank ⟨projectedFit columns tests,(sub_eq_zero.mp silent).symm⟩

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ k : Nat, observation.coordinate = -2*(k+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "pa" => OriginalKCombCofinalPaAction.actualPa observation nontrivial half depth
local notation "Event" => RetainedRecord.Progress observation nontrivial half depth
local notation "paired" => physicalPair observation nontrivial half depth

def cofinalResidual (tests : Fin n → ℝ) (ordinal : Nat) : BurnolPaAmbientCarrier :=
  fieldResidual (fun i : Fin (n+1) => pa (ordinal+i.val)) tests

local notation "residual" => cofinalResidual observation nontrivial half depth

private theorem cofinal_live (tests : Fin n → ℝ) (ordinal : Nat) : residual tests ordinal ≠ 0 := by
  have rank := (LocalPaSmear.actual_division_Pa_linearIndependent observation nontrivial half depth).comp
    (fun i : Fin (n+1) => ordinal+i.val) (fun i j same =>
      Fin.ext (Nat.add_left_cancel (show ordinal+i.val = ordinal+j.val from same)))
  exact residual_live rank tests

private theorem cofinal_exists (tests : Fin n → ℝ) (lower : ℝ) :
    ∃ height : ℝ, lower < height ∧ ∀ ordinal, PhysicalPriceCountable.price height (residual tests ordinal) ≠ 0 :=
  PhysicalPriceCountable.exists_after (residual tests)
    (cofinal_live observation nontrivial half depth tests) lower

/-- A single original K coordinate reads the new physical direction at every literal Division ordinal. -/
def commonHeight (tests : Fin n → ℝ) (lower : ℝ) : ℝ :=
  Classical.choose (cofinal_exists observation nontrivial half depth tests lower)

local notation "height" => commonHeight observation nontrivial half depth

theorem common_height_live (tests : Fin n → ℝ) (lower : ℝ) :
    lower < height tests lower ∧
      ∀ ordinal, PhysicalPriceCountable.price (height tests lower) (residual tests ordinal) ≠ 0 :=
  Classical.choose_spec (cofinal_exists observation nontrivial half depth tests lower)

/-- Both actual emitted legs use that same fixed coordinate, including at future native ordinals. -/
theorem same_height_reads_emitted_pair {start : Nat} (event : Event start n)
    (tests : Fin n → ℝ) (lower : ℝ) :
    let read := PhysicalPriceCountable.price (height tests lower)
    read (fieldResidual (fun i => (paired event i).1) tests) ≠ 0 ∧
      read (fieldResidual (fun i => (paired event i).2) tests) ≠ 0 := by
  let time := candidateTime observation nontrivial half depth start n
    (paidPivot observation nontrivial half depth start n)
  let ordinal := start+time
  have before : (fun i => (paired event i).1) = fun i => pa (ordinal+i.val) := by
    funext i
    have read : (paired event i).1 = pa (start+i.val+time) :=
      congrArg Prod.fst (physical_pair_actual observation nontrivial half depth event i)
    have address : start+i.val+time = ordinal+i.val := by dsimp only [ordinal]; omega
    exact read.trans (congrArg pa address)
  have after : (fun i => (paired event i).2) = fun i => pa (ordinal+1+i.val) := by
    funext i
    have read : (paired event i).2 = pa (start+i.val+time+1) :=
      congrArg Prod.snd (physical_pair_actual observation nontrivial half depth event i)
    have address : start+i.val+time+1 = ordinal+1+i.val := by dsimp only [ordinal]; omega
    exact read.trans (congrArg pa address)
  have live := (common_height_live observation nontrivial half depth tests lower).2
  dsimp only
  rw [before, after]
  exact ⟨live ordinal,live (ordinal+1)⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.CofinalPaCommonProbe
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
