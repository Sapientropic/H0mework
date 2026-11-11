import Mathlib.Analysis.InnerProductSpace.ProdL2
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open BurnolPhysicalState OriginalKCofinalFullBranchFibre OutsideQuarterAction
open scoped InnerProductSpace lp

open private next_field from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction
open private full_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

local notation "R" => burnolDirectRightResolventCLM
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "P₀" => OriginalKCombPhysicalAction.physicalProjection
local notation "BI" => burnolMeanZeroBlockInverse

local instance : CompleteSpace PositionField :=
  IsComplete.completeSpace_coe positionSpace.isClosed.isComplete

abbrev WholeFieldStock := WithLp 2 (ℓ²(Nat, ℂ) × PositionFieldᗮ)
abbrev WholeBranchStock := WholeFieldStock × BurnolL2

/-- The original gap coefficients and their full orthogonal residual exhaust the ambient field. -/
def wholeCoordinates (c : BurnolCompletedMellinCoordinate) : BurnolL2 ≃ₗᵢ[ℂ] WholeFieldStock :=
  PositionField.orthogonalDecomposition.trans
    ((basis c).repr.withLpProdCongr 2 (LinearIsometryEquiv.refl ℂ (PositionFieldᗮ)))

private theorem whole_synthesis (c : BurnolCompletedMellinCoordinate) (value : WholeFieldStock) :
    (wholeCoordinates c).symm value =
      ((basis c).repr.symm value.fst : BurnolL2) + (value.snd : BurnolL2) := rfl

/-- An arbitrary branch pair also retains its original exterior slot. -/
def branchCoordinates (c : BurnolCompletedMellinCoordinate) : SourcePair ≃ₗ[ℂ] WholeBranchStock where
  toFun pair := (wholeCoordinates c (pair.1+pair.2), pair.2)
  invFun stock := ((wholeCoordinates c).symm stock.1-stock.2, stock.2)
  left_inv pair := by
    change ((wholeCoordinates c).symm (wholeCoordinates c (pair.1+pair.2))-pair.2, pair.2) = pair
    rw [LinearIsometryEquiv.symm_apply_apply, add_sub_cancel_right]
  right_inv stock := by
    change (wholeCoordinates c ((wholeCoordinates c).symm stock.1-stock.2+stock.2), stock.2) = stock
    rw [sub_add_cancel, LinearIsometryEquiv.apply_symm_apply]
  map_add' a b := by
    change (wholeCoordinates c ((a.1+b.1)+(a.2+b.2)), a.2+b.2) =
      (wholeCoordinates c (a.1+a.2)+wholeCoordinates c (b.1+b.2), a.2+b.2)
    rw [← map_add, add_add_add_comm]
  map_smul' z a := by
    change (wholeCoordinates c (z • a.1+z • a.2), z • a.2) =
      (z • wholeCoordinates c (a.1+a.2), z • a.2)
    rw [← smul_add, map_smul]

theorem branchCoordinates_gap (c : BurnolCompletedMellinCoordinate) (pair : SourcePair)
    (v : PositionField) (source : pair.1 + pair.2 = (v : BurnolL2)) :
    branchCoordinates c pair = (WithLp.toLp 2 ((basis c).repr v, 0), pair.2) := by
  change (wholeCoordinates c (pair.1+pair.2), pair.2) = _
  rw [source]
  congr 1
  rw [wholeCoordinates, LinearIsometryEquiv.trans_apply, Submodule.orthogonalDecomposition_apply,
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero v.property]
  rfl

/-- The paid position and Fourier updates act on the gap inventory.
    The original R acts on the retained orthogonal residual. -/
def advanceStock (c : BurnolCompletedMellinCoordinate) (stock : WholeBranchStock) : WholeBranchStock :=
  let a := stock.1.fst
  let gap := ((basis c).repr.symm (nextCoefficients c a) : BurnolL2)
  let residual := R c (stock.1.snd : BurnolL2)
  let quarter := nextFourierCenter c (hankel c a) (centeredFourier c a)
  (wholeCoordinates c (gap+residual), outsideEmbedding (BI quarter) + O residual)

private theorem actual_advance_stock (c : BurnolCompletedMellinCoordinate) (stock : WholeBranchStock) :
    let whole := (wholeCoordinates c).symm stock.1;
    advanceStock c stock = branchCoordinates c (P₀ (R c whole), O (R c whole)) := by
  let a := stock.1.fst
  let gap := ((basis c).repr.symm (nextCoefficients c a) : BurnolL2)
  let residual := R c (stock.1.snd : BurnolL2)
  let whole := (wholeCoordinates c).symm stock.1
  have action : R c whole = gap + residual := by
    dsimp only [whole, gap, residual, a]
    rw [whole_synthesis, map_add, next_field]
  have exterior : O gap =
      outsideEmbedding (BI (nextFourierCenter c (hankel c a) (centeredFourier c a))) := by
    rw [← actual_fourier_center_write]
    exact actual_original_B_outside c (nextCoefficients c a)
  change (wholeCoordinates c (gap+residual),
    outsideEmbedding (BI (nextFourierCenter c (hankel c a) (centeredFourier c a)))+O residual) =
    (wholeCoordinates c (P₀ (R c whole)+O (R c whole)), O (R c whole))
  have split : P₀ (R c whole) + O (R c whole) = R c whole := (full_split _).symm
  rw [split, action, map_add O, exterior]

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down

/-- The generated inventory update commutes with the original complete four-branch source action. -/
theorem actual_stock_source_step (pair : SourcePair) :
    advanceStock coord (branchCoordinates coord pair) =
      branchCoordinates coord (sourceStep observation nontrivial half pair) := by
  rw [actual_advance_stock]
  change branchCoordinates coord
    (P₀ (R coord ((wholeCoordinates coord).symm (wholeCoordinates coord (pair.1+pair.2)))),
     O (R coord ((wholeCoordinates coord).symm (wholeCoordinates coord (pair.1+pair.2))))) =
    branchCoordinates coord (sourceStep observation nontrivial half pair)
  rw [LinearIsometryEquiv.symm_apply_apply]
  change branchCoordinates coord
    (P₀ (R coord (pair.1+pair.2)), O (R coord (pair.1+pair.2))) =
    branchCoordinates coord
      (P₀ ((P.R observation nontrivial half) (pair.1+pair.2)),
       O ((P.R observation nontrivial half) (pair.1+pair.2)))
  rw [OriginalKCombCofinalRAction.original_R_direct]
  rfl

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
