import H0mework.Versions.Rf94092ef.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedNativeUpdate
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedTransport

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKRead

open BurnolPhysicalState SourceOperationEffects SourceOperationScalarInventoryLift
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open OriginalKCofinalFullBranchFibre.KernelWrite
open scoped InnerProductSpace

open private gain original_gain from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryCountedTransport
open private below_half from H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private original_K_live from H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.ResidualProbe.BoundaryAdjointDefect

namespace U
export BoundaryCountedNativeUpdate (writtenUpdate actual_physical)
end U
namespace D
export BoundaryAdjointDefect (nativeSlot coefficient physical_defect actual_coefficient_live actual_fixed_price price actual_physical_defect)
end D
namespace B
export BoundaryCountedNativeBeta (total beta_total)
end B

local notation "End" => (BurnolL2 →L[ℂ] BurnolL2)
local notation "T" => sourceCayley
local notation "C" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "K" => burnolCompletedMellinRieszVector
local notation "Ppos" => HilbertInventory.positionSpace.toSubmodule.starProjection
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "S" => HilbertInventory.PositionField

/-- The whole operation uses the original adjoint, position cut, return and ambient projection. -/
def field (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) : End :=
  (P).comp (((1 : End) - (T (C coordinate)).comp ((Ppos).comp (T (C coordinate)).adjoint)).comp
    ((T (C coordinate)).adjoint^order))

theorem field_apply (coordinate : BurnolCompletedMellinCoordinate) (order : Nat) (value : BurnolL2) :
    field coordinate order value =
      let shifted := ((T (C coordinate)).adjoint^order) value
      P (shifted - T (C coordinate) (Ppos ((T (C coordinate)).adjoint shifted))) := rfl

private theorem gain_square_ne (coordinate : BurnolCompletedMellinCoordinate) : gain coordinate^2 ≠ 1 := by
  have denominator : coordinate.value-1/2 ≠ 0 := by
    intro zero
    have real := congrArg Complex.re zero
    norm_num at real
    linarith [coordinate.rightHalf]
  have product : gain coordinate * (coordinate.value-1/2) = -1 := by
    unfold gain
    rw [neg_mul, one_div_mul_cancel denominator]
  have below : coordinate.value.re < 1 := by
    have bound := below_half coordinate
    norm_num [Complex.div_re] at bound
    linarith
  intro square
  have factors : (gain coordinate-1)*(gain coordinate+1) = 0 := by
    calc
      _ = gain coordinate^2-1 := by ring
      _ = 0 := sub_eq_zero.mpr square
  rcases mul_eq_zero.mp factors with first | second
  · have same : gain coordinate = 1 := sub_eq_zero.mp first
    rw [same, one_mul] at product
    have real := congrArg Complex.re product
    norm_num at real
    linarith [coordinate.rightHalf]
  · have same : gain coordinate = -1 := eq_neg_of_add_eq_zero_left second
    rw [same, neg_one_mul] at product
    have real := congrArg Complex.re product
    norm_num at real
    linarith [coordinate.rightHalf]

local instance groups (grade : Nat) (slot : Unit) :
    AddCommGroup (L.Value (PairValue OriginalKCombReceiptFeedback.Value) grade slot) :=
  L.groups (PairValue OriginalKCombReceiptFeedback.Value) grade slot

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ j : Nat, observation.coordinate = -2*(j+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "c" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "a" => C c
local notation "m" => generatedRiemannXiZeroOrder ActualAnalyticOwner observation.coordinate
local notation "factory" => OriginalKCombFirstFullSourceDynamics.factory observation nontrivial half
local notation "nativeAt" => originalNative observation nontrivial half depth
local notation "raw" => OriginalKCombFirstFullSourceDynamics.raw observation nontrivial half depth
local notation "slot" => D.nativeSlot observation nontrivial half depth
local notation "amount" => fun i : Nat => D.coefficient a (slot i)

/-- Decode the full physical total of the actual paid receipt through its finite inverse. -/
def input (ordinal n : Nat) : BurnolL2 :=
  (BoundaryCountedWordInverse.equiv c n).symm
    (B.total (NativeSigma.collapseNative factory (AS.bornAfterNative (nativeAt (ordinal+1)))
      (U.writtenUpdate c n factory (nativeAt (ordinal+1)))))

theorem input_source (ordinal n : Nat) : input observation nontrivial half depth ordinal n =
    raw (ordinal+3)-raw (ordinal+1) := by
  unfold input
  rw [U.actual_physical, B.beta_total, ContinuousLinearEquiv.symm_apply_apply]

private theorem slot_source (ordinal : Nat) : (slot ordinal : BurnolL2) =
    ((T a).adjoint^m) (raw ordinal) := by
  change ((T a).adjoint^m) (ThreePortCausal.field observation nontrivial half depth ordinal 0) = _
  rw [ThreePortCausal.actual_field, Nat.add_zero]

def betaSlot (ordinal : Nat) : S := slot (ordinal+3)-slot (ordinal+1)

theorem slot_input (ordinal n : Nat) :
    ((T a).adjoint^m) (input observation nontrivial half depth ordinal n) =
      (betaSlot observation nontrivial half depth ordinal : BurnolL2) := by
  rw [input_source, map_sub, ← slot_source, ← slot_source]
  rfl

def amplitude (ordinal : Nat) : ℂ :=
  D.coefficient a (betaSlot observation nontrivial half depth ordinal)

private theorem head_step (ordinal : Nat) :
    M c (slot (ordinal+1) : BurnolL2) = gain c * M c (slot ordinal : BurnolL2) := by
  rw [BoundaryCountedTransport.actual_slot_next]
  exact original_gain c (slot ordinal)

theorem amplitude_source (ordinal : Nat) :
    amplitude observation nontrivial half depth ordinal = (gain c^2-1)*amount (ordinal+1) := by
  have first := head_step observation nontrivial half depth (ordinal+1)
  have second := head_step observation nontrivial half depth (ordinal+2)
  rw [first] at second
  unfold amplitude D.coefficient betaSlot
  rw [BoundaryXiSlot.conjugate_twice, Submodule.coe_sub, map_sub, second]
  ring

theorem amplitude_live (ordinal : Nat) : amplitude observation nontrivial half depth ordinal ≠ 0 := by
  rw [amplitude_source]
  exact mul_ne_zero (sub_ne_zero.mpr (gain_square_ne c))
    (D.actual_coefficient_live observation nontrivial half depth (ordinal+1))

/-- The exact original K is recognized after the entire source action. -/
theorem field_source (ordinal n : Nat) :
    field c m (input observation nontrivial half depth ordinal n) =
      amplitude observation nontrivial half depth ordinal • (K c : BurnolL2) := by
  rw [field_apply, slot_input]
  have projected := D.physical_defect a (betaSlot observation nontrivial half depth ordinal)
  rw [BoundaryXiSlot.conjugate_twice] at projected
  exact congrArg (fun value : BurnolPaAmbientCarrier => (value : BurnolL2)) projected

theorem field_live (ordinal n : Nat) :
    field c m (input observation nontrivial half depth ordinal n) ≠ 0 := by
  rw [field_source]
  apply smul_ne_zero (amplitude_live observation nontrivial half depth ordinal)
  intro zero
  exact original_K_live observation half
    ((congrArg (M c) zero).trans (map_zero (M c)))

private theorem fixed_pairing :
    inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2) (K c : BurnolL2) =
      -(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual := by
  have paid := D.actual_fixed_price observation nontrivial half 0 0
  unfold D.price at paid
  rw [D.actual_physical_defect, Submodule.coe_smul, inner_smul_right] at paid
  exact mul_left_cancel₀ (D.actual_coefficient_live observation nontrivial half 0 0) paid

/-- The independent original fixed B reads the field generated by the actual paid beta. -/
theorem fixed_price (ordinal n : Nat) :
    inner ℂ (BoundaryAdjointDefect.B.physicalCotest c : BurnolL2)
      (field c m (input observation nontrivial half depth ordinal n)) =
      amplitude observation nontrivial half depth ordinal *
        (-(installedOriginalKReceiptAt observation nontrivial half.down).fixedResidual) := by
  rw [field_source observation nontrivial half depth ordinal n, inner_smul_right,
    fixed_pairing observation nontrivial half]

end OriginalKFiniteOrderRelease.PositionGapCayley.OutsideLogRank.ParameterSource.FixedRead.ResidualProbe.BoundaryNativeKRead
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
