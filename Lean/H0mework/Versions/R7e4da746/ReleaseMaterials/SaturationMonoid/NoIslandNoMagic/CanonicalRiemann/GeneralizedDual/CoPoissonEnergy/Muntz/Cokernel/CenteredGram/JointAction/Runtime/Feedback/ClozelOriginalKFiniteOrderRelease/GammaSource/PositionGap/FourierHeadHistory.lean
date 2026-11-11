import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.CompactFourierUniqueness
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open Complex BurnolPhysicalState OriginalKCofinalFullBranchFibre
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open scoped lp

open private hankel_inner orbit_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierHankel
open private unit_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
open private conjugate_twice from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierInventoryAction
open private damping_ne current from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients

local notation "δ" => sourceDamping
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "F" => fourierL2
local notation "E" => burnolQuarterZeroExtension
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "Seq" => ℓ²(Nat, ℂ)

private theorem hankel_zero (c : BurnolCompletedMellinCoordinate) (a : Seq)
    (silent : hankel c a = 0) : a = 0 := by
  let v := (basis c).repr.symm a
  have read := actual_fourier_readback c a
  rw [silent, map_zero, Submodule.coe_zero, zero_add] at read
  have full : F (E (centeredFourier c a : BurnolQuarterIntervalL2)) = (v : BurnolL2) := by
    rw [read, fourierL2_fourierL2, mem_evenL2ClosedFace_iff.mp v.property.2]
  have center := centered_fourier_gap_zero (centeredFourier c a) (by rw [full]; exact v.property.1)
  rw [center, Submodule.coe_zero, map_zero, map_zero] at full
  apply (basis c).repr.symm.injective
  rw [map_zero]
  exact Subtype.ext full.symm

/-- The complete Hankel wave has a unique original field even when the center was not observed. -/
theorem hankel_injective (c : BurnolCompletedMellinCoordinate) : Function.Injective (hankel c) := by
  intro a b same
  apply sub_eq_zero.mp
  apply hankel_zero c
  rw [map_sub, same, sub_self]

/-- One scalar per actual R update, read in the original Fourier chart. -/
def fourierHeadHistory (c : BurnolCompletedMellinCoordinate) (a : Seq) (time : Nat) : ℂ :=
  hankel c (((nextCoefficients c)^[time]) a) 0

/-- A finite triangular reconstruction of one wave slot from the actual head history. -/
def waveFromHeads (c : BurnolCompletedMellinCoordinate) (head : Nat → ℂ)
    (slot : Nat) : Nat → ℂ :=
  Nat.rec head (fun _ prior time => prior time + (δ c : ℂ) * prior (time+1)) slot

private theorem waveFromHeads_step (c : BurnolCompletedMellinCoordinate) (head : Nat → ℂ)
    (slot time : Nat) : waveFromHeads c head (slot+1) time =
      waveFromHeads c head slot time + (δ c : ℂ) * waveFromHeads c head slot (time+1) :=
  rfl

theorem waveFromHeads_prefix (c : BurnolCompletedMellinCoordinate) (a b : Nat → ℂ) (slot time : Nat)
    (same : ∀ k ≤ time+slot, a k = b k) : waveFromHeads c a slot time = waveFromHeads c b slot time := by
  induction slot generalizing time with
  | zero => exact same time (by omega)
  | succ n previous =>
    rw [waveFromHeads_step, waveFromHeads_step,
      previous time (fun k inside => same k (by omega)),
      previous (time+1) (fun k inside => same k (by omega))]

/-- The reconstructed slot is the exact Fourier coefficient of the same old frame. -/
theorem actual_wave_from_heads (c : BurnolCompletedMellinCoordinate) (a : Seq) (slot time : Nat) :
    waveFromHeads c (fourierHeadHistory c a) slot time =
      hankel c (((nextCoefficients c)^[time]) a) slot := by
  induction slot generalizing time with
  | zero => rfl
  | succ n previous =>
    rw [waveFromHeads_step, previous, previous, Function.iterate_succ_apply', actual_fourier_wave_write]
    let wave := hankel c (((nextCoefficients c)^[time]) a)
    change wave n + (δ c : ℂ)*((δ c : ℂ)⁻¹*(wave (n+1)-wave n)) = wave (n+1)
    rw [← mul_assoc, mul_inv_cancel₀ (damping_ne c), one_mul, add_comm (wave n), sub_add_cancel]

/-- The complete scalar history is faithful on the original position-gap field. -/
theorem fourierHeadHistory_injective (c : BurnolCompletedMellinCoordinate) :
    Function.Injective (fourierHeadHistory c) := by
  intro a b same
  apply hankel_injective c
  apply lp.ext
  funext n
  have left := actual_wave_from_heads c a n 0
  have right := actual_wave_from_heads c b n 0
  rw [same] at left
  simpa only [Function.iterate_zero, id_eq] using left.symm.trans right

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "stock" => coefficientsAt observation nontrivial half depth
local notation "raw" => D.raw observation nontrivial half depth

private theorem actual_stock_iterated (ordinal time : Nat) :
    ((nextCoefficients coord)^[time]) (stock ordinal) = stock (ordinal+time) := by
  induction time with
  | zero => rfl
  | succ n earlier =>
    rw [Function.iterate_succ_apply', earlier, actual_division_coefficient_step]
    rfl

/-- Each observed head is the original complete Fourier read at the literal source occurrence. -/
theorem actual_division_head_history (ordinal time : Nat) :
    fourierHeadHistory coord (stock ordinal) time =
      normalization (d coord) * M coord (F (raw (ordinal+time))) := by
  unfold fourierHeadHistory
  rw [actual_stock_iterated, hankel_inner, orbit_read, pow_zero, one_apply_eq_self, coefficientsAt,
    LinearIsometryEquiv.symm_apply_apply]
  let v := current observation nontrivial half depth (ordinal+time)
  have even := mem_evenL2ClosedFace_iff.mp (fourierL2_mem_evenL2ClosedFace v.property.2)
  rw [unit_read _ _ even, conjugate_twice]
  rfl

/-- The literal cofinal history determines the unique complete inventory of its original frame. -/
theorem actual_division_head_inverse (ordinal : Nat) :
    ∃! a : Seq, fourierHeadHistory coord a =
      fun time => normalization (d coord) * M coord (F (raw (ordinal+time))) := by
  have actual : fourierHeadHistory coord (stock ordinal) =
    fun time => normalization (d coord) * M coord (F (raw (ordinal+time))) :=
    funext (actual_division_head_history observation nontrivial half depth ordinal)
  exact ⟨stock ordinal, actual, fun other same => fourierHeadHistory_injective coord (same.trans actual.symm)⟩

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
