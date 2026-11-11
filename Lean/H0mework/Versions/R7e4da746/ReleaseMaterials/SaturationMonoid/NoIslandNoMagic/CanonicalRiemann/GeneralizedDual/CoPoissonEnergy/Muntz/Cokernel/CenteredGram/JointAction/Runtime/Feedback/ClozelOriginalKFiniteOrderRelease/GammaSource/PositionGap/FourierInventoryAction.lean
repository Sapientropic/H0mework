import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierHankel
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.OutsideQuarterAction

set_option autoImplicit false
noncomputable section

namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
namespace OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory

open Complex BurnolPhysicalState OriginalRieszSource
open OriginalRieszFinitePairing.CoPoisson.Ward
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open UnitPowerJordanAction GenericSourceStepBAction OutsideQuarterAction
open scoped InnerProductSpace lp

open private cayley_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGapCayley
open private actual_next_stock damping_ne from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.DivisionCoefficients
open private fourier_forward orbit_read hankel_inner from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.FourierHankel
open private unit_read from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.GapHilbertBasis
open private fourier_R from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GammaSource.PositionGap.PairedCayleyAction
open private position_read fourier_read actual_position_step position_gap_zero block_unique source_even from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKFiniteOrderRelease.GenericSourceStepBAction
open private full_split from
  H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyIntertwiningSource

local notation "R" => burnolDirectRightResolventCLM
local notation "F" => fourierL2
local notation "T" => sourceCayley
local notation "δ" => sourceDamping
local notation "d" => OriginalPrimitiveRankBalance.conjugateCoordinate
local notation "E" => burnolQuarterZeroExtension
local notation "Rq" => burnolQuarterRestriction
local notation "Z" => Constructor.zeroMean
local notation "M" => burnolAmbientCompletedMellinEvaluator
local notation "Seq" => ℓ²(Nat, ℂ)
local notation "Quarter" => BurnolQuarterMeanZeroCarrier
local notation "O" => OriginalKCombPhysicalAction.physicalRemainder
local notation "P" => OriginalKCombPhysicalAction.physicalProjection
local notation "BI" => burnolMeanZeroBlockInverse
local notation "S₀" => burnolMeanZeroTruncatedFourier

private theorem conjugate_twice (c : BurnolCompletedMellinCoordinate) : d (d c) = c := by
  cases c
  simp only [OriginalPrimitiveRankBalance.conjugateCoordinate, star_star]

private theorem next_field (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    ((basis c).repr.symm (nextCoefficients c a) : BurnolL2) = R c (((basis c).repr.symm a : BurnolL2)) := by
  let x := (basis c).repr.symm a
  have even := mem_evenL2ClosedFace_iff.mp x.property.2
  let shifted : PositionField :=
    ⟨T c x, actual_gap_cayley c _ x.property.1, mem_evenL2ClosedFace_iff.mpr (cayley_even c _ even)⟩
  let y := (δ c : ℂ)⁻¹ • (shifted - x)
  have performed : (y : BurnolL2) = R c x := by
    change (δ c : ℂ)⁻¹ • (T c x-(x : BurnolL2)) = R c x
    rw [sourceCayley_apply, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ (damping_ne c), one_smul]
    rfl
  have coefficient := actual_next_stock c x y performed
  dsimp only [x] at coefficient
  rw [LinearIsometryEquiv.apply_symm_apply] at coefficient
  rw [coefficient, LinearIsometryEquiv.symm_apply_apply]
  exact performed

private def leftShift (wave : Seq) : Seq :=
  ⟨fun n => wave (n+1), memℓp_gen ((summable_nat_add_iff 1).mpr
    ((lp.memℓp wave).summable (by norm_num)))⟩

/-- The Fourier wave clock advances by the opposite neighbor difference. -/
def nextFourierWave (c : BurnolCompletedMellinCoordinate) (wave : Seq) : Seq :=
  (δ c : ℂ)⁻¹ • (leftShift wave - wave)

/-- The quarter update consumes the old center and the actual wave head. -/
def nextFourierCenter (c : BurnolCompletedMellinCoordinate) (wave : Seq) (center : Quarter) : Quarter :=
  centeredQuarterStep (d c) center +
    (-2 * ((normalization (d c))⁻¹ * wave 0)) • SingularCounting.centeredPower (d c)

theorem actual_fourier_wave_write (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    hankel c (nextCoefficients c a) = nextFourierWave c (hankel c a) := by
  apply lp.ext
  funext i
  apply mul_left_cancel₀ (damping_ne c)
  change (δ c : ℂ) * hankel c (nextCoefficients c a) i =
    (δ c : ℂ) * ((δ c : ℂ)⁻¹ * (hankel c a (i+1)-hankel c a i))
  rw [← mul_assoc, mul_inv_cancel₀ (damping_ne c), one_mul]
  let v := ((basis c).repr.symm a : BurnolL2)
  let column : BurnolL2 := basis (d c) i
  have next_column : T (d c) column = (basis (d c) (i+1) : BurnolL2) := by
    dsimp only [column]
    rw [orbit_read, orbit_read, pow_succ', mul_apply_eq_comp]
  have paid := congrArg (inner ℂ column) (fourier_forward c v)
  change inner ℂ column (F (T c v)) = inner ℂ column ((T (d c)).adjoint (F v)) at paid
  rw [sourceCayley_apply, map_add, map_smul, inner_add_right, inner_smul_right,
    ContinuousLinearMap.adjoint_inner_right, next_column] at paid
  rw [hankel_inner, hankel_inner, hankel_inner, next_field]
  change (δ c : ℂ) * inner ℂ column (F (R c v)) =
    inner ℂ (basis (d c) (i+1) : BurnolL2) (F v) - inner ℂ column (F v)
  exact eq_sub_of_add_eq ((add_comm _ _).trans paid)

theorem actual_fourier_center_write (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    centeredFourier c (nextCoefficients c a) =
      nextFourierCenter c (hankel c a) (centeredFourier c a) := by
  let v := (basis c).repr.symm a
  have even := mem_evenL2ClosedFace_iff.mp (fourierL2_mem_evenL2ClosedFace v.property.2)
  have paid := actual_position_step (d c) (F (v : BurnolL2)) even
  rw [position_read _ (source_even (d c) _ even), position_read _ even,
    actual_currentAmplitude_ambient, conjugate_twice] at paid
  have head : hankel c a 0 = normalization (d c) * M c (F (v : BurnolL2)) := by
    rw [hankel_inner, orbit_read, pow_zero, one_apply_eq_self, unit_read _ _ even, conjugate_twice]
  have amplitude : (normalization (d c))⁻¹ * hankel c a 0 = M c (F (v : BurnolL2)) := by
    rw [head, ← mul_assoc, inv_mul_cancel₀ (normalization_ne_zero (d c)), one_mul]
  unfold nextFourierCenter
  rw [amplitude]
  change Z (Rq (F (((basis c).repr.symm (nextCoefficients c a) : BurnolL2)))) =
    centeredQuarterStep (d c) (Z (Rq (F (v : BurnolL2)))) +
      (-2 * M c (F (v : BurnolL2))) • SingularCounting.centeredPower (d c)
  rw [next_field, fourier_R]
  exact paid

/-- The two source updates synthesize the actual Fourier image of the original R successor. -/
theorem actual_fourier_next_readback (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    ((basis (d c)).repr.symm (nextFourierWave c (hankel c a)) : BurnolL2) +
      E (nextFourierCenter c (hankel c a) (centeredFourier c a) : BurnolQuarterIntervalL2) =
      F (R c (((basis c).repr.symm a : BurnolL2))) := by
  rw [← actual_fourier_wave_write, ← actual_fourier_center_write, actual_fourier_readback, next_field]

/-- The complete centered coordinate is the source of the original B inverse and exterior column. -/
theorem actual_original_B_outside (c : BurnolCompletedMellinCoordinate) (a : Seq) :
    O (((basis c).repr.symm a : BurnolL2)) = outsideEmbedding (BI (centeredFourier c a)) := by
  let v := (basis c).repr.symm a
  let z := BI (centeredFourier c a)
  have even := mem_evenL2ClosedFace_iff.mp v.property.2
  have centered : centeredFourier c a = burnolAmbientMeanZeroFourier (v : BurnolL2) :=
    (fourier_read _ even).symm
  have block : z - S₀ (S₀ z) = centeredFourier c a := by
    have right := congrArg (fun op : Quarter →L[ℂ] Quarter => op (centeredFourier c a))
      burnolMeanZeroBlockInverse_right
    exact right
  have solved := (block_unique (burnolAmbientMeanZeroPosition v) (burnolAmbientMeanZeroFourier v)
    (-(S₀ z)) z (by rw [neg_add_cancel, position_gap_zero _ even v.property.1])
    (by rw [map_neg, neg_add_eq_sub, block, centered])).2
  change O (v : BurnolL2) = outsideEmbedding z
  rw [outside_of_gap _ even v.property.1]
  exact congrArg outsideEmbedding solved.symm

variable (observation : GeneratedRiemannZeroObservation)
variable (nontrivial : ¬ ∃ n : Nat, observation.coordinate = -2*(n+1))
variable (half : OriginalKCombCalculation.Half observation) (depth : Nat)

local notation "coord" => burnolDivisionZeroCompletedMellinCoordinate observation half.down
local notation "stock" => coefficientsAt observation nontrivial half depth
local notation "input" => OriginalKCombFirstFullSourceDynamics.input observation nontrivial half depth

/-- The existing B solve writes the complete physical and outside branches of the literal next row. -/
theorem actual_division_B_inventory_write (ordinal : Nat) :
    let a := stock ordinal;
    let whole := ((basis coord).repr.symm (nextCoefficients coord a) : BurnolL2);
    let exterior := outsideEmbedding (BI (nextFourierCenter coord (hankel coord a) (centeredFourier coord a)));
    (whole - exterior, exterior) = input (ordinal+1) := by
  let a := stock ordinal
  let generated := nextCoefficients coord a
  let v := ((basis coord).repr.symm generated : BurnolL2)
  have exterior : O v =
    outsideEmbedding (BI (nextFourierCenter coord (hankel coord a) (centeredFourier coord a))) := by
    rw [← actual_fourier_center_write]
    exact actual_original_B_outside coord generated
  have whole := full_split v
  have physical : v - O v = P v := (eq_sub_of_add_eq whole.symm).symm
  have source := (actual_division_inventory_write observation nontrivial half depth ordinal).2.1
  change (P v, O v) = _ at source
  change (v - outsideEmbedding (BI (nextFourierCenter coord (hankel coord a) (centeredFourier coord a))),
    outsideEmbedding (BI (nextFourierCenter coord (hankel coord a) (centeredFourier coord a)))) = _
  rw [← exterior, physical]
  exact source

end OriginalKFiniteOrderRelease.PositionGapCayley.HilbertInventory
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
