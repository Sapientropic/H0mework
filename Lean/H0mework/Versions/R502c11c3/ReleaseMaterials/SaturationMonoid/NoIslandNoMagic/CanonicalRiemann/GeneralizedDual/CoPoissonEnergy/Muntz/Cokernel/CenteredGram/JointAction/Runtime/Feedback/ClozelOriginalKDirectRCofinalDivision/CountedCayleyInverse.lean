import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.GenericFoundation.Operations.Observed.Hilbert.ContractiveRecovery.RangeAverage
import H0mework.Versions.R502c11c3.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKDirectRCofinalDivision.CountedCellReceipt
import H0mework.Versions.R7e4da746.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.CanonicalRiemann.GeneralizedDual.CoPoissonEnergy.Muntz.Cokernel.CenteredGram.JointAction.Runtime.Feedback.ClozelOriginalKCrossParameterRAdjointSource.CayleyEnergySource

set_option autoImplicit false
set_option Elab.async false
set_option pp.deepTerms.threshold 25
set_option maxHeartbeats 140000

noncomputable section
namespace SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
namespace NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
namespace CountedCayleyInverse

open BurnolPhysicalState OriginalRieszFinitePairing.CoPoisson.Ward CountedJointStrong
open OriginalKCrossParameterRAdjointSource.CayleyEnergySource
open SourceGeneratedActionObservationHistory.ContractiveRecovery Filter Function
open scoped Topology

local notation "R" => burnolDirectRightResolventCLM
local notation "A" => sourceCayley
local notation "d" => sourceDamping
local notation "F" => fourierL2

def drive (c : BurnolCompletedMellinCoordinate) (y : BurnolL2) : BurnolL2 :=
  (-(d c : ℂ)) • y

def entrance (c : BurnolCompletedMellinCoordinate) (y : BurnolL2) (n : Nat) : BurnolL2 :=
  approximate (A c) (drive c y) n

theorem drive_source (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    drive c (R c x) = x-A c x := by
  rw [sourceCayley_apply, drive]
  change (-(d c : ℂ)) • R c x = x-(x+(d c : ℂ) • R c x)
  rw [neg_smul]
  abel

private theorem contraction (c : BurnolCompletedMellinCoordinate) : ‖A c‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [sourceCayley_norm, one_mul]

private theorem resolvent_separates_zero (c : BurnolCompletedMellinCoordinate) (x : BurnolL2)
    (zero : R c x = 0) : x = 0 := by
  have recovered := CountedCellInverse.recover_input c x
  rw [zero] at recovered
  have flat : (fun h : ℝ => burnolMultiplicativeDilation h (0 : BurnolL2)) = fun _ => 0 := by
    funext h
    exact map_zero _
  simpa only [CountedCellInverse.recoverInput, flat, deriv_const, smul_zero, add_zero] using recovered.symm

theorem entrance_tendsto (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    Tendsto (entrance c (R c x)) atTop (𝓝 x) := by
  change Tendsto (approximate (A c) (drive c (R c x))) atTop (𝓝 x)
  rw [drive_source]
  apply recover (A c) (contraction c) _ x
  intro z fixed
  rw [sourceCayley_apply] at fixed
  change z+(d c : ℂ) • R c z = z at fixed
  have erased : (d c : ℂ) • R c z = 0 := add_left_cancel (fixed.trans (add_zero z).symm)
  exact resolvent_separates_zero c z
    ((smul_eq_zero.mp erased).resolve_left (Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'))

/-- Two successive actual resolvent fields provide the explicit finite entrance error. -/
theorem entrance_error (c : BurnolCompletedMellinCoordinate) (previous : BurnolL2) (n : Nat) :
    ‖entrance c (R c (R c previous)) n-R c previous‖ ≤
      2*‖previous‖/(d c*((n : ℝ)+1)) := by
  let z := (-(d c : ℂ)⁻¹) • previous
  have nonzero := Complex.ofReal_ne_zero.mpr (sourceDamping_pos c).ne'
  have range : z-A c z = R c previous := by
    rw [← drive_source, drive]
    dsimp only [z]
    rw [map_smul, smul_smul, neg_mul_neg, mul_inv_cancel₀ nonzero, one_smul]
  have size : ‖z‖ = ‖previous‖ / d c := by
    dsimp only [z]
    rw [norm_smul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sourceDamping_pos c), div_eq_inv_mul]
  rw [entrance, drive_source]
  have error := range_error (A c) (contraction c) z n
  rw [range, size] at error
  simpa only [div_div, mul_div_assoc] using error

theorem entrance_data_error (c : BurnolCompletedMellinCoordinate) (left right : BurnolL2) (n : Nat) :
    ‖entrance c left n-entrance c right n‖ ≤ (n : ℝ)*d c*‖left-right‖ := by
  have error := SourceGeneratedActionObservationHistory.ContractiveRecovery.error
    (A c) (contraction c) (drive c left) (drive c right) n
  have size : ‖drive c left-drive c right‖ = d c*‖left-right‖ := by
    rw [drive, drive, ← smul_sub, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (sourceDamping_pos c)]
  rw [size, ← mul_assoc] at error
  exact error

/-- The wave action is the original positive-time resolvent, on the entire Fourier field. -/
def waveAction (c : BurnolCompletedMellinCoordinate) : BurnolL2 →L[ℂ] BurnolL2 :=
  (F).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((A c).comp (F).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem waveAction_source (c : BurnolCompletedMellinCoordinate) (x : BurnolL2) :
    waveAction c x = x+(d c : ℂ) • FiniteMobiusResolventFlux.Rplus (c.value/2) x := by
  have right : 1/4 < (c.value/2).re := by
    rw [Complex.div_re]
    norm_num
    linarith [c.rightHalf]
  change F (A c ((F).symm x)) = _
  rw [sourceCayley_apply, map_add, map_smul, (F).apply_symm_apply, FiniteMobiusResolventFlux.fourier_R _ right,
    (F).apply_symm_apply]

def waveEntrance (c : BurnolCompletedMellinCoordinate) (y : BurnolL2) (n : Nat) : BurnolL2 :=
  approximate (waveAction c) (drive c y) n

theorem entrance_fourier (c : BurnolCompletedMellinCoordinate) (y : BurnolL2) (n : Nat) :
    F (entrance c y n) = waveEntrance c (F y) n := by
  have intertwines : Semiconj F (step (A c) (drive c y))
      (step (waveAction c) (drive c (F y))) := by
    intro x
    change F (A c x+drive c y) = waveAction c (F x)+drive c (F y)
    rw [map_add, drive, map_smul, drive]
    exact congrArg (fun z : BurnolL2 => z + (-(d c : ℂ)) • F y)
      (congrArg (fun z : BurnolL2 => F (A c z)) ((F).symm_apply_apply x).symm)
  unfold entrance waveEntrance approximate birkhoffAverage birkhoffSum
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (intertwines.iterate_right j 0).trans (congrArg _ (map_zero F))

end CountedCayleyInverse
end NoIslandNoMagic.CanonicalRiemann.ClozelGeneralizedDual.CenteredGram.IntegralGraphJointAction.OriginalKDirectRCofinalDivision
end SaturationMonoid.ResponsibilityLifecycle.LivingLawEvolution.ConstructiveRoot
