import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorPhaseCharge
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorSpin
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.NamedColorQtNext.Charge.MixedSpectatorOccupation
import H0mework.Versions.R9c73a630.ReleaseMaterials.Scratch.LowEnergyRetardedCouncil.ActiveMatterSectorCharge.SourceActiveMatterSectorCharge

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.MixedSpectatorCandidate
open SaturationMonoid.PhysicsCore
open SU7MotherLieAlgebra SU7ExteriorMatterRestriction
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge
open ActiveMatterSectorCharge
open scoped BigOperators InnerProductSpace

theorem actual_candidate_active_sector (dual : Bool) :
    ActiveMatterSectorCharge.occupation (fiberCoordinates (candidate dual)) =
      (if dual then (-3 : ℂ) else 3) • fiberCoordinates (candidate dual) := by
  have h := actual_candidate_constant_mode_charge
    (fun i => (modeWeight i : ℂ)) dual (if dual then (-1 : ℂ) else 1)
    (by intro i; cases dual <;> simp [modeWeight, primalWeight, rootMode, rootIndex])
  have hc := congrArg fiberCoordinates h
  simp only [fiberCharge, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply, map_smul] at hc
  cases dual <;> simpa [ActiveMatterSectorCharge.occupation] using hc

/-- The other eleven source diagonal sectors all live in Lambda4. The same
state annihilates every Lambda4 diagonal charge, including all their linear combinations. -/
def degreeFourWeight (q : ExteriorBasisIndex 4 → ℂ) (m : Mode) : ℂ :=
  match m with
  | .inl i => match i.2 with
    | .inr (.inr b) => q b
    | _ => 0
  | .inr i => match i.2 with
    | .inr (.inr b) => -q b
    | _ => 0

theorem actual_candidate_other_sectors_zero (dual : Bool) (q : ExteriorBasisIndex 4 → ℂ) :
    fiberCharge (degreeFourWeight q) (candidate dual) = 0 := by
  have h := actual_candidate_constant_mode_charge (degreeFourWeight q) dual 0
    (by intro i; cases dual <;> rfl)
  simpa only [mul_zero, zero_smul] using h

/-- One concrete original CAR state carries all the computed charges, the
actual spin Casimir and the full color kernel simultaneously. -/
theorem actual_charged_color_singlet_spin_half (dual : Bool) :
    inner ℂ (candidate dual) (candidate dual) = 2 ∧
    candidate dual ≠ 0 ∧
    phaseCharge (candidate dual) = (if dual then (-1 : ℂ) else 1) • candidate dual ∧
    NamedColorQtNext.originalSpinCasimir (candidate dual) = (3/4 : ℂ) • candidate dual ∧
    (∀ A : SU3BlockLieMatrix, GaussNativeMatter.nativeFock (colorNative A) (candidate dual) = 0) ∧
    ActiveMatterSectorCharge.occupation (fiberCoordinates (candidate dual)) =
      (if dual then (-3 : ℂ) else 3) • fiberCoordinates (candidate dual) ∧
    (∀ q : ExteriorBasisIndex 4 → ℂ, fiberCharge (degreeFourWeight q) (candidate dual) = 0) ∧
    GaussCoreLabel.fiberPiece (3,0) (candidate dual) = candidate dual :=
  ⟨actual_candidate_norm_sq dual, actual_candidate_nonzero dual,
    actual_candidate_phase_charge dual, actual_candidate_spin_half dual,
    fun A => actual_candidate_color_singlet A dual, actual_candidate_active_sector dual,
    actual_candidate_other_sectors_zero dual, actual_candidate_bottom_sector dual⟩

end LowEnergy.MixedSpectatorCandidate
