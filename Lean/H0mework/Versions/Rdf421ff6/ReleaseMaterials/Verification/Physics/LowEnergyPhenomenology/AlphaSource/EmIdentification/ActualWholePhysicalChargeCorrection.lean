import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualElectronPhysicalDomainAndContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronWholeChargeSoft
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open ActualElectronPhysicalJointInverse CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization
open SourceFamilyHilbert SourceFamilyOperator Filter
open scoped InnerProductSpace Topology
attribute [local irreducible] actualElectronPhysicalUnit actualElectronPhysicalChargeCorrection
  actualElectronPhysicalResponse chargeReader

abbrev ElectronFamily := SourceFamilyHilbert.Family H GaussUnitaryHistory.sourceFilter
abbrev ElectronHistory := GaussUnitaryHistory.HistorySpace

def actualElectronSign (leg : CompositeLeg) : ℂ:=if leg.dual then -1 else 1

theorem actual_electron_sign_norm (leg : CompositeLeg) : ‖actualElectronSign leg‖=1 := by
  unfold actualElectronSign
  split_ifs <;> norm_num

/-- The existing bounded charge acts on the actual physical output, so the mixing correction needs no uniform inverse-norm premise. -/
def actualWholeElectronCorrectionFamily (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) : ElectronFamily :=
  SourceFamilyOperator.act GaussUnitaryHistory.sourceFilter
    (SourceFamilyOperator.constant (chargeReader sourcePhaseGaugeLie))
    (actualElectronPhysicalStateFamily p z hz leg)-
      actualElectronSign leg • actualElectronPhysicalStateFamily p z hz leg

theorem actual_whole_electron_correction_value (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0)
    (leg : CompositeLeg) (F : GaussUnitaryHistory.Index) :
    value (actualWholeElectronCorrectionFamily p z hz leg) F=actualElectronPhysicalChargeCorrection p F z leg := by
  change chargeReader sourcePhaseGaugeLie (actualElectronPhysicalUnit p F z leg)-
    actualElectronSign leg • actualElectronPhysicalUnit p F z leg=_
  rw [actual_electron_physical_unit_charge p F z hz leg]
  exact add_sub_cancel_left _ _

theorem actual_whole_electron_correction_frame_bound (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0)
    (leg : CompositeLeg) (F : GaussUnitaryHistory.Index) :
    ‖value (actualWholeElectronCorrectionFamily p z hz leg) F‖≤‖chargeReader sourcePhaseGaugeLie‖+1 := by
  change ‖chargeReader sourcePhaseGaugeLie (actualElectronPhysicalUnit p F z leg)-
    actualElectronSign leg • actualElectronPhysicalUnit p F z leg‖≤_
  calc
    _≤‖chargeReader sourcePhaseGaugeLie (actualElectronPhysicalUnit p F z leg)‖+
      ‖actualElectronSign leg • actualElectronPhysicalUnit p F z leg‖ := norm_sub_le _ _
    _≤‖chargeReader sourcePhaseGaugeLie‖*‖actualElectronPhysicalUnit p F z leg‖+
      ‖actualElectronSign leg‖*‖actualElectronPhysicalUnit p F z leg‖ :=
        add_le_add ((chargeReader sourcePhaseGaugeLie).le_opNorm _) (norm_smul _ _).le
    _=_ := by rw [actual_electron_physical_unit_norm p F z hz leg,actual_electron_sign_norm,mul_one,one_mul]

def actualWholeElectronCorrection (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) : ElectronHistory :=
  (actualWholeElectronCorrectionFamily p z hz leg : ElectronHistory)

theorem actual_whole_electron_charge_equation (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) :
    GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) (actualElectronPhysicalState p z hz leg)=
      actualElectronSign leg • actualElectronPhysicalState p z hz leg+actualWholeElectronCorrection p z hz leg := by
  unfold actualElectronPhysicalState GaussUnitaryHistory.reader actualWholeElectronCorrection
  rw [SourceFamilyOperator.lift_coe,actualWholeElectronCorrectionFamily,
    UniformSpace.Completion.coe_sub,UniformSpace.Completion.coe_smul]
  abel

theorem actual_whole_electron_correction_bound (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) :
    ‖actualWholeElectronCorrection p z hz leg‖≤‖chargeReader sourcePhaseGaugeLie‖+1 := by
  rw [actualWholeElectronCorrection,UniformSpace.Completion.norm_coe]
  exact norm_le_of_eventually GaussUnitaryHistory.sourceFilter _ _
    (Eventually.of_forall (actual_whole_electron_correction_frame_bound p z hz leg))

/-- Distinct actual external legs retain their overlap and right-leg mixing correction in the same complete carrier. -/
theorem actual_whole_electron_paired_charge (pL pR : PhysicalMomentum) (z w : ℂ)
    (hz : z.im≠0) (hw : w.im≠0) (left right : CompositeLeg) :
    inner ℂ (actualElectronPhysicalState pL z hz left)
      (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) (actualElectronPhysicalState pR w hw right))=
    actualElectronSign right*inner ℂ (actualElectronPhysicalState pL z hz left) (actualElectronPhysicalState pR w hw right)+
      inner ℂ (actualElectronPhysicalState pL z hz left) (actualWholeElectronCorrection pR w hw right) := by
  rw [actual_whole_electron_charge_equation,inner_add_right,inner_smul_right]

/-- The zero-transfer diagonal reads the actual physical output correction, with its whole-carrier source value. -/
theorem actual_whole_electron_diagonal_charge (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) :
    inner ℂ (actualElectronPhysicalState p z hz leg)
      (GaussUnitaryHistory.reader (chargeReader sourcePhaseGaugeLie) (actualElectronPhysicalState p z hz leg))=
    actualElectronSign leg+inner ℂ (actualElectronPhysicalState p z hz leg) (actualWholeElectronCorrection p z hz leg) := by
  rw [actual_whole_electron_paired_charge,inner_self_eq_norm_sq_to_K,
    actual_electron_physical_state_norm]
  norm_num

theorem actual_whole_electron_correction_read_return (p : PhysicalMomentum) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) :
    Tendsto (fun F=>inner ℂ (actualElectronPhysicalUnit p F z leg) (actualElectronPhysicalChargeCorrection p F z leg))
      GaussUnitaryHistory.sourceFilter
      (𝓝 (inner ℂ (actualElectronPhysicalState p z hz leg) (actualWholeElectronCorrection p z hz leg))) := by
  rw [actualElectronPhysicalState,actualWholeElectronCorrection,inner_coe]
  exact (pair_tendsto GaussUnitaryHistory.sourceFilter (actualElectronPhysicalStateFamily p z hz leg)
    (actualWholeElectronCorrectionFamily p z hz leg)).congr'
      (Eventually.of_forall (fun F=>by rw [actual_whole_electron_correction_value];rfl))

end LowEnergy.GaussComposite.ActualElectronWholeChargeSoft
