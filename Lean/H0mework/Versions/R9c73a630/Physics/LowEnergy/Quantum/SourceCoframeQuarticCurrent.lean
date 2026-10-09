import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeSpinContraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceCoframeQuarticCurrent
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open GaussCoframeForm SourceCoframeCovariantAction SourceCoframeCovariantSquare SourceCoframeSpinNormalOrder
open SourceCoframeSpinContraction SourceMatterContactNative SourceContactFullFlux SourceContactTimeBalance
open scoped ContDiff
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest

/-- The original four-operator kernel acts with the original inverse-volume coefficient. -/
def quarticAction : End := multiply inverseVolume inverseVolume_smooth *
  localMultiplier (fun _ => quartic) (fun _ => contDiffAt_const)

private theorem number_shift_value (f : QuantumTest) (z : SourceCoordinateSlice) :
    numberShift f z=(inverseVolume z : ℂ) • ((-9/8 : ℂ) • fiberNumber (f z)) := by
  have hn (q : QuantumTest) : number q z=fiberNumber (q z) := by
    apply PiLp.ext
    intro w
    exact (number_apply q z w).trans (fiberNumber_apply (q z) w).symm
  change (1/2 : ℂ) • (number (multiply numberCoefficient numberCoefficient_smooth f) z+
    multiply numberCoefficient numberCoefficient_smooth (number f) z)=_
  rw [hn,multiply_apply,multiply_apply,hn,map_smul]
  simp only [numberCoefficient,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_div,
    Complex.ofReal_ofNat,smul_add,smul_smul]
  module

/-- The complete spin remainder separates its genuine CAR interaction from its commuting Number term. -/
theorem original_spin_quartic_action : spinRemainder=quarticAction+(5/6 : ℂ) • numberShift := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  have h := original_spin_normal_action f z
  rw [original_one_body_number] at h
  change spinRemainder f z+numberShift f z=_ at h
  rw [number_shift_value] at h
  simp only [add_apply,smul_apply,smul_add,smul_smul] at h
  change spinRemainder f z=(inverseVolume z : ℂ) • quartic (f z)+(5/6 : ℂ) • numberShift f z
  rw [number_shift_value]
  rw [eq_sub_of_add_eq h]
  module

/-- The full source coframe action retains only one true local quartic interaction. -/
theorem original_coframe_quartic_action : coframeAction=covariantKinetic+quarticAction+
    (11/6 : ℂ) • numberShift+multiply volumePotential volumePotential_smooth := by
  rw [original_coframe_covariant,original_spin_quartic_action]
  module

/-- Both local factors are evaluated on the same source occurrence; no static-carrier compatibility premise is used. -/
theorem original_quartic_gram_current (f : QuantumTest) (z : SourceCoordinateSlice) :
    ((quarticAction*gramAction-gramAction*quarticAction) f) z=
      (inverseVolume z : ℂ) • ((quartic*gramFiber z-gramFiber z*quartic) (f z)) := by
  change quarticAction (gramAction f) z-gramAction (quarticAction f) z=_
  rw [original_contact_gram_value]
  change (inverseVolume z : ℂ) • quartic (gramAction f z)-
    gramFiber z ((inverseVolume z : ℂ) • quartic (f z))=_
  rw [original_contact_gram_value,map_smul]
  simp only [sub_apply,mul_apply_eq_comp,smul_sub]

/-- The Number contraction exits the exact dynamic current; the full four-operator commutator remains. -/
theorem original_reduced_quartic_current : reducedCurrent=
    (covariantKinetic+quarticAction+GaussMatterCore.matterAction)*gramAction-
      gramAction*(covariantKinetic+quarticAction+GaussMatterCore.matterAction) := by
  rw [reducedCurrent,original_coframe_quartic_action]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
  rw [original_number_volume_contact.1.eq,original_number_volume_contact.2.eq]
  abel

end LowEnergy.SourceCoframeQuarticCurrent
