import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualWholePhysicalChargeCorrection
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationActualMomentumPencil

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualElectronWholeChargeSoft
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open ActualElectronPhysicalJointInverse PreparationVacuumJointFieldResponse SourcePropagationCommonMomentum
open ActualSourceMixed289ResponseOwn Filter
open scoped Topology InnerProductSpace
attribute [local irreducible] jointGenerator jointResolvent actualElectronPhysicalSeed
  actualElectronPhysicalResponse actualElectronPhysicalUnit momentumCompressionMap

private theorem inverse_difference {A : Type*} [Ring A] (D0 D1 R0 R1 : A)
    (right0 : D0*R0=1) (left1 : R1*D1=1) :R1-R0=-(R1*(D1-D0)*R0) := by
  have eq : R1*(D1-D0)*R0=R0-R1 := by
    rw [mul_sub,sub_mul,left1,one_mul,mul_assoc,right0,mul_one]
  rw [eq,neg_sub]

/-- The literal uncut Y is common; only the source momentum compression changes. -/
theorem actual_electron_physical_inverse_difference (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0) :
    jointResolvent (p+k) F z 0-jointResolvent p F z 0=
      -(jointResolvent (p+k) F z 0*momentumCompressionMap F k*jointResolvent p F z 0) := by
  have difference:=inverse_difference (jointGenerator p F z 0) (jointGenerator (p+k) F z 0)
    (jointResolvent p F z 0) (jointResolvent (p+k) F z 0)
    (actual_electron_joint_inverse_right p F z hz) (actual_electron_joint_inverse_left (p+k) F z hz)
  exact difference.trans (congrArg (fun E : H→L[ℂ]H=>
    -(jointResolvent (p+k) F z 0*E*jointResolvent p F z 0))
      (jointGenerator_momentum_difference p k F z))

def actualElectronPhysicalMomentumPrice (p k : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) : ℝ :=
  originalJointResolventPrice (p+k) F z*‖momentumCompressionMap F‖*‖k‖*originalJointResolventPrice p F z

theorem actual_electron_physical_inverse_difference_price (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0) :
    ‖jointResolvent (p+k) F z 0-jointResolvent p F z 0‖≤actualElectronPhysicalMomentumPrice p k F z := by
  rw [actual_electron_physical_inverse_difference p k F z hz,norm_neg]
  calc
    _≤‖jointResolvent (p+k) F z 0*momentumCompressionMap F k‖*‖jointResolvent p F z 0‖ := norm_mul_le _ _
    _≤(‖jointResolvent (p+k) F z 0‖*‖momentumCompressionMap F k‖)*‖jointResolvent p F z 0‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _≤(originalJointResolventPrice (p+k) F z*(‖momentumCompressionMap F‖*‖k‖))*originalJointResolventPrice p F z :=
      mul_le_mul (mul_le_mul (originalJointResolvent_price (p+k) F z hz)
        ((momentumCompressionMap F).le_opNorm k) (norm_nonneg _) ((norm_nonneg (jointResolvent (p+k) F z 0)).trans (originalJointResolvent_price (p+k) F z hz)))
        (originalJointResolvent_price p F z hz) (norm_nonneg _)
        (mul_nonneg ((norm_nonneg (jointResolvent (p+k) F z 0)).trans (originalJointResolvent_price (p+k) F z hz)) (mul_nonneg (norm_nonneg (momentumCompressionMap F)) (norm_nonneg k)))
    _=_ := by unfold actualElectronPhysicalMomentumPrice;ring

theorem actual_electron_physical_response_difference_price (p k : PhysicalMomentum)
    (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) :
    ‖actualElectronPhysicalResponse (p+k) F z leg-actualElectronPhysicalResponse p F z leg‖≤
      actualElectronPhysicalMomentumPrice p k F z := by
  unfold actualElectronPhysicalResponse
  change ‖(jointResolvent (p+k) F z 0-jointResolvent p F z 0) (actualElectronPhysicalSeed leg)‖≤_
  calc
    _≤‖jointResolvent (p+k) F z 0-jointResolvent p F z 0‖*‖actualElectronPhysicalSeed leg‖ :=
      (jointResolvent (p+k) F z 0-jointResolvent p F z 0).le_opNorm _
    _≤_ := by rw [actual_electron_physical_seed_norm,mul_one];exact actual_electron_physical_inverse_difference_price p k F z hz

/-- This continuity is generated from the actual affine physical generator and its actual nonreal inverse. -/
theorem actual_electron_physical_resolvent_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0) :
    Continuous (fun p : PhysicalMomentum=>jointResolvent p F z 0) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨u,hu⟩:=jointGenerator_unit p F z hz
  have inverse : ContinuousAt (Ring.inverse : (H→L[ℂ]H)→(H→L[ℂ]H)) (jointGenerator p F z 0) := by
    rw [←hu]
    exact (contDiffAt_ringInverse ℝ (n:=1) u).continuousAt
  unfold jointResolvent
  change ContinuousAt (fun p : PhysicalMomentum=>Ring.inverse (jointGenerator p F z 0)) p
  exact inverse.comp (f:=fun q : PhysicalMomentum=>jointGenerator q F z 0) (x:=p)
    (jointGenerator_base_continuous F z).continuousAt

theorem actual_electron_physical_response_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0)
    (leg : CompositeLeg) :Continuous (fun p : PhysicalMomentum=>actualElectronPhysicalResponse p F z leg) := by
  unfold actualElectronPhysicalResponse
  exact (actual_electron_physical_resolvent_continuous F z hz).clm_apply continuous_const

theorem actual_electron_physical_unit_continuous (F : GaussUnitaryHistory.Index) (z : ℂ) (hz : z.im≠0)
    (leg : CompositeLeg) :Continuous (fun p : PhysicalMomentum=>actualElectronPhysicalUnit p F z leg) := by
  have raw:=actual_electron_physical_response_continuous F z hz leg
  apply continuous_iff_continuousAt.mpr
  intro p
  have nz : (‖actualElectronPhysicalResponse p F z leg‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (actual_electron_physical_response_nonzero p F z hz leg))
  unfold actualElectronPhysicalUnit
  exact (((Complex.continuous_ofReal.comp raw.norm).continuousAt).inv₀ nz).smul raw.continuousAt

/-- No exchange with the sourceFilter limit is used in this ordinary finite-frame transfer limit. -/
theorem actual_electron_physical_finite_soft_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (hz : z.im≠0) (leg : CompositeLeg) :
    Tendsto (fun k : PhysicalMomentum=>actualElectronPhysicalUnit (p+k) F z leg) (𝓝 0)
      (𝓝 (actualElectronPhysicalUnit p F z leg)) := by
  simpa only [Function.comp_def,Pi.add_apply,id_eq,add_zero] using ((actual_electron_physical_unit_continuous F z hz leg).comp
    ((continuous_const (y:=p)).add continuous_id)).tendsto (0:PhysicalMomentum)

end LowEnergy.GaussComposite.ActualElectronWholeChargeSoft
