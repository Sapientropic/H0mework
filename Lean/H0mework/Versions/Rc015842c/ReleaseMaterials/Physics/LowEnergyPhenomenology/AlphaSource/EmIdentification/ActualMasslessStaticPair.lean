import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualMasslessCurrent
import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceStaticSpatialCoupling

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualMasslessStaticPair
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10 CanonicalGradedSpatialSource
open PreparationVacuumElectromagneticIdentity PreparationVacuumPhysicalFeedback
open PreparationVacuumOriginalGreenFeedback PreparationVacuumFullOriginResponse
open PreparationVacuumStaticPoleResponse PreparationVacuumFullPoleContinuation
open PreparationVacuumPhysicalConstraint114 PreparationVacuumRawJointFeedback
open PreparationVacuumRestModeCoupling PreparationVacuumMixedFieldReturn
open PreparationPhysicalActualLegNormalization PreparationVacuumLowerClassical PreparationVacuumPhysicalPoleSheet
open PreparationVacuumPhysicalCharacteristic PreparationPhysicalStaticSpatialCouplingReturn
open ActualEMObservable ActualEMResponseSplit ActualElectronOwnerTest ActualMasslessCurrent
open Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] fullNativeOrigin actualElectronFieldTest actualJointKernel

def actualStaticPairSeed : ℂ := (9023/9000:ℂ)*rootTwo*rootFifteen

private theorem static_inverse_pair (w : ℂ) :
    staticInverse*ᵥ(Pi.single 0 w+Pi.single 1 w)=
      Pi.single 0 ((-9/125:ℂ)*rootTwo*rootFifteen*w)+
      Pi.single 1 ((-67/72:ℂ)*rootTwo*rootFifteen*w) := by
  norm_num [staticInverse,staticInverseTerms,sourceMatrix,SourceTerm.matrix,Powers.value,coefficientValue,
    Matrix.add_mulVec,Matrix.zero_mulVec,Matrix.single_mulVec,Pi.add_apply,Pi.single_apply,Fin.ext_iff]
  congr 1

/-- Both actual current endpoints retain all64 preparation and the entire unit-leg corrections. -/
theorem actualUnitMasslessWeight_return (q : PhysicalResponsePoint) (sideL sideR : Fin 2)
    (mu : ℂ) (S : ℝ) (hz : q.z.im≠0) (hw : q.w.im≠0) :
    actualUnitMasslessWeight q sideL sideR mu S=
      sourceActualLegNormalization q sideL 0 sideR 0*
        (actualPreparedMasslessWeight q sideL sideR mu S-
          (fullNativeOrigin.transpose*ᵥemUnitSourceCorrection q sideL sideR mu S) 0) := by
  have result:=congrFun (actualUnitMasslessCurrent_generated q sideL sideR mu S hz hw) 0
  rw [actualUnitMasslessCurrent_complete] at result
  simpa only [Pi.add_apply,Pi.single_apply,Pi.smul_apply,Pi.sub_apply,smul_eq_mul,Fin.reduceEq,if_true,if_false,add_zero] using result

/-- This scalar is one original static inverse acting between two independently generated actual currents. -/
theorem actual_unit_static_pair (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) :
    dotProduct (emUnitSourceCurrent qd dL dR lambda T)
      (staticResidue (emUnitSourceCurrent qs sL sR mu S))=
      -actualStaticPairSeed*actualUnitMasslessWeight qd dL dR lambda T*
        actualUnitMasslessWeight qs sL sR mu S := by
  have transpose_pair (M : Matrix (Fin 289) (Fin 289) ℂ) (u v : Fin 289→ℂ) :
      dotProduct u (M*ᵥv)=dotProduct (M.transpose*ᵥu) v := by
    simp only [Matrix.mulVec,dotProduct,Matrix.transpose_apply,Finset.mul_sum,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold staticResidue
  rw [transpose_pair,actualUnitMasslessCurrent_complete,actualUnitMasslessCurrent_complete,
    static_inverse_pair]
  simp only [dotProduct_add,dotProduct_single,Pi.add_apply,Pi.single_apply]
  norm_num [Fin.ext_iff]
  unfold actualStaticPairSeed
  ring

/-- The detector carries exactly one source action unit; the source current carries none. -/
theorem actual_unit_detector_factor (branch : Fin 2) (q : PhysicalResponsePoint)
    (sideL sideR : Fin 2) (lambda : ℂ) (T : ℝ) :
    emUnitDetectorCovector branch q sideL sideR lambda T=
      (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)⁻¹) •
        emUnitSourceCurrent q sideL sideR lambda T := by
  funext i
  simp only [emUnitDetectorCovector,actualElectronFieldTest,emUnitSourceCurrent,emUnitSourceTest,
    smul_apply,Pi.smul_apply]

/-- Both complete actual unit endpoints observe the same whole-field Coulomb coefficient with a single hc. -/
theorem actual_unit_static_observable (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) :
    actualElectronFieldTest branch qd dL dR lambda T
      (staticResidue (emUnitSourceCurrent qs sL sR mu S))=
      -actualStaticPairSeed*actualUnitMasslessWeight qd dL dR lambda T*
        actualUnitMasslessWeight qs sL sR mu S/
          (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)) := by
  rw [←em_unit_detector_actual,actual_unit_detector_factor,smul_dotProduct,actual_unit_static_pair]
  simp only [smul_eq_mul,div_eq_mul_inv]
  ring

/-- The same complete source and actual detector directly consume the original static-field pole limit. -/
theorem actual_unit_static_native_limit (branch : Fin 2) (qd qs : PhysicalResponsePoint)
    (dL dR sL sR : Fin 2) (lambda mu : ℂ) (T S : ℝ) :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      actualElectronFieldTest branch qd dL dR lambda T
        (staticNativeField kappa (emUnitSourceCurrent qs sL sR mu S))) staticApproach
      (𝓝 (actualStaticPairSeed*actualUnitMasslessWeight qd dL dR lambda T*
        actualUnitMasslessWeight qs sL sR mu S/
          (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)))) := by
  have result:=((actualElectronFieldTest branch qd dL dR lambda T).continuous.tendsto _).comp
    (staticNativeField_residue (emUnitSourceCurrent qs sL sR mu S))
  rw [actual_unit_static_observable] at result
  simpa only [Function.comp_def,map_smul,smul_eq_mul,neg_mul,neg_div,neg_neg] using result.neg

/-- The physical full Green on its original nonempty static ray has the identical actual unit coefficient. -/
theorem actual_unit_full_green_limit (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (branch : Fin 2) (qd qs : PhysicalResponsePoint) (dL dR sL sR : Fin 2)
    (lambda mu : ℂ) (T S : ℝ) :
    Tendsto (fun kappa : staticDomain=>(kappa.val:ℂ)^2*
      emCurrentObservation (sourceGreen (sourceSpatialStaticRegularPoint n unit kappa))
        (emUnitDetectorCovector branch qd dL dR lambda T) (emUnitSourceCurrent qs sL sR mu S))
      staticApproach
      (𝓝 (actualStaticPairSeed*actualUnitMasslessWeight qd dL dR lambda T*
        actualUnitMasslessWeight qs sL sR mu S/
          (((ActionNormalization.phaseMomentum*sourceSpeed branch:ℝ):ℂ)))) := by
  have result:=((actualElectronFieldTest branch qd dL dR lambda T).continuous.tendsto _).comp
    (sourceSpatialStaticNativeFieldResidue n unit (emUnitSourceCurrent qs sL sR mu S))
  rw [actual_unit_static_observable] at result
  simpa only [Function.comp_def,map_smul,smul_eq_mul,sourceSpatialStaticNativeField,
    PreparationVacuumOriginalGreenFeedback.sourceField,←em_unit_detector_actual,emCurrentObservation,
    neg_mul,neg_div,neg_neg] using result.neg

end LowEnergy.GaussComposite.ActualMasslessStaticPair
