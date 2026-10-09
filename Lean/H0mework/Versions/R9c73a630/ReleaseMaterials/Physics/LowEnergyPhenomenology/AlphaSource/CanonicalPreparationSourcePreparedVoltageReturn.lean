import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceVoltageGreenRecovery
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceActionFieldFeed
import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhysicalEnergyChannels

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalVoltageCompleteReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage9C.Material.SpinPair FullQuantum FullSpace
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCausalPoleResponse
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalCharacteristic
open PreparationVacuumStaticVoltageSource PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumMatterEulerFeedback PreparationVacuumMixedFieldReturn
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedEnergyVariation
open PreparationVacuumGaugeSourceInjection PreparationVacuumOrderedRealSignal CanonicalGradedSpatialSource
open MeasureTheory Filter
open scoped Matrix BigOperators Topology
attribute [local irreducible] originalJacobi originalChange originalInverse originalReadback originalRowLift
  sourceGreen sourceCompatibility modeForcing sourceVoltageLaplaceRamp

private theorem lapse_coefficient : (6/25:ℂ)*rootTwo*rootFifteen=2*(lapse:ℂ) := by
  have two : (Real.sqrt 2)^2=2:=Real.sq_sqrt (by norm_num)
  have fifteen : (Real.sqrt 15)^2=15:=Real.sq_sqrt (by norm_num)
  have positive : 0≤(3/25:ℝ)*Real.sqrt 2*Real.sqrt 15:=by positivity
  have equal : (3/25:ℝ)*Real.sqrt 2*Real.sqrt 15=lapse:=by
    nlinarith [lapse_sq,lapse_pos,mul_self_nonneg ((3/25:ℝ)*Real.sqrt 2*Real.sqrt 15-lapse)]
  unfold rootTwo rootFifteen
  have h:=congrArg (fun x : ℝ=>(x:ℂ)) equal
  push_cast at h
  linear_combination 2*h

@[local simp] private theorem momentum_one (spatial : Fin 3→ℂ) (z : ℂ) : Fin.cases z spatial 1=spatial 0:=rfl
@[local simp] private theorem momentum_two (spatial : Fin 3→ℂ) (z : ℂ) : Fin.cases z spatial 2=spatial 1:=rfl
@[local simp] private theorem momentum_three (spatial : Fin 3→ℂ) (z : ℂ) : Fin.cases z spatial 3=spatial 2:=rfl

/-- The Gauss coordinate is extracted from the complete 38-term forcing, after retaining its other rows. -/
theorem sourceVoltageLaplaceForcing_gauss (wave : PhysicalMomentum) (z : ℂ) (nonzero : z≠0) :
    sourceVoltageLaplaceForcing (physicalSpatial wave) z 20=
      z⁻¹*(2*(lapse:ℂ)*(spatialSquare wave:ℂ)) := by
  norm_num [sourceVoltageLaplaceForcing,sourceVoltageRampTerms,sourceMatrix,SourceTerm.matrix,
    Powers.value,fullMomentum,Matrix.add_mulVec,Matrix.single_mulVec,Matrix.mulVec_single,Matrix.col,
    Matrix.add_apply,Matrix.single_apply,Pi.single_apply,Matrix.single,coefficientValue,
    QuadraticAlgebra.re_one,QuadraticAlgebra.im_one,Pi.smul_apply,smul_eq_mul,PreparationVacuumPhysicalFeedback.physicalSpatial,
    spatialSquare,Complex.ofReal_add,Complex.ofReal_pow,Fin.ext_iff]
  rw [←lapse_coefficient]
  field_simp [nonzero]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- Its scalar amplitude is read from the original prepared Euler source, rather than supplied as a desired field. -/
def sourcePreparedVoltageAmplitude (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (z : ℂ) (T : ℝ) : ℂ :=
  z*modeForcing q force true wave z T 20/(2*(lapse:ℂ)*(spatialSquare wave:ℂ))

def sourcePreparedVoltageRemainder (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (z : ℂ) (T : ℝ) : Fin 289→ℂ :=
  modeForcing q force true wave z T-
    sourcePreparedVoltageAmplitude q force wave z T • sourceVoltageLaplaceForcing (physicalSpatial wave) z

theorem sourcePreparedVoltageRemainder_gauss (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (z : ℂ) (nonzero : z≠0) (spatial : 0<spatialSquare wave) (T : ℝ) :
    sourcePreparedVoltageRemainder q force wave z T 20=0 := by
  simp only [sourcePreparedVoltageRemainder,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    sourceVoltageLaplaceForcing_gauss wave z nonzero,sourcePreparedVoltageAmplitude]
  have lapseNonzero : (lapse:ℂ)≠0:=Complex.ofReal_ne_zero.mpr lapse_pos.ne'
  have spatialNonzero : (spatialSquare wave:ℂ)≠0:=Complex.ofReal_ne_zero.mpr spatial.ne'
  field_simp [nonzero,lapseNonzero,spatialNonzero]
  ring

/-- Gauss extraction preserves all nine source compatibilities, including their initial and final cosources. -/
theorem sourcePreparedVoltageRemainder_compatibility (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (z : ℂ) (nonzero : z≠0) (T : ℝ) :
    sourceCompatibility (fullMomentum (physicalSpatial wave) z) (sourcePreparedVoltageRemainder q force wave z T)=
      sourceCompatibility (fullMomentum (physicalSpatial wave) z) (modeForcing q force true wave z T) := by
  unfold sourcePreparedVoltageRemainder sourceCompatibility
  rw [Matrix.mulVec_sub,Matrix.mulVec_smul,Matrix.mulVec_sub,Matrix.mulVec_smul]
  have compatible:=sourceVoltageLaplaceForcing_compatible (PreparationVacuumPhysicalFeedback.physicalSpatial wave) z nonzero
  unfold sourceCompatibility at compatible
  rw [compatible,smul_zero,sub_zero]

theorem sourcePreparedVoltage_return (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (z : physicalSpectralDomain wave) (nonzero : z.val≠0) (T : ℝ) :
    modeField q force true wave z T=
      sourcePreparedVoltageAmplitude q force wave z.val T •
        (sourceVoltageLaplaceRamp (physicalSpatial wave) z.val-
          originalChange (fullMomentum (physicalSpatial wave) z.val)*ᵥ(nullProjection*ᵥ
            (originalInverse (fullMomentum (physicalSpatial wave) z.val)*ᵥsourceVoltageLaplaceRamp (physicalSpatial wave) z.val)))+
      PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum (physicalSpatial wave) z.val,z.property⟩
        (sourcePreparedVoltageRemainder q force wave z.val T) := by
  rw [←sourceVoltageLaplaceRamp_recovered (physicalSpatial wave) z.val nonzero z.property]
  simp only [modeField,PreparationVacuumOriginalGreenFeedback.sourceField,sourcePreparedVoltageRemainder,
    Matrix.mulVec_sub,Matrix.mulVec_smul]
  module

/-- This is the derivative of the actual original matter-Euler field curve, not a second independent response model. -/
theorem sourcePreparedVoltage_action_return (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (z : physicalSpectralDomain wave) (nonzero : z.val≠0) (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) :
    deriv (actionFieldCurve q force wave z T) 0=
      sourcePreparedVoltageAmplitude q force wave z.val T •
        (sourceVoltageLaplaceRamp (physicalSpatial wave) z.val-
          originalChange (fullMomentum (physicalSpatial wave) z.val)*ᵥ(nullProjection*ᵥ
            (originalInverse (fullMomentum (physicalSpatial wave) z.val)*ᵥsourceVoltageLaplaceRamp (physicalSpatial wave) z.val)))+
      PreparationVacuumOriginalGreenFeedback.sourceField ⟨fullMomentum (physicalSpatial wave) z.val,z.property⟩
        (sourcePreparedVoltageRemainder q force wave z.val T) := by
  rw [(actionFieldCurve_generated q force wave z hz hw T).deriv]
  exact sourcePreparedVoltage_return q force wave z nonzero T

/-- The same physical Phi consumes the recovered voltage, its exact null data, and the complete residual field. -/
theorem sourcePreparedVoltage_energy_return (q : PhysicalResponsePoint) (force : Field289) (shift : Position)
    (z : physicalSpectralDomain (physicalMomentum shift)) (nonzero : z.val≠0)
    (hz : q.z.im≠0) (hw : q.w.im≠0) (T : ℝ) (sideL edgeL sideR edgeR : Fin 2) :
    sourcePhysicalEnergyReader shift sideL edgeL sideR edgeR
      (deriv (actionFieldCurve q force (physicalMomentum shift) z T) 0)=
      sourcePreparedVoltageAmplitude q force (physicalMomentum shift) z.val T*
        (sourceFullEnergyRead (sourceVoltageLaplaceRamp (physicalSpatial (physicalMomentum shift)) z.val)
            shift sideL edgeL sideR edgeR-
          sourceFullEnergyRead
            (originalChange (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ(nullProjection*ᵥ
              (originalInverse (fullMomentum (physicalSpatial (physicalMomentum shift)) z.val)*ᵥ
                sourceVoltageLaplaceRamp (physicalSpatial (physicalMomentum shift)) z.val))) shift sideL edgeL sideR edgeR)+
      sourceFullEnergyRead
        (PreparationVacuumOriginalGreenFeedback.sourceField
          ⟨fullMomentum (physicalSpatial (physicalMomentum shift)) z.val,z.property⟩
          (sourcePreparedVoltageRemainder q force (physicalMomentum shift) z.val T)) shift sideL edgeL sideR edgeR := by
  rw [sourcePreparedVoltage_action_return q force (physicalMomentum shift) z nonzero hz hw T]
  simp only [map_add,map_smul,map_sub,smul_eq_mul,sourcePhysicalEnergyReader_original]

/-- Every residual compatibility is the original prepared source window, with both boundary terms intact. -/
theorem sourcePreparedVoltageRemainder_cosources (q : PhysicalResponsePoint) (force : Field289) (wave : PhysicalMomentum)
    (z : physicalSpectralDomain wave) (nonzero : z.val≠0) (T : ℝ) (row : Fin 9) :
    sourceCompatibility (fullMomentum (physicalSpatial wave) z.val)
      (sourcePreparedVoltageRemainder q force wave z.val T) (compatibilitySlot row)=
      (∫t in (0:ℝ)..T,laplaceWeight z.val t*
        (compatibilityC0 (physicalSpatial wave) (fun i=>(modeJet q force true wave t i).value) row+
          compatibilityCtime (physicalSpatial wave) (fun i=>(modeJet q force true wave t i).first) row))-
        (modeBoundary q force true wave (physicalSpatial wave) z.val T (compatibilitySlot row)-
          compatibilityCtime (physicalSpatial wave) (fun i=>(modeJet q force true wave 0 i).value) row) := by
  rw [sourcePreparedVoltageRemainder_compatibility q force wave z.val nonzero T]
  exact actionFieldResponse_compatibility q force wave z T row

end LowEnergy.PreparationPhysicalVoltageCompleteReturn
