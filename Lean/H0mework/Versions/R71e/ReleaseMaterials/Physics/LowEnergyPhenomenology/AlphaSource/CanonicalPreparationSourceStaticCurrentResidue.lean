import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceObservedFieldVertex

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumObservedStaticResidue
open PreparationVacuumObservedPoleTensor PreparationVacuumPhysicalFeedback
open CanonicalGradedSpatialSource PreparationVacuumElectromagneticIdentity
open PreparationVacuumQuantumSlowResidue PreparationVacuumQuantumSlowResponse
open PreparationVacuumPhysicalSlowBlock PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumMovingPoleGaussReturn
open PreparationVacuumPhysicalPoleHalfResponse
open Filter Set
open scoped Topology
attribute [local irreducible] sourceEqualProjection sourceRetainerReturn sourceFullInitialUpper
  sourceFullInitialBase sourcePinnedResolvent sourcePoleRead sourceOriginInverse sourceBaseResidue sourceUpperResidue

/-- The actual zero-velocity channel returns twice through the original retainer. -/
def sourceStaticBase (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) : SourceOp :=
  -(sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
    (sourceRetainerReturn q.F (sourceResonanceProjection q.F n 0*
      sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))))

def sourceStaticUpper (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) : SourceOp :=
  sourceResonanceProjection q.F n 0*sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)

def sourceStaticGauge (q : PhysicalResponsePoint) (n : PhysicalMomentum) (mu : Fin 4) (a : Fin 12) : SourceOp :=
  sourceResonanceProjection q.F n 0*sourceEqualProjection q.F
    (sourceFullInitialBase q 0 0 (PreparationVacuumMixedFieldReturn.gaugeSlot mu a))

private theorem projected_origin (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum)
    (zeta : ℂ) (X : SourceOp) :
    sourceOriginInverse F n zeta (sourceEqualProjection F X)=
      sourcePinnedResolvent F n zeta*sourceEqualProjection F X := by
  have idem:=congrArg (fun A : SourceSuperOp=>A X) (sourceEqualProjection_idempotent F)
  change sourceEqualProjection F (sourceEqualProjection F X)=sourceEqualProjection F X at idem
  simp only [sourceOriginInverse,add_apply,sourcePinnedLeadingInverse_apply,
    sourceOffProjection,sub_apply,one_apply_eq_self,idem,sub_self,add_zero]

private theorem scaled_base (q : PhysicalResponsePoint) (n : PhysicalMomentum) (eta : ℝ) (i : Fin 289) :
    ((eta:ℂ)^2) • sourceBaseResidue q n (eta:ℂ) i=
      -(((eta:ℂ) • sourcePinnedResolvent q.F n (eta:ℂ))*sourceEqualProjection q.F
        (sourceRetainerReturn q.F (((eta:ℂ) • sourcePinnedResolvent q.F n (eta:ℂ))*
          sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i)))) := by
  simp only [sourceBaseResidue,sourceUpperResidue,projected_origin]
  simp only [smul_mul_assoc,map_smul,mul_smul_comm,smul_neg,smul_smul,pow_two]

private theorem static_resolvent (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • sourcePinnedResolvent F n (eta:ℂ))
      (𝓝[>] 0) (𝓝 (sourceResonanceProjection F n 0)) := by
  simpa only [sourcePoleSide,Complex.ofReal_zero,mul_zero,add_zero] using sourcePinnedResolvent_residue F n 0

/-- Actual B1 is consumed, with the source-generated resonance projector and no gap premise. -/
theorem sourceStaticUpper_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • sourceUpperResidue q n (eta:ℂ) i)
      (𝓝[>] 0) (𝓝 (sourceStaticUpper q n i)) := by
  have h:=(static_resolvent q.F n).mul_const (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))
  simpa only [sourceUpperResidue,projected_origin,sourceStaticUpper,smul_mul_assoc] using h

/-- The full actual base returns the double zero-velocity retainer coefficient. -/
theorem sourceStaticBase_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (i : Fin 289) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceBaseResidue q n (eta:ℂ) i)
      (𝓝[>] 0) (𝓝 (sourceStaticBase q n i)) := by
  have inner:=(static_resolvent q.F n).mul_const (sourceEqualProjection q.F (sourceFullInitialUpper q 0 0 i))
  have retained:=(sourceRetainerReturn q.F).continuous.continuousAt.tendsto.comp inner
  have projected:=(sourceEqualProjection q.F).continuous.continuousAt.tendsto.comp retained
  have result:=((static_resolvent q.F n).mul projected).neg
  simpa only [Function.comp_def,sourceStaticBase,scaled_base] using result

theorem sourceStaticGauge_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (mu : Fin 4) (a : Fin 12) :
    Tendsto (fun eta : ℝ=>(eta:ℂ) • sourceGaugeResidue q n (eta:ℂ) mu a)
      (𝓝[>] 0) (𝓝 (sourceStaticGauge q n mu a)) := by
  have h:=(static_resolvent q.F n).mul_const
    (sourceEqualProjection q.F (sourceFullInitialBase q 0 0 (PreparationVacuumMixedFieldReturn.gaugeSlot mu a)))
  simpa only [sourceGaugeResidue,projected_origin,sourceStaticGauge,smul_mul_assoc] using h

def sourceStaticCurrent (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) : Fin 289→ℂ :=
  fun i=> -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceStaticBase q n i)

def sourceStaticGaugeCurrent (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) : ℂ :=
  -sourcePoleRead q.epsilon q.precision 0 0 l r (sourceStaticGauge q n mu a)

/-- Every original field component is returned on the same common-eight external carrier. -/
theorem sourceStaticCurrent_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum) (l r : RestStateIndex) :
    Tendsto (fun eta : ℝ=>((eta:ℂ)^2) • sourceFullCurrentResidue q n (eta:ℂ) l r)
      (𝓝[>] 0) (𝓝 (sourceStaticCurrent q n l r)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  have h:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp
    (sourceStaticBase_generated q n i)).neg
  simpa only [Function.comp_def,sourceStaticCurrent,sourceFullCurrentResidue,Pi.smul_apply,map_smul,smul_neg] using h

theorem sourceStaticGaugeCurrent_generated (q : PhysicalResponsePoint) (n : PhysicalMomentum)
    (l r : RestStateIndex) (mu : Fin 4) (a : Fin 12) :
    Tendsto (fun eta : ℝ=>(eta:ℂ)*sourceGaugeCurrentResidue q n (eta:ℂ) l r mu a)
      (𝓝[>] 0) (𝓝 (sourceStaticGaugeCurrent q n l r mu a)) := by
  have h:=((sourcePoleRead q.epsilon q.precision 0 0 l r).continuous.continuousAt.tendsto.comp
    (sourceStaticGauge_generated q n mu a)).neg
  simpa only [Function.comp_def,sourceStaticGaugeCurrent,sourceGaugeCurrentResidue,map_smul,smul_neg,smul_eq_mul,mul_neg] using h

end LowEnergy.PreparationVacuumObservedStaticResidue
