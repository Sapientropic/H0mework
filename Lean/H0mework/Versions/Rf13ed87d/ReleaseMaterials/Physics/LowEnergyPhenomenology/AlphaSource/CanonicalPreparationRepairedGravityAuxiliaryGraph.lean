import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRepairedGravitySourceJets
import H0mework.Physics.DualVariation.GravityMultiplierAuxiliaryVariation

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumRepairedGravityActionReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction StageNineBlockwiseConstitutive StageNineEnrichedProofFreeSource
open StageNineFormNativeMotherAction StageNineDiracDualFormNativeMotherAction
open StageNineTopologicalFourFormPairing StageNineTopologicalGravityCurvatureVariancePairing
open StageNineHolonomicGravityCurvatureVarianceNormalization StageNineIIPlusRestriction
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open PreparationVacuumNativeFullGravityReturn PreparationVacuumNativeSourceRestriction
open PreparationVacuumJointFieldResponse PreparationVacuumLorentzFieldInjection PreparationVacuumNativeFieldInjection
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

def repairedAuxiliaryGraph (s : GravitySourceState) : GravitySourceState:=
  ((s.1.1,physicalIIPlusBivector s.1.1,
    gravityInternalDualEquiv (physicalIIPlusBivector s.1.1)-gravityInternalPairVarianceNormalization s.2),s.2)

theorem repairedAuxiliaryGraph_original (u : JointParameter) (s : GravitySourceState) :
    formNativeGravityMultiplierEulerResidual (repairedGravityPoint u (repairedAuxiliaryGraph s))=0 ∧
      formNativeGravityAuxiliaryEulerResidual (repairedGravityPoint u (repairedAuxiliaryGraph s))=0 :=by
  constructor <;> funext i p <;>
    simp [repairedAuxiliaryGraph,repairedGravityPoint,gravityPoint,formNativeGravityMultiplierEulerResidual,
      generatedGravitySimplicityResidual,formNativeGravityAuxiliaryEulerResidual]

theorem repairedAuxiliaryGraph_unique (u : JointParameter) (s : GravitySourceState)
    (B L : PhysicalBivector)
    (multiplierEuler : formNativeGravityMultiplierEulerResidual (repairedGravityPoint u ((s.1.1,B,L),s.2))=0)
    (auxiliaryEuler : formNativeGravityAuxiliaryEulerResidual (repairedGravityPoint u ((s.1.1,B,L),s.2))=0) :
    ((s.1.1,B,L),s.2)=repairedAuxiliaryGraph s :=by
  have Bgenerated : B=physicalIIPlusBivector s.1.1:=by
    have source:=formNativeGravityMultiplierEulerResidual_eq_zero_iff_simplicity
      (repairedGravityPoint u ((s.1.1,B,L),s.2))
    exact source.mp multiplierEuler
  have Lgenerated : L=gravityInternalDualEquiv B-gravityInternalPairVarianceNormalization s.2:=by
    exact (formNativeGravityAuxiliaryEulerResidual_eq_zero_iff_reaction
      (repairedGravityPoint u ((s.1.1,B,L),s.2))).mp auxiliaryEuler
  simp only [Bgenerated] at Lgenerated
  simp only [repairedAuxiliaryGraph,Bgenerated,Lgenerated]

theorem repairedAuxiliaryGraph_smooth : ContDiff ℝ ∞ repairedAuxiliaryGraph :=by
  have B : ContDiff ℝ ∞ (fun s : GravitySourceState=>physicalIIPlusBivector s.1.1):=
    physicalIIPlusBivector_contDiff.comp (by fun_prop)
  have JB:=gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp B
  have NR : ContDiff ℝ ∞ (fun s : GravitySourceState=>gravityInternalPairVarianceNormalization s.2):=
    gravityInternalPairVarianceNormalization.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp (by fun_prop)
  exact ((by fun_prop : ContDiff ℝ ∞ (fun s : GravitySourceState=>s.1.1)).prodMk
    (B.prodMk (JB.sub NR))).prodMk (by fun_prop)

def repairedGraphFirst (s d : GravitySourceState) : GravitySourceState:=
  ((d.1.1,gravityInternalDualEquiv (wedgeFirst s.1.1 d.1.1),
      gravityInternalDualEquiv (gravityInternalDualEquiv (wedgeFirst s.1.1 d.1.1))-
        gravityInternalPairVarianceNormalization d.2),d.2)

theorem repairedGraphFirst_generated (s d : GravitySourceState) :
    HasDerivAt (fun r : ℝ=>repairedAuxiliaryGraph (s+r • d)) (repairedGraphFirst s d) 0 :=by
  have e : HasDerivAt (fun r : ℝ=>s.1.1+r • d.1.1) d.1.1 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d.1.1).const_add s.1.1 using 1
    simp
  have R : HasDerivAt (fun r : ℝ=>s.2+r • d.2) d.2 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d.2).const_add s.2 using 1
    simp
  have W : HasDerivAt (fun r : ℝ=>coframeWedge (s.1.1+r • d.1.1)) (wedgeFirst s.1.1 d.1.1) 0:=
    hasDerivAt_pi.mpr (fun i=>hasDerivAt_pi.mpr (fun p=>wedgeFirst_generated _ _ i p))
  have B:=gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 W
  have JB:=gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 B
  have NR:=gravityInternalPairVarianceNormalization.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 R
  exact (e.prodMk (B.prodMk (JB.sub NR))).prodMk R

theorem repairedGraphFirst_fderiv (s d : GravitySourceState) :
    fderiv ℝ repairedAuxiliaryGraph s d=repairedGraphFirst s d :=by
  have original:=repairedAuxiliaryGraph_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=s)
  have curve : HasDerivAt (fun r : ℝ=>s+r • d) d 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
    simp
  exact (original.comp_hasDerivAt_of_eq 0 curve (by simp)).unique (repairedGraphFirst_generated s d)

private theorem wedge_sub_right (B R S : PhysicalBivector) :
    gravityTopologicalWedgeCoefficient B (R-S)=gravityTopologicalWedgeCoefficient B R-gravityTopologicalWedgeCoefficient B S :=by
  rw [sub_eq_add_neg,gravityTopologicalWedgeCoefficient_add_right,
    show -S=(-1:ℝ) • S by simp,gravityTopologicalWedgeCoefficient_smul_right]
  ring

def retainedGravityFirst (s d : GravitySourceState) : ℝ:=
  gravityTopologicalBFCoefficient s.1.2.1 d.2-
    gravityTopologicalWedgeCoefficient s.1.2.2 (gravityInternalDualEquiv (wedgeFirst s.1.1 d.1.1))

theorem repairedGravityFirst_eulerSplit (u : JointParameter) (s d : GravitySourceState) :
    repairedGravityFirst s d=retainedGravityFirst s d+
      formNativeGravityAuxiliaryFirstVariationDensity (repairedGravityPoint u s) d.1.2.1+
        formNativeGravityMultiplierFirstVariationDensity (repairedGravityPoint u s) d.1.2.2 :=by
  unfold repairedGravityFirst retainedGravityFirst formNativeGravityAuxiliaryFirstVariationDensity
    formNativeGravityAuxiliaryBFFirstVariationDensity formNativeGravityAuxiliaryConstraintFirstVariationDensity
    formNativeGravityMultiplierFirstVariationDensity formNativeGravityMultiplierEulerResidual
    repairedGravityPoint gravityPoint residualFirst
  change gravityTopologicalBFCoefficient d.1.2.1 s.2+gravityTopologicalBFCoefficient s.1.2.1 d.2-
    (1/2:ℝ)*(gravityTopologicalWedgeCoefficient d.1.2.1 (gravityInternalDualEquiv s.1.2.1)+
      gravityTopologicalWedgeCoefficient s.1.2.1 (gravityInternalDualEquiv d.1.2.1))+
    gravityTopologicalWedgeCoefficient d.1.2.2 (simplicityResidual s.1)+
    gravityTopologicalWedgeCoefficient s.1.2.2 (d.1.2.1-gravityInternalDualEquiv (wedgeFirst s.1.1 d.1.1))=_
  rw [wedge_sub_right]
  simp only [simplicityResidual,generatedGravitySimplicityResidual]
  ring

theorem repairedGravityFirst_graphEnvelope (u : JointParameter) (s d : GravitySourceState) :
    repairedGravityFirst (repairedAuxiliaryGraph s) d=retainedGravityFirst (repairedAuxiliaryGraph s) d :=by
  rw [repairedGravityFirst_eulerSplit u,formNativeGravityAuxiliaryFirstVariationDensity_eq_eulerPairing]
  have equations:=repairedAuxiliaryGraph_original u s
  rw [equations.2]
  simp only [gravityTopologicalWedgeCoefficient,orientedTwoFormWedgeCoefficient,generatedTwoFormWedgeCoefficient,
    Pi.zero_apply,mul_zero,Finset.sum_const_zero]
  rw [formNativeGravityMultiplierFirstVariationDensity,equations.1]
  simp

def reducedGravityDensity (s : GravitySourceState) : ℝ:=repairedGravityDensity (repairedAuxiliaryGraph s)

theorem reducedGravityDensity_original (s : GravitySourceState) :
    reducedGravityDensity s=gravityTopologicalBFCoefficient (physicalIIPlusBivector s.1.1) s.2-
      (1/2:ℝ)*gravityTopologicalWedgeCoefficient (physicalIIPlusBivector s.1.1)
        (gravityInternalDualEquiv (physicalIIPlusBivector s.1.1)) :=by
  simp [reducedGravityDensity,repairedGravityDensity,repairedAuxiliaryGraph,simplicityResidual,
    gravityTopologicalWedgeCoefficient,orientedTwoFormWedgeCoefficient,generatedTwoFormWedgeCoefficient]

theorem repairedUnifiedAction_graphValue (u : JointParameter) (s : GravitySourceState) :
    sourceGeneratedDiracDualFormNativeUnifiedLocalDensity positiveSmoothUnifiedSource 0 0
      (repairedGravityPoint u (repairedAuxiliaryGraph s))=
      reducedGravityDensity s+
        generatedFormNativeGaugeDensityAtBoundary (sourceGeneratedUnifiedCouplings positiveSmoothUnifiedSource)
          (repairedGravityPoint u s)+
        generatedDiracDualFormNativeMatterDensity positiveSmoothUnifiedSource 0 0 (repairedGravityPoint u s) :=rfl

def reducedGravityFirst (s d : GravitySourceState) : ℝ:=
  retainedGravityFirst (repairedAuxiliaryGraph s) d

theorem reducedGravityFirst_generated (u : JointParameter) (s d : GravitySourceState) :
    HasDerivAt (fun r : ℝ=>reducedGravityDensity (s+r • d)) (reducedGravityFirst s d) 0 :=by
  have outer:=repairedGravityDensity_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=repairedAuxiliaryGraph s)
  have generated:=outer.comp_hasDerivAt_of_eq 0 (repairedGraphFirst_generated s d) (by simp)
  rw [repairedGravityFirst_fderiv,repairedGravityFirst_graphEnvelope u] at generated
  exact generated

theorem sourceInternalQuadratic_volume (e : LorentzianCoframe) :
    (1/2:ℝ)*gravityTopologicalWedgeCoefficient (physicalIIPlusBivector e)
      (gravityInternalDualEquiv (physicalIIPlusBivector e))=3*e.det :=by
  rw [Matrix.det_succ_row_zero]
  simp [gravityTopologicalWedgeCoefficient,orientedTwoFormWedgeCoefficient,generatedTwoFormWedgeCoefficient,
    physicalIIPlusBivector,gravityInternalDualEquiv,gravityInternalDualLinear,internalBivectorDual,
    lorentzianCoframeHodge,coframeWedge,
    lorentzianTwoFormSign,minkowskiInternalSign,pairFirst,pairSecond,twoFormComplement,
    Fin.sum_univ_six,Fin.sum_univ_four,Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove]
  ring

theorem reducedGravityDensity_volume (s : GravitySourceState) :
    reducedGravityDensity s=gravityTopologicalBFCoefficient (physicalIIPlusBivector s.1.1) s.2-3*s.1.1.det :=by
  rw [reducedGravityDensity_original,sourceInternalQuadratic_volume]

theorem sourceGravity_volumePotential (z : SourceQuantumGaugeSliceCoordinates.SourceCoordinateSlice) :
    3*(GaussNativeEnergy.coframe GaussNativeEnergy.sourceTime z.1).det=
      GaussCoframeForm.volumePotential z :=by
  rw [GaussNativeEnergy.coframe_determinant]
  unfold GaussCoframeForm.volumePotential GaussNativeEnergy.volume
  ring

end LowEnergy.PreparationVacuumRepairedGravityActionReturn
