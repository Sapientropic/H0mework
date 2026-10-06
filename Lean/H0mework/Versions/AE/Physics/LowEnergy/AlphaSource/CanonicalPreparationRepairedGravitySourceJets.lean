import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceGravityActualCurveReturn
import H0mework.Physics.DualVariation.MotherAction

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumRepairedGravityActionReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction StageNineBlockwiseConstitutive
open StageNineFormNativeMotherAction StageNineDiracDualFormNativeMotherAction
open StageNineTopologicalFourFormPairing StageNineTopologicalGravityCurvatureVariancePairing
open StageNineHolonomicGravityCurvatureVarianceNormalization StageNineIIPlusRestriction
open PreparationVacuumNativeFullGravityReturn PreparationVacuumNativeSourceRestriction
open PreparationVacuumJointFieldResponse PreparationVacuumLorentzFieldInjection PreparationVacuumNativeFieldInjection
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

abbrev GravitySourceState:=GravityState×PhysicalBivector

def repairedGravityPoint (u : JointParameter) (s : GravitySourceState) : StageNineContinuumPointField:=
  {gravityPoint u s.1 with gravityCurvature:=s.2}

def repairedGravityDensity (s : GravitySourceState) : ℝ:=
  gravityTopologicalBFCoefficient s.1.2.1 s.2-
    (1/2:ℝ)*gravityTopologicalWedgeCoefficient s.1.2.1 (gravityInternalDualEquiv s.1.2.1)+
      gravityTopologicalWedgeCoefficient s.1.2.2 (simplicityResidual s.1)

theorem repairedGravityDensity_original (u : JointParameter) (s : GravitySourceState) :
    repairedGravityDensity s=generatedFormNativeGravityBFDensity (repairedGravityPoint u s)+
      generatedFormNativeGravityConstraintDensity (repairedGravityPoint u s) :=rfl

private theorem wedgePair_derivative {B R : ℝ→PhysicalBivector} {dB dR : PhysicalBivector}
    (hB : HasDerivAt B dB 0) (hR : HasDerivAt R dR 0) :
    HasDerivAt (fun r=>gravityTopologicalWedgeCoefficient (B r) (R r))
      (gravityTopologicalWedgeCoefficient dB (R 0)+gravityTopologicalWedgeCoefficient (B 0) dR) 0 :=by
  unfold gravityTopologicalWedgeCoefficient
  rw [←Finset.sum_add_distrib]
  apply HasDerivAt.fun_sum
  intro i _
  have b (p : Fin 6):=hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i) p
  have q (p : Fin 6):=hasDerivAt_pi.mp (hasDerivAt_pi.mp hR i) p
  have generated:=(((((b 0).mul (q 3)).add ((b 1).mul (q 4))).add ((b 2).mul (q 5))).add
      ((b 3).mul (q 0))).add ((b 4).mul (q 1)) |>.add ((b 5).mul (q 2))
  convert! generated.const_mul (lorentzianTwoFormSign i) using 1
  · funext r
    rw [orientedTwoFormWedgeCoefficient_explicit]
    rfl
  · simp only [orientedTwoFormWedgeCoefficient_explicit]
    ring

private theorem bfPair_derivative {B R : ℝ→PhysicalBivector} {dB dR : PhysicalBivector}
    (hB : HasDerivAt B dB 0) (hR : HasDerivAt R dR 0) :
    HasDerivAt (fun r=>gravityTopologicalBFCoefficient (B r) (R r))
      (gravityTopologicalBFCoefficient dB (R 0)+gravityTopologicalBFCoefficient (B 0) dR) 0 :=by
  exact wedgePair_derivative hB
    (gravityInternalPairVarianceNormalization.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hR)

def repairedGravityFirst (s d : GravitySourceState) : ℝ:=
  gravityTopologicalBFCoefficient d.1.2.1 s.2+gravityTopologicalBFCoefficient s.1.2.1 d.2-
    (1/2:ℝ)*(gravityTopologicalWedgeCoefficient d.1.2.1 (gravityInternalDualEquiv s.1.2.1)+
      gravityTopologicalWedgeCoefficient s.1.2.1 (gravityInternalDualEquiv d.1.2.1))+
    gravityTopologicalWedgeCoefficient d.1.2.2 (simplicityResidual s.1)+
      gravityTopologicalWedgeCoefficient s.1.2.2 (residualFirst s.1 d.1)

private theorem line_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s d : E) :
    HasDerivAt (fun r : ℝ=>s+r • d) d 0 :=by
  convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
  simp

theorem repairedGravityFirst_generated (s d : GravitySourceState) :
    HasDerivAt (fun r : ℝ=>repairedGravityDensity (s+r • d)) (repairedGravityFirst s d) 0 :=by
  have B:=line_first s.1.2.1 d.1.2.1
  have R:=line_first s.2 d.2
  have L:=line_first s.1.2.2 d.1.2.2
  have JB:=gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 B
  have bf:=bfPair_derivative B R
  have quadratic:=(wedgePair_derivative B JB).const_mul (1/2:ℝ)
  have constraint:=wedgePair_derivative L (residualFirst_generated s.1 d.1)
  convert! (bf.sub quadratic).add constraint using 1
  simp only [zero_smul,add_zero,repairedGravityFirst,Function.comp_apply]
  change gravityTopologicalBFCoefficient d.1.2.1 s.2+gravityTopologicalBFCoefficient s.1.2.1 d.2-
    (1/2:ℝ)*(gravityTopologicalWedgeCoefficient d.1.2.1 (gravityInternalDualEquiv s.1.2.1)+
      gravityTopologicalWedgeCoefficient s.1.2.1 (gravityInternalDualEquiv d.1.2.1))+
    gravityTopologicalWedgeCoefficient d.1.2.2 (simplicityResidual s.1)+
      gravityTopologicalWedgeCoefficient s.1.2.2 (residualFirst s.1 d.1)=
      gravityTopologicalBFCoefficient d.1.2.1 s.2+gravityTopologicalBFCoefficient s.1.2.1 d.2-
        (1/2:ℝ)*(gravityTopologicalWedgeCoefficient d.1.2.1 (gravityInternalDualEquiv s.1.2.1)+
          gravityTopologicalWedgeCoefficient s.1.2.1 (gravityInternalDualEquiv d.1.2.1))+
        (gravityTopologicalWedgeCoefficient d.1.2.2 (simplicityResidual s.1)+
          gravityTopologicalWedgeCoefficient s.1.2.2 (residualFirst s.1 d.1))
  ring

private theorem wedgePair_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B R : E→PhysicalBivector) (hB : ContDiff ℝ ∞ B) (hR : ContDiff ℝ ∞ R) :
    ContDiff ℝ ∞ (fun s=>gravityTopologicalWedgeCoefficient (B s) (R s)) :=by
  unfold gravityTopologicalWedgeCoefficient orientedTwoFormWedgeCoefficient generatedTwoFormWedgeCoefficient
  apply ContDiff.sum
  intro i _
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro p _
  exact (contDiff_pi.mp (contDiff_pi.mp hB i) p).mul
    (contDiff_pi.mp (contDiff_pi.mp hR i) (twoFormComplement p))

theorem repairedGravityDensity_smooth : ContDiff ℝ ∞ repairedGravityDensity :=by
  have B : ContDiff ℝ ∞ (fun s : GravitySourceState=>s.1.2.1):=by fun_prop
  have R : ContDiff ℝ ∞ (fun s : GravitySourceState=>gravityInternalPairVarianceNormalization s.2):=
    gravityInternalPairVarianceNormalization.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp (by fun_prop)
  have JB : ContDiff ℝ ∞ (fun s : GravitySourceState=>gravityInternalDualEquiv s.1.2.1):=
    gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp B
  have residual : ContDiff ℝ ∞ (fun s : GravitySourceState=>simplicityResidual s.1):=
    (by fun_prop : ContDiff ℝ ∞ (fun s : GravitySourceState=>s.1.2.1)).sub
      (physicalIIPlusBivector_contDiff.comp (by fun_prop))
  exact ((wedgePair_smooth _ _ B R).sub (contDiff_const.mul (wedgePair_smooth _ _ B JB))).add
    (wedgePair_smooth _ _ (by fun_prop) residual)

theorem repairedGravityFirst_fderiv (s d : GravitySourceState) :
    fderiv ℝ repairedGravityDensity s d=repairedGravityFirst s d :=by
  have derivative:=repairedGravityDensity_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=s)
  have generated:=derivative.comp_hasDerivAt_of_eq 0 (line_first s d) (by simp)
  exact generated.unique (repairedGravityFirst_generated s d)

def actualRepairedGravityCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (r : ℝ) : GravitySourceState:=
  (((nativeGravityCurve a theta u r).coframe 0,(nativeGravityCurve a theta u r).gravityAuxiliary 0,
      (nativeGravityCurve a theta u r).gravitySimplicityMultiplier 0),
    holonomicGravityCurvature (nativeGravityCurve a theta u r) 0)

def nativeRepairedGravityDirection (a : Fin 6) (theta : ℝ) (u : JointParameter) : GravitySourceState:=
  (nativeGravityDirection a theta (originalGravityState u),(nativeBFDirection a theta u).2.2)

theorem actualRepairedGravityCurve_first (a : Fin 6) (theta : ℝ) (u : JointParameter) :
    HasDerivAt (actualRepairedGravityCurve a theta u) (nativeRepairedGravityDirection a theta u) 0 :=by
  have eB:=(ContinuousLinearMap.fst ℝ LorentzianCoframe (PhysicalBivector×PhysicalBivector)).hasFDerivAt.comp_hasDerivAt 0
    (actualBFStateCurve_first a theta u)
  have br:=(ContinuousLinearMap.snd ℝ LorentzianCoframe (PhysicalBivector×PhysicalBivector)).hasFDerivAt.comp_hasDerivAt 0
    (actualBFStateCurve_first a theta u)
  have b:=(ContinuousLinearMap.fst ℝ PhysicalBivector PhysicalBivector).hasFDerivAt.comp_hasDerivAt 0 br
  have r:=(ContinuousLinearMap.snd ℝ PhysicalBivector PhysicalBivector).hasFDerivAt.comp_hasDerivAt 0 br
  have l:=line_first ((primitiveFamily u).gravitySimplicityMultiplier 0)
    ((nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).gravitySimplicityMultiplier 0)
  convert! (eB.prodMk (b.prodMk l)).prodMk r using 1
  rw [nativeRepairedGravityDirection,nativeGravityDirection_original]
  rfl

def originalRepairedGravityState (u : JointParameter) : GravitySourceState:=
  (originalGravityState u,holonomicGravityCurvature (primitiveFamily u) 0)

def nativeRepairedGravityTorque (a : Fin 6) (theta : ℝ) (u : JointParameter) : ℝ:=
  repairedGravityFirst (originalRepairedGravityState u) (nativeRepairedGravityDirection a theta u)

theorem nativeRepairedGravityTorque_actualCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) :
    HasDerivAt (fun r : ℝ=>generatedFormNativeGravityBFDensity
      (toContinuumPointField (nativeGravityCurve a theta u r) 0)+
      generatedFormNativeGravityConstraintDensity (toContinuumPointField (nativeGravityCurve a theta u r) 0))
      (nativeRepairedGravityTorque a theta u) 0 :=by
  have generated:=repairedGravityDensity_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=originalRepairedGravityState u)
  have zero : holonomicGravityCurvature (nativeGravityCurve a theta u 0) 0=
      holonomicGravityCurvature (primitiveFamily u) 0 :=by
    simpa using nativeGravityCurve_curvature a theta u 0
  have derivative:=generated.comp_hasDerivAt_of_eq 0 (actualRepairedGravityCurve_first a theta u) (by
    simp only [actualRepairedGravityCurve,zero]
    simp [nativeGravityCurve,configurationRay,originalRepairedGravityState,originalGravityState])
  rw [repairedGravityFirst_fderiv] at derivative
  convert! derivative using 1

end LowEnergy.PreparationVacuumRepairedGravityActionReturn
