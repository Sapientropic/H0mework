import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationRepairedGravityAuxiliaryGraph

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
open StageNineFormNativeGravityMultiplierAuxiliaryVariation
open PreparationVacuumNativeFullGravityReturn PreparationVacuumNativeSourceRestriction
open PreparationVacuumJointFieldResponse PreparationVacuumLorentzFieldInjection PreparationVacuumNativeFieldInjection
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily StageNineCompactSupportIntegrationByParts
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

private theorem topologicalPair_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

private theorem wedgeFirst_smooth : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>wedgeFirst v.1.1.1 v.2.1.1) :=by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro p
  unfold wedgeFirst
  fun_prop

theorem repairedGravityFirst_smooth :
    ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>repairedGravityFirst v.1 v.2) :=by
  let J:=gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  let N:=gravityInternalPairVarianceNormalization.toContinuousLinearEquiv.toContinuousLinearMap
  have B : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>v.1.1.2.1):=by fun_prop
  have dB : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>v.2.1.2.1):=by fun_prop
  have JB:=J.contDiff.comp B
  have JdB:=J.contDiff.comp dB
  have R : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>N v.1.2):=N.contDiff.comp (by fun_prop)
  have dR : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>N v.2.2):=N.contDiff.comp (by fun_prop)
  have residual : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>simplicityResidual v.1.1):=
    B.sub (physicalIIPlusBivector_contDiff.comp (by fun_prop))
  have residualJet : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>residualFirst v.1.1 v.2.1):=
    dB.sub (J.contDiff.comp wedgeFirst_smooth)
  exact (((topologicalPair_smooth _ _ dB R).add (topologicalPair_smooth _ _ B dR)).sub
    (contDiff_const.mul ((topologicalPair_smooth _ _ dB JB).add (topologicalPair_smooth _ _ B JdB)))).add
      (topologicalPair_smooth _ _ (by fun_prop) residual) |>.add
        (topologicalPair_smooth _ _ (by fun_prop) residualJet)

def repairedGravityMixed (s d h c : GravitySourceState) : ℝ:=
  fderiv ℝ (fun v : GravitySourceState×GravitySourceState=>repairedGravityFirst v.1 v.2) (s,d) (h,c)

private theorem sourceLine_first {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (s d : E) :
    HasDerivAt (fun r : ℝ=>s+r • d) d 0 :=by
  convert! ((hasDerivAt_id (0:ℝ)).smul_const d).const_add s using 1
  simp

private theorem sourceTopologicalPair_derivative {B R : ℝ→PhysicalBivector} {dB dR : PhysicalBivector}
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

private theorem sourceBFPair_derivative {B R : ℝ→PhysicalBivector} {dB dR : PhysicalBivector}
    (hB : HasDerivAt B dB 0) (hR : HasDerivAt R dR 0) :
    HasDerivAt (fun r=>gravityTopologicalBFCoefficient (B r) (R r))
      (gravityTopologicalBFCoefficient dB (R 0)+gravityTopologicalBFCoefficient (B 0) dR) 0 :=
  sourceTopologicalPair_derivative hB
    (gravityInternalPairVarianceNormalization.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 hR)

private theorem sourceWedgeFirst_moving (e d h c : LorentzianCoframe) (i p : Fin 6) :
    HasDerivAt (fun r : ℝ=>wedgeFirst (e+r • h) (d+r • c) i p)
      (wedgeFirst h d i p+wedgeFirst e c i p) 0 :=by
  have entry (s k : LorentzianCoframe) (a mu : Fin 4) : HasDerivAt (fun r : ℝ=>(s+r • k) a mu) (k a mu) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const (k a mu)).const_add (s a mu) using 1
    simp
  have generated:=(((entry d c (pairFirst i) (pairFirst p)).mul (entry e h (pairSecond i) (pairSecond p))).add
    ((entry e h (pairFirst i) (pairFirst p)).mul (entry d c (pairSecond i) (pairSecond p)))).sub
      (((entry d c (pairFirst i) (pairSecond p)).mul (entry e h (pairSecond i) (pairFirst p))).add
        ((entry e h (pairFirst i) (pairSecond p)).mul (entry d c (pairSecond i) (pairFirst p))))
  convert! generated using 1
  · funext r
    simp only [wedgeFirst,Pi.add_apply,Pi.mul_apply,Pi.sub_apply]
    ring
  · simp only [wedgeFirst,zero_smul,add_zero]
    ring

private theorem sourceResidualFirst_moving (s d h c : GravityState) :
    HasDerivAt (fun r : ℝ=>residualFirst (s+r • h) (d+r • c))
      (residualMixed d h+residualFirst s c) 0 :=by
  have wedge : HasDerivAt (fun r : ℝ=>wedgeFirst (s.1+r • h.1) (d.1+r • c.1))
      (wedgeFirst h.1 d.1+wedgeFirst s.1 c.1) 0:=
    hasDerivAt_pi.mpr (fun i=>hasDerivAt_pi.mpr (fun p=>sourceWedgeFirst_moving _ _ _ _ i p))
  have dual:=gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 wedge
  have generated:=(sourceLine_first d.2.1 c.2.1).sub dual
  convert! generated using 1
  change -gravityInternalDualEquiv (wedgeFirst h.1 d.1)+(c.2.1-gravityInternalDualEquiv (wedgeFirst s.1 c.1))=
    c.2.1-gravityInternalDualEquiv (wedgeFirst h.1 d.1+wedgeFirst s.1 c.1)
  rw [map_add]
  abel

def repairedGravityMixedTerms (s d h c : GravitySourceState) : ℝ:=
  gravityTopologicalBFCoefficient c.1.2.1 s.2+gravityTopologicalBFCoefficient d.1.2.1 h.2+
    gravityTopologicalBFCoefficient h.1.2.1 d.2+gravityTopologicalBFCoefficient s.1.2.1 c.2-
    (1/2:ℝ)*(gravityTopologicalWedgeCoefficient c.1.2.1 (gravityInternalDualEquiv s.1.2.1)+
      gravityTopologicalWedgeCoefficient d.1.2.1 (gravityInternalDualEquiv h.1.2.1)+
      gravityTopologicalWedgeCoefficient h.1.2.1 (gravityInternalDualEquiv d.1.2.1)+
      gravityTopologicalWedgeCoefficient s.1.2.1 (gravityInternalDualEquiv c.1.2.1))+
    gravityTopologicalWedgeCoefficient c.1.2.2 (simplicityResidual s.1)+
      gravityTopologicalWedgeCoefficient d.1.2.2 (residualFirst s.1 h.1)+
      gravityTopologicalWedgeCoefficient h.1.2.2 (residualFirst s.1 d.1)+
      gravityTopologicalWedgeCoefficient s.1.2.2 (residualMixed d.1 h.1+residualFirst s.1 c.1)

theorem repairedGravityMixed_explicit (s d h c : GravitySourceState) :
    repairedGravityMixed s d h c=repairedGravityMixedTerms s d h c :=by
  have B:=sourceLine_first s.1.2.1 h.1.2.1
  have dB:=sourceLine_first d.1.2.1 c.1.2.1
  have R:=sourceLine_first s.2 h.2
  have dR:=sourceLine_first d.2 c.2
  have L:=sourceLine_first s.1.2.2 h.1.2.2
  have dL:=sourceLine_first d.1.2.2 c.1.2.2
  have JB : HasDerivAt (fun r : ℝ=>gravityInternalDualEquiv (s.1.2.1+r • h.1.2.1))
      (gravityInternalDualEquiv h.1.2.1) 0:=
    gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 B
  have JdB : HasDerivAt (fun r : ℝ=>gravityInternalDualEquiv (d.1.2.1+r • c.1.2.1))
      (gravityInternalDualEquiv c.1.2.1) 0:=
    gravityInternalDualEquiv.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 dB
  have firstBF:=sourceBFPair_derivative dB R
  have secondBF:=sourceBFPair_derivative B dR
  have firstBB:=sourceTopologicalPair_derivative dB JB
  have secondBB:=sourceTopologicalPair_derivative B JdB
  have firstConstraint:=sourceTopologicalPair_derivative dL (residualFirst_generated s.1 h.1)
  have secondConstraint:=sourceTopologicalPair_derivative L (sourceResidualFirst_moving s.1 d.1 h.1 c.1)
  have explicit : HasDerivAt (fun r : ℝ=>repairedGravityFirst (s+r • h) (d+r • c))
      (repairedGravityMixedTerms s d h c) 0:=by
    convert! (((firstBF.add secondBF).sub ((firstBB.add secondBB).const_mul (1/2:ℝ))).add firstConstraint).add secondConstraint using 1
    simp only [zero_smul,add_zero,Function.comp_apply,repairedGravityMixedTerms]
    ring
  have source:=repairedGravityFirst_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=(s,d))
  exact (source.comp_hasDerivAt_of_eq 0 ((sourceLine_first s h).prodMk (sourceLine_first d c)) (by simp)).unique explicit

def sourceRepairedGravityForce (u : JointParameter) (force : Field289) : GravitySourceState:=
  (originalGravityForce force,(originalBFForce u force).2.2)

def sourceRepairedGravityContact (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) : GravitySourceState:=
  (nativeGravityDirection a theta (originalGravityForce force),(originalBFContact a theta u force).2.2)

def actualRepairedJointCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) (r : ℝ) :
    GravitySourceState×GravitySourceState:=
  ((actualSimplicityStateCurve u force r,(fieldNativeBFCurve a theta u force r).1.2.2),
    (actualNativeSimplicityDirection a theta u force r,(fieldNativeBFCurve a theta u force r).2.2.2))

private def assembleGravityJets : ((BFState×BFState)×(PhysicalBivector×PhysicalBivector))→ₗ[ℝ]
    (GravitySourceState×GravitySourceState) where
  toFun v:=((((v.1.1.1,v.1.1.2.1,v.2.1),v.1.1.2.2),((v.1.2.1,v.1.2.2.1,v.2.2),v.1.2.2.2)))
  map_add' _v _w:=rfl
  map_smul' _r _v:=rfl

theorem actualRepairedJointCurve_first (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (actualRepairedJointCurve a theta u force)
      (sourceRepairedGravityForce u force,sourceRepairedGravityContact a theta u force) 0 :=by
  have lambda:=sourceLine_first (originalGravityState u).2.2 (originalGravityForce force).2.2
  have nativeLambda:=sourceLine_first (nativeGravityDirection a theta (originalGravityState u)).2.2
    (nativeGravityDirection a theta (originalGravityForce force)).2.2
  have movingLambda : HasDerivAt (fun r : ℝ=>(actualNativeSimplicityDirection a theta u force r).2.2)
      (nativeGravityDirection a theta (originalGravityForce force)).2.2 0:=by
    have same : (fun r : ℝ=>(actualNativeSimplicityDirection a theta u force r).2.2)=
        fun r=>(nativeGravityDirection a theta (originalGravityState u)).2.2+
          r • (nativeGravityDirection a theta (originalGravityForce force)).2.2:=by
      funext r
      rw [actualNativeSimplicityDirection_source,actualSimplicityStateCurve_source,nativeGravityDirection_affine]
      rfl
    rw [same]
    exact nativeLambda
  have originalLambda : HasDerivAt (fun r : ℝ=>(actualSimplicityStateCurve u force r).2.2)
      (originalGravityForce force).2.2 0:=by
    simpa only [actualSimplicityStateCurve_source,Prod.snd_add,Prod.smul_snd] using lambda
  have original:=(fieldNativeBFCurve_first a theta u force).prodMk (originalLambda.prodMk movingLambda)
  have generated:=assembleGravityJets.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 original
  exact generated

theorem actualRepairedJointCurve_initial (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    actualRepairedJointCurve a theta u force 0=(originalRepairedGravityState u,nativeRepairedGravityDirection a theta u) :=by
  simp only [actualRepairedJointCurve,actualSimplicityStateCurve_source,actualNativeSimplicityDirection_source,
    zero_smul,add_zero,fieldNativeBFCurve,fieldGravityCurve,configurationRay,zero_smul,add_zero,fieldNativeGravityDirection,
    lorentzPrimitiveDirection,originalRepairedGravityState,originalGravityState,nativeRepairedGravityDirection,
    nativeBFDirection,nativePrimitiveFamily,Fin.addCases_right,nativeGravityDirection_original]
  rw [show (fun _=>connectionBivectorDirection a theta 0 (ambientPrimitiveData u).2.2.2)=
    nativeLorentzFamilyDirection a (fun _=>theta) u from by
      funext x mu
      simp [nativeLorentzFamilyDirection,connectionBivectorDirection,fieldDirectionalDerivative]]
  rfl

def sourceRepairedGravityMixed (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) : ℝ:=
  repairedGravityMixed (originalRepairedGravityState u) (nativeRepairedGravityDirection a theta u)
    (sourceRepairedGravityForce u force) (sourceRepairedGravityContact a theta u force)

theorem sourceRepairedGravityMixed_actualCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>repairedGravityFirst (actualRepairedJointCurve a theta u force r).1
      (actualRepairedJointCurve a theta u force r).2) (sourceRepairedGravityMixed a theta u force) 0 :=by
  have original:=repairedGravityFirst_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=(originalRepairedGravityState u,nativeRepairedGravityDirection a theta u))
  exact original.comp_hasDerivAt_of_eq 0 (actualRepairedJointCurve_first a theta u force)
    (actualRepairedJointCurve_initial a theta u force).symm

def reducedGravityMixed (s d h c : GravitySourceState) : ℝ:=
  fderiv ℝ (fun v : GravitySourceState×GravitySourceState=>reducedGravityFirst v.1 v.2) (s,d) (h,c)

theorem reducedGravityFirst_smooth :
    ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>reducedGravityFirst v.1 v.2) :=by
  have graph : ContDiff ℝ ∞ (fun v : GravitySourceState×GravitySourceState=>(repairedAuxiliaryGraph v.1,v.2)):=
    (repairedAuxiliaryGraph_smooth.comp (by fun_prop)).prodMk (by fun_prop)
  have original:=repairedGravityFirst_smooth.comp graph
  have same : (fun v : GravitySourceState×GravitySourceState=>reducedGravityFirst v.1 v.2)=
      fun v=>repairedGravityFirst (repairedAuxiliaryGraph v.1) v.2:=by
    funext v
    rw [repairedGravityFirst_graphEnvelope (0,0)]
    rfl
  rw [same]
  exact original

theorem reducedGravityMixed_actualCurve (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>reducedGravityFirst (actualRepairedJointCurve a theta u force r).1
      (actualRepairedJointCurve a theta u force r).2)
      (reducedGravityMixed (originalRepairedGravityState u) (nativeRepairedGravityDirection a theta u)
        (sourceRepairedGravityForce u force) (sourceRepairedGravityContact a theta u force)) 0 :=by
  have original:=reducedGravityFirst_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=(originalRepairedGravityState u,nativeRepairedGravityDirection a theta u))
  exact original.comp_hasDerivAt_of_eq 0 (actualRepairedJointCurve_first a theta u force)
    (actualRepairedJointCurve_initial a theta u force).symm

theorem reducedGravityMixed_graphTransport (u : JointParameter) (s d h c : GravitySourceState) :
    reducedGravityMixed s d h c=
      repairedGravityMixed (repairedAuxiliaryGraph s) d (repairedGraphFirst s h) c :=by
  have original:=repairedGravityFirst_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=(repairedAuxiliaryGraph s,d))
  have transported:=original.comp_hasDerivAt_of_eq 0
    ((repairedGraphFirst_generated s h).prodMk (sourceLine_first d c)) (by simp)
  have originalReduced:=reducedGravityFirst_smooth.differentiable (by simp)
    |>.differentiableAt.hasFDerivAt (x:=(s,d))
  have reduced:=originalReduced.comp_hasDerivAt_of_eq 0
    ((sourceLine_first s h).prodMk (sourceLine_first d c)) (by simp)
  have same : (fun r : ℝ=>reducedGravityFirst (s+r • h) (d+r • c))=
      fun r=>repairedGravityFirst (repairedAuxiliaryGraph (s+r • h)) (d+r • c):=by
    funext r
    rw [repairedGravityFirst_graphEnvelope u]
    rfl
  have actualReduced : HasDerivAt (fun r : ℝ=>reducedGravityFirst (s+r • h) (d+r • c))
      (reducedGravityMixed s d h c) 0:=reduced
  have actualTransported : HasDerivAt (fun r : ℝ=>repairedGravityFirst
      (repairedAuxiliaryGraph (s+r • h)) (d+r • c))
      (repairedGravityMixed (repairedAuxiliaryGraph s) d (repairedGraphFirst s h) c) 0:=transported
  rw [same] at actualReduced
  exact actualReduced.unique actualTransported

theorem reducedGravityMixed_sourceTerms (u : JointParameter) (s d h c : GravitySourceState) :
    reducedGravityMixed s d h c=
      repairedGravityMixedTerms (repairedAuxiliaryGraph s) d (repairedGraphFirst s h) c :=by
  rw [reducedGravityMixed_graphTransport u,repairedGravityMixed_explicit]

end LowEnergy.PreparationVacuumRepairedGravityActionReturn
