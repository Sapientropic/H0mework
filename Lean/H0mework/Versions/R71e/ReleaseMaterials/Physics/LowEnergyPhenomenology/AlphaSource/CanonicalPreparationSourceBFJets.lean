import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationSourceSimplicityJets
import H0mework.Physics.Coframe.CoframeTwoFormPairing

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeFullGravityReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction
open StageNineCoframeTwoFormPairing StageNineCoframeVariation EmpiricalReferenceScaleCouplingBoundary
open PreparationVacuumNativeSourceRestriction PreparationVacuumNativeLocalWard
open PreparationVacuumNativeFieldInjection PreparationVacuumLorentzFieldInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily
open Filter Set
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

abbrev BFState:=LorentzianCoframe×PhysicalBivector×PhysicalBivector

def originalBFState (u : JointParameter) : BFState:=
  ((primitiveFamily u).coframe 0,(primitiveFamily u).gravityAuxiliary 0,holonomicGravityCurvature (primitiveFamily u) 0)

def bfPoint (u : JointParameter) (s : BFState) : StageNineContinuumPointField:=
  {toContinuumPointField (primitiveFamily u) 0 with coframe:=s.1,gravityAuxiliary:=s.2.1,gravityCurvature:=s.2.2}

def framed (e : LorentzianCoframe) (B : PhysicalBivector) : PhysicalBivector:=
  fun i=>coframeTwoFormLinear e (B i)

def framedFirst (e h : LorentzianCoframe) (B dB : PhysicalBivector) : PhysicalBivector:=
  fun i p=>(∑j : Fin 6,wedgeFirst e h p j*B i j)+coframeTwoFormLinear e (dB i) p

private def spaceDualLinear : PhysicalBivector→ₗ[ℝ] PhysicalBivector where
  toFun B:=fun i=>lorentzianCoframeHodge (B i)
  map_add' B C:=by funext i p;exact congrFun (lorentzianCoframeHodge.map_add _ _) p
  map_smul' t B:=by funext i p;exact congrFun (lorentzianCoframeHodge.map_smul t _) p

def signedPairing (B R : PhysicalBivector) : ℝ:=
  ∑i : Fin 6,∑p : Fin 6,lorentzianTwoFormSign i*lorentzianTwoFormSign p*B i p*R i p

def constitutivePair (e : LorentzianCoframe) (B R : PhysicalBivector) : ℝ:=
  signedPairing (framed e B) (spaceDualLinear (framed e R))

/-- The actual metric and actual dynamical Hodge cancel only their common inverse-frame, preserving both signed pairings. -/
theorem constitutivePair_original (e : LorentzianCoframe) (B R : PhysicalBivector) (nondegenerate : e.det≠0) :
    constitutivePair e B R=gravityCoframePairing e B (gravitySpacetimeHodge e R) :=by
  unfold constitutivePair signedPairing gravityCoframePairing coframeTwoFormMetricPairing gravitySpacetimeHodge
  simp only [coframeTwoFormLinear_dynamicHodge e nondegenerate,framed,spaceDualLinear,LinearMap.coe_mk,AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

def bfPolynomial (s : BFState) : ℝ:=
  constitutivePair s.1 s.2.1 s.2.2-(1/2:ℝ)*constitutivePair s.1 s.2.1 (internalBivectorDual s.2.1)

theorem bfPolynomial_original (u : JointParameter) (s : BFState) (nondegenerate : s.1.det≠0) :
    bfPolynomial s=generatedGravityBFDensity (bfPoint u s) :=by
  rw [bfPolynomial,constitutivePair_original _ _ _ nondegenerate,constitutivePair_original _ _ _ nondegenerate]
  rfl

theorem framedFirst_generated (e h : LorentzianCoframe) (B dB : PhysicalBivector) :
    HasDerivAt (fun r : ℝ=>framed (e+r • h) (B+r • dB)) (framedFirst e h B dB) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro p
  have entry (j : Fin 6) : HasDerivAt (fun r : ℝ=>(B+r • dB) i j) (dB i j) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const (dB i j)).const_add (B i j) using 1
    simp
  have each (j : Fin 6) :=(wedgeFirst_generated e h p j).mul (entry j)
  have generated:=HasDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 6)))=>each j)
  convert! generated using 1
  simp only [framedFirst,zero_smul,add_zero,Finset.sum_add_distrib,framed,coframeTwoFormLinear,LinearMap.coe_mk,AddHom.coe_mk]

theorem signedPairing_generated {B R : ℝ→PhysicalBivector} {dB dR : PhysicalBivector}
    (hB : HasDerivAt B dB 0) (hR : HasDerivAt R dR 0) :
    HasDerivAt (fun r : ℝ=>signedPairing (B r) (R r))
      (signedPairing dB (R 0)+signedPairing (B 0) dR) 0 :=by
  have entryB:=fun i p=>hasDerivAt_pi.mp (hasDerivAt_pi.mp hB i) p
  have entryR:=fun i p=>hasDerivAt_pi.mp (hasDerivAt_pi.mp hR i) p
  have generated:=HasDerivAt.fun_sum (fun i (_ : i∈(Finset.univ : Finset (Fin 6)))=>
    HasDerivAt.fun_sum (fun p (_ : p∈(Finset.univ : Finset (Fin 6)))=>
      ((entryB i p).mul (entryR i p)).const_mul (lorentzianTwoFormSign i*lorentzianTwoFormSign p)))
  convert! generated using 1
  · funext r
    simp only [signedPairing,Pi.mul_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro p _
    ring
  · simp only [signedPairing,Finset.sum_add_distrib]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    ring

def constitutiveFirst (e h : LorentzianCoframe) (B R dB dR : PhysicalBivector) : ℝ:=
  signedPairing (framedFirst e h B dB) (spaceDualLinear (framed e R))+
    signedPairing (framed e B) (spaceDualLinear (framedFirst e h R dR))

theorem constitutiveFirst_generated (e h : LorentzianCoframe) (B R dB dR : PhysicalBivector) :
    HasDerivAt (fun r : ℝ=>constitutivePair (e+r • h) (B+r • dB) (R+r • dR))
      (constitutiveFirst e h B R dB dR) 0 :=by
  have first:=framedFirst_generated e h B dB
  have second:=spaceDualLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (framedFirst_generated e h R dR)
  have generated:=signedPairing_generated first second
  convert! generated using 1
  simp only [zero_smul,add_zero,constitutiveFirst,Function.comp_apply]
  rfl

def bfFirst (s d : BFState) : ℝ:=
  constitutiveFirst s.1 d.1 s.2.1 s.2.2 d.2.1 d.2.2-
    (1/2:ℝ)*constitutiveFirst s.1 d.1 s.2.1 (internalBivectorDual s.2.1) d.2.1 (internalBivectorDual d.2.1)

theorem bfFirst_polynomial_generated (s d : BFState) :
    HasDerivAt (fun r : ℝ=>bfPolynomial (s+r • d)) (bfFirst s d) 0 :=by
  have first:=constitutiveFirst_generated s.1 d.1 s.2.1 s.2.2 d.2.1 d.2.2
  have second:=(constitutiveFirst_generated s.1 d.1 s.2.1 (internalBivectorDual s.2.1)
    d.2.1 (internalBivectorDual d.2.1)).const_mul (1/2:ℝ)
  have linear (r : ℝ) : internalBivectorDual (s.2.1+r • d.2.1)=internalBivectorDual s.2.1+r • internalBivectorDual d.2.1 :=by
    funext i p
    exact congrFun (lorentzianCoframeHodge.map_add _ _ |>.trans
      (congrArg (fun v=>lorentzianCoframeHodge (fun j=>s.2.1 j p)+v) (lorentzianCoframeHodge.map_smul r (fun j=>d.2.1 j p)))) i
  convert! first.sub second using 1
  funext r
  simp only [bfPolynomial,linear,Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,Pi.sub_apply]

theorem bfFirst_generated (u : JointParameter) (s d : BFState) (nondegenerate : s.1.det≠0) :
    HasDerivAt (fun r : ℝ=>generatedGravityBFDensity (bfPoint u (s+r • d))) (bfFirst s d) 0 :=by
  have determinant : ContinuousAt (fun r : ℝ=>(s.1+r • d.1).det) 0:=
    coframe_det_contDiff.continuous.continuousAt.comp
      (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have regular : ∀ᶠ r : ℝ in 𝓝 0,(s.1+r • d.1).det≠0:=
    determinant.eventually (isOpen_compl_singleton.mem_nhds (by simpa using nondegenerate))
  have same : (fun r : ℝ=>generatedGravityBFDensity (bfPoint u (s+r • d)))=ᶠ[𝓝 0]
      (fun r : ℝ=>bfPolynomial (s+r • d)) :=by
    filter_upwards [regular] with r hr
    exact (bfPolynomial_original u (s+r • d) hr).symm
  exact (bfFirst_polynomial_generated s d).congr_of_eventuallyEq same

def nativeBFDirection (a : Fin 6) (theta : ℝ) (u : JointParameter) : BFState:=
  ((nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).coframe 0,
    (nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).gravityAuxiliary 0,
      StageNineLorentzConnectionVariation.lorentzConnectionLinearCurvatureVariation (primitiveFamily u)
        (nativeLorentzFamilyDirection a (fun _=>theta) u) 0)

def nativeBFTorque (a : Fin 6) (theta : ℝ) (u : JointParameter) : ℝ:=
  bfFirst (originalBFState u) (nativeBFDirection a theta u)

theorem nativeBFTorque_generated (a : Fin 6) (theta : ℝ) (u : JointParameter)
    (nondegenerate : ((primitiveFamily u).coframe 0).det≠0) :
    HasDerivAt (fun r : ℝ=>generatedGravityBFDensity (bfPoint u
      (originalBFState u+r • nativeBFDirection a theta u))) (nativeBFTorque a theta u) 0 :=
  bfFirst_generated u (originalBFState u) (nativeBFDirection a theta u) nondegenerate

private theorem wedgeFirst_movingBF (e d h c : LorentzianCoframe) (i p : Fin 6) :
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

def framedMixed (e d h c : LorentzianCoframe) (B dB hB cB : PhysicalBivector) : PhysicalBivector:=
  fun i p=>∑j : Fin 6,((wedgeFirst h d p j+wedgeFirst e c p j)*B i j+
    wedgeFirst e d p j*hB i j+wedgeFirst e h p j*dB i j+coframeWedge e p j*cB i j)

theorem framedMixed_generated (e d h c : LorentzianCoframe) (B dB hB cB : PhysicalBivector) :
    HasDerivAt (fun r : ℝ=>framedFirst (e+r • h) (d+r • c) (B+r • hB) (dB+r • cB))
      (framedMixed e d h c B dB hB cB) 0 :=by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro p
  have entry (U V : PhysicalBivector) (j : Fin 6) : HasDerivAt (fun r : ℝ=>(U+r • V) i j) (V i j) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const (V i j)).const_add (U i j) using 1
    simp
  have each (j : Fin 6) :=((wedgeFirst_movingBF e d h c p j).mul (entry B hB j)).add
    ((wedgeFirst_generated e h p j).mul (entry dB cB j))
  have generated:=HasDerivAt.fun_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 6)))=>each j)
  convert! generated using 1
  · funext r
    simp only [framedFirst,coframeTwoFormLinear,LinearMap.coe_mk,AddHom.coe_mk,Pi.add_apply,Pi.mul_apply,Finset.sum_add_distrib]
  · simp only [framedMixed,zero_smul,add_zero]
    apply Finset.sum_congr rfl
    intro j _
    ring

def constitutiveMixed (s d h c : BFState) : ℝ:=
  signedPairing (framedMixed s.1 d.1 h.1 c.1 s.2.1 d.2.1 h.2.1 c.2.1) (spaceDualLinear (framed s.1 s.2.2))+
    signedPairing (framedFirst s.1 d.1 s.2.1 d.2.1) (spaceDualLinear (framedFirst s.1 h.1 s.2.2 h.2.2))+
    signedPairing (framedFirst s.1 h.1 s.2.1 h.2.1) (spaceDualLinear (framedFirst s.1 d.1 s.2.2 d.2.2))+
    signedPairing (framed s.1 s.2.1) (spaceDualLinear (framedMixed s.1 d.1 h.1 c.1 s.2.2 d.2.2 h.2.2 c.2.2))

theorem constitutiveMixed_generated (s d h c : BFState) :
    HasDerivAt (fun r : ℝ=>constitutiveFirst (s+r • h).1 (d+r • c).1
      (s+r • h).2.1 (s+r • h).2.2 (d+r • c).2.1 (d+r • c).2.2)
      (constitutiveMixed s d h c) 0 :=by
  have B:=framedFirst_generated s.1 h.1 s.2.1 h.2.1
  have R:=spaceDualLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 (framedFirst_generated s.1 h.1 s.2.2 h.2.2)
  have dB:=framedMixed_generated s.1 d.1 h.1 c.1 s.2.1 d.2.1 h.2.1 c.2.1
  have dR:=spaceDualLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (framedMixed_generated s.1 d.1 h.1 c.1 s.2.2 d.2.2 h.2.2 c.2.2)
  have generated:=(signedPairing_generated dB R).add (signedPairing_generated B dR)
  convert! generated using 1
  simp only [constitutiveFirst,constitutiveMixed,Function.comp_apply,zero_smul,add_zero]
  abel

private def dualBFState (s : BFState) : BFState:=(s.1,s.2.1,internalBivectorDual s.2.1)

def bfMixed (s d h c : BFState) : ℝ:=
  constitutiveMixed s d h c-(1/2:ℝ)*constitutiveMixed (dualBFState s) (dualBFState d) (dualBFState h) (dualBFState c)

theorem bfMixed_generated (s d h c : BFState) :
    HasDerivAt (fun r : ℝ=>bfFirst (s+r • h) (d+r • c)) (bfMixed s d h c) 0 :=by
  have first:=constitutiveMixed_generated s d h c
  have second:=(constitutiveMixed_generated (dualBFState s) (dualBFState d) (dualBFState h) (dualBFState c)).const_mul (1/2:ℝ)
  have linear (s h : BFState) (r : ℝ) : dualBFState (s+r • h)=dualBFState s+r • dualBFState h:=by
    apply Prod.ext
    · rfl
    apply Prod.ext
    · rfl
    funext i p
    exact congrFun (lorentzianCoframeHodge.map_add _ _ |>.trans
      (congrArg (fun v=>lorentzianCoframeHodge (fun j=>s.2.1 j p)+v) (lorentzianCoframeHodge.map_smul r (fun j=>h.2.1 j p)))) i
  convert! first.sub second using 1
  funext r
  change constitutiveFirst (s+r • h).1 (d+r • c).1 (s+r • h).2.1 (s+r • h).2.2 (d+r • c).2.1 (d+r • c).2.2-
    (1/2:ℝ)*constitutiveFirst (dualBFState (s+r • h)).1 (dualBFState (d+r • c)).1
      (dualBFState (s+r • h)).2.1 (dualBFState (s+r • h)).2.2 (dualBFState (d+r • c)).2.1 (dualBFState (d+r • c)).2.2=_
  rw [linear,linear]
  rfl

end LowEnergy.PreparationVacuumNativeFullGravityReturn
