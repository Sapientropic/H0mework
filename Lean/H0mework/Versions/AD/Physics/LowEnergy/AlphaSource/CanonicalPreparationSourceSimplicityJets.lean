import H0mework.Versions.AD.Physics.LowEnergy.AlphaSource.CanonicalPreparationLorentzCurvatureMixed

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumNativeFullGravityReturn
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction EmpiricalReferenceScaleCouplingBoundary
open PreparationVacuumNativeSourceRestriction PreparationVacuumNativeLocalWard
open PreparationVacuumNativeFieldInjection PreparationVacuumLorentzFieldInjection PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumSourceFieldFamily
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

abbrev GravityState:=LorentzianCoframe×PhysicalBivector×PhysicalBivector

def originalGravityState (u : JointParameter) : GravityState:=
  ((primitiveFamily u).coframe 0,(primitiveFamily u).gravityAuxiliary 0,(primitiveFamily u).gravitySimplicityMultiplier 0)

def originalGravityForce (force : Field289) : GravityState:=
  (fieldCoframe force,fieldGravityB force,fieldMultiplier force)

def gravityPoint (u : JointParameter) (s : GravityState) : StageNineContinuumPointField:=
  {toContinuumPointField (primitiveFamily u) 0 with coframe:=s.1,gravityAuxiliary:=s.2.1,gravitySimplicityMultiplier:=s.2.2}

def simplicityResidual (s : GravityState) : PhysicalBivector:=s.2.1-physicalIIPlusBivector s.1

def simplicityDensity (s : GravityState) : ℝ:=gravitySimplicityMultiplierPairing s.2.2 (simplicityResidual s)

theorem simplicityDensity_original (u : JointParameter) (s : GravityState) :
    simplicityDensity s=generatedGravitySimplicityDensity (gravityPoint u s) :=rfl

def wedgeFirst (e h : LorentzianCoframe) : PhysicalBivector:=fun i p=>
  h (pairFirst i) (pairFirst p)*e (pairSecond i) (pairSecond p)+
    e (pairFirst i) (pairFirst p)*h (pairSecond i) (pairSecond p)-
      h (pairFirst i) (pairSecond p)*e (pairSecond i) (pairFirst p)-
        e (pairFirst i) (pairSecond p)*h (pairSecond i) (pairFirst p)

theorem wedgeFirst_generated (e h : LorentzianCoframe) (i p : Fin 6) :
    HasDerivAt (fun r : ℝ=>coframeWedge (e+r • h) i p) (wedgeFirst e h i p) 0 :=by
  have entry (a mu : Fin 4) : HasDerivAt (fun r : ℝ=>(e+r • h) a mu) (h a mu) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const (h a mu)).const_add (e a mu) using 1
    simp
  have generated:=((entry (pairFirst i) (pairFirst p)).mul (entry (pairSecond i) (pairSecond p))).sub
    ((entry (pairFirst i) (pairSecond p)).mul (entry (pairSecond i) (pairFirst p)))
  convert! generated using 1
  simp only [zero_smul,add_zero,wedgeFirst]
  ring

private def internalDualLinear : PhysicalBivector→ₗ[ℝ] PhysicalBivector where
  toFun:=internalBivectorDual
  map_add' B C:=by
    funext i p
    exact congrFun (lorentzianCoframeHodgeEquiv.map_add (fun j=>B j p) (fun j=>C j p)) i
  map_smul' t B:=by
    funext i p
    exact congrFun (lorentzianCoframeHodgeEquiv.map_smul t (fun j=>B j p)) i

def residualFirst (s d : GravityState) : PhysicalBivector:=d.2.1-internalBivectorDual (wedgeFirst s.1 d.1)

def simplicityFirst (s d : GravityState) : ℝ:=
  ∑i : Fin 6,∑p : Fin 6,(d.2.2 i p*(simplicityResidual s i p)^2+
    2*s.2.2 i p*simplicityResidual s i p*residualFirst s d i p)

theorem residualFirst_generated (s d : GravityState) :
    HasDerivAt (fun r : ℝ=>simplicityResidual (s+r • d)) (residualFirst s d) 0 :=by
  have wedge : HasDerivAt (fun r : ℝ=>coframeWedge (s.1+r • d.1)) (wedgeFirst s.1 d.1) 0:=
    hasDerivAt_pi.mpr (fun i=>hasDerivAt_pi.mpr (fun p=>wedgeFirst_generated _ _ i p))
  have dual:=internalDualLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 wedge
  have B : HasDerivAt (fun r : ℝ=>s.2.1+r • d.2.1) d.2.1 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const d.2.1).const_add s.2.1 using 1
    simp
  exact B.sub dual

theorem simplicityFirst_generated (s d : GravityState) :
    HasDerivAt (fun r : ℝ=>simplicityDensity (s+r • d)) (simplicityFirst s d) 0 :=by
  simp only [simplicityDensity,gravitySimplicityMultiplierPairing,simplicityFirst]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro p _
  have multiplier : HasDerivAt (fun r : ℝ=>(s+r • d).2.2 i p) (d.2.2 i p) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const (d.2.2 i p)).const_add (s.2.2 i p) using 1
    simp
  have residual:=hasDerivAt_pi.mp (hasDerivAt_pi.mp (residualFirst_generated s d) i) p
  convert! multiplier.mul (residual.pow 2) using 1
  simp only [Pi.pow_apply,Pi.mul_apply,zero_smul,add_zero,pow_one]
  ring

def nativeGravityDirection (a : Fin 6) (theta : ℝ) (s : GravityState) : GravityState:=
  ((theta • frameGenerator a)*s.1,bivectorDirection a theta s.2.1,bivectorDirection a theta s.2.2)

theorem nativeGravityDirection_original (a : Fin 6) (theta : ℝ) (u : JointParameter) :
    nativeGravityDirection a theta (originalGravityState u)=
      ((nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).coframe 0,
        (nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).gravityAuxiliary 0,
          (nativePrimitiveFamily (Fin.natAdd 3 a) theta 0 u).gravitySimplicityMultiplier 0) :=by
  simp only [nativePrimitiveFamily,Fin.addCases_right,lorentzPrimitiveDirection]
  rfl

def nativeSimplicityTorque (a : Fin 6) (theta : ℝ) (u : JointParameter) : ℝ:=
  simplicityFirst (originalGravityState u) (nativeGravityDirection a theta (originalGravityState u))

theorem nativeSimplicityTorque_generated (a : Fin 6) (theta : ℝ) (u : JointParameter) :
    HasDerivAt (fun r : ℝ=>generatedGravitySimplicityDensity (gravityPoint u
      (originalGravityState u+r • nativeGravityDirection a theta (originalGravityState u))))
      (nativeSimplicityTorque a theta u) 0 :=by
  simp only [←simplicityDensity_original,nativeSimplicityTorque]
  exact simplicityFirst_generated _ _

theorem fieldSimplicityTorque_generated (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>generatedGravitySimplicityDensity (gravityPoint u
      (originalGravityState u+r • originalGravityForce force)))
      (simplicityFirst (originalGravityState u) (originalGravityForce force)) 0 :=by
  simp only [←simplicityDensity_original]
  exact simplicityFirst_generated _ _

theorem nativeGravityDirection_affine (a : Fin 6) (theta : ℝ) (s h : GravityState) (r : ℝ) :
    nativeGravityDirection a theta (s+r • h)=nativeGravityDirection a theta s+r • nativeGravityDirection a theta h :=by
  apply Prod.ext
  · change (theta • frameGenerator a)*(s.1+r • h.1)=
      (theta • frameGenerator a)*s.1+r • ((theta • frameGenerator a)*h.1)
    rw [mul_add,mul_smul_comm]
  apply Prod.ext <;> funext i p <;>
    simp only [nativeGravityDirection,bivectorDirection,Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul] <;>
    (congr 1; apply Finset.sum_congr rfl; intro j _; ring)

private theorem wedgeFirst_moving (e d h c : LorentzianCoframe) (i p : Fin 6) :
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

def residualMixed (d h : GravityState) : PhysicalBivector:= -internalBivectorDual (wedgeFirst h.1 d.1)

private theorem residualFirst_moving (s d h c : GravityState) :
    HasDerivAt (fun r : ℝ=>residualFirst (s+r • h) (d+r • c))
      (residualMixed d h+residualFirst s c) 0 :=by
  have wedge : HasDerivAt (fun r : ℝ=>wedgeFirst (s.1+r • h.1) (d.1+r • c.1))
      (wedgeFirst h.1 d.1+wedgeFirst s.1 c.1) 0:=
    hasDerivAt_pi.mpr (fun i=>hasDerivAt_pi.mpr (fun p=>wedgeFirst_moving _ _ _ _ i p))
  have dual:=internalDualLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 wedge
  have B : HasDerivAt (fun r : ℝ=>d.2.1+r • c.2.1) c.2.1 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const c.2.1).const_add d.2.1 using 1
    simp
  have generated:=B.sub dual
  convert! generated using 1
  change residualMixed d h+residualFirst s c=c.2.1-internalDualLinear (wedgeFirst h.1 d.1+wedgeFirst s.1 c.1)
  rw [map_add]
  change -internalBivectorDual (wedgeFirst h.1 d.1)+(c.2.1-internalBivectorDual (wedgeFirst s.1 c.1))=
    c.2.1-(internalBivectorDual (wedgeFirst h.1 d.1)+internalBivectorDual (wedgeFirst s.1 c.1))
  abel

def simplicityMixed (s d h c : GravityState) : ℝ:=
  ∑i : Fin 6,∑p : Fin 6,(c.2.2 i p*(simplicityResidual s i p)^2+
    2*d.2.2 i p*simplicityResidual s i p*residualFirst s h i p+
    2*h.2.2 i p*simplicityResidual s i p*residualFirst s d i p+
    2*s.2.2 i p*residualFirst s h i p*residualFirst s d i p+
    2*s.2.2 i p*simplicityResidual s i p*(residualMixed d h+residualFirst s c) i p)

theorem simplicityMixed_generated (s d h c : GravityState) :
    HasDerivAt (fun r : ℝ=>simplicityFirst (s+r • h) (d+r • c)) (simplicityMixed s d h c) 0 :=by
  simp only [simplicityFirst,simplicityMixed]
  apply HasDerivAt.fun_sum
  intro i _
  apply HasDerivAt.fun_sum
  intro p _
  have entry (s k : GravityState) : HasDerivAt (fun r : ℝ=>(s+r • k).2.2 i p) (k.2.2 i p) 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).mul_const (k.2.2 i p)).const_add (s.2.2 i p) using 1
    simp
  have R:=hasDerivAt_pi.mp (hasDerivAt_pi.mp (residualFirst_generated s h) i) p
  have DR:=hasDerivAt_pi.mp (hasDerivAt_pi.mp (residualFirst_moving s d h c) i) p
  have generated:=((entry d c).mul (R.pow 2)).add
    ((((entry s h).const_mul 2).mul R).mul DR)
  convert! generated using 1
  simp only [Pi.pow_apply,Pi.mul_apply,zero_smul,add_zero,pow_one]
  ring

def nativeSimplicityMixed (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) : ℝ:=
  simplicityMixed (originalGravityState u) (nativeGravityDirection a theta (originalGravityState u))
    (originalGravityForce force) (nativeGravityDirection a theta (originalGravityForce force))

theorem nativeSimplicityMixed_generated (a : Fin 6) (theta : ℝ) (u : JointParameter) (force : Field289) :
    HasDerivAt (fun r : ℝ=>simplicityFirst (originalGravityState u+r • originalGravityForce force)
      (nativeGravityDirection a theta (originalGravityState u+r • originalGravityForce force)))
      (nativeSimplicityMixed a theta u force) 0 :=by
  simp only [nativeGravityDirection_affine,nativeSimplicityMixed]
  exact simplicityMixed_generated _ _ _ _

end LowEnergy.PreparationVacuumNativeFullGravityReturn
