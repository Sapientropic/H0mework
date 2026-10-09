import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationRepairedGravityMixedReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumGravityLegendreSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction StageNineBlockwiseConstitutive
open StageNineFormNativeMotherAction StageNineDiracDualFormNativeMotherAction
open StageNineTopologicalFourFormPairing StageNineTopologicalGravityCurvatureVariancePairing
open StageNineHolonomicGravityCurvatureVarianceNormalization
open PreparationVacuumNativeFullGravityReturn PreparationVacuumNativeSourceRestriction
open PreparationVacuumJointFieldResponse PreparationVacuumLorentzFieldInjection PreparationVacuumNativeFieldInjection
open PreparationVacuumRepairedGravityActionReturn PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open StageNineCompactSupportIntegrationByParts StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator
local instance : NormedAddCommGroup LorentzianCoframe:=Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe:=Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe:=Matrix.normedSpace

abbrev LorentzIndex:=Fin 4×Fin 6

def sourceConnectionMatrix (omega : LorentzBivectorOneForm) (mu : Fin 4) : LorentzianCoframe:=
  lorentzSkewConnectionOfBivectorOneForm omega mu

def sourceCurvatureQuadratic (omega : LorentzBivectorOneForm) : PhysicalBivector:=fun i p=>
  minkowskiInternalSign (pairFirst i)*
    (sourceConnectionMatrix omega (pairFirst p)*sourceConnectionMatrix omega (pairSecond p)-
      sourceConnectionMatrix omega (pairSecond p)*sourceConnectionMatrix omega (pairFirst p)) (pairFirst i) (pairSecond i)

def sourceCurvaturePolarization (omega eta : LorentzBivectorOneForm) : PhysicalBivector:=fun i p=>
  minkowskiInternalSign (pairFirst i)*
    ((sourceConnectionMatrix omega (pairFirst p)*sourceConnectionMatrix eta (pairSecond p)-
      sourceConnectionMatrix eta (pairSecond p)*sourceConnectionMatrix omega (pairFirst p))+
      (sourceConnectionMatrix eta (pairFirst p)*sourceConnectionMatrix omega (pairSecond p)-
        sourceConnectionMatrix omega (pairSecond p)*sourceConnectionMatrix eta (pairFirst p))) (pairFirst i) (pairSecond i)

def sourceConnectionBasis (i : LorentzIndex) : LorentzBivectorOneForm:=fun mu a=>if (mu,a)=i then 1 else 0

def sourceLorentzBilinear (e : LorentzianCoframe) (omega eta : LorentzBivectorOneForm) : ℝ:=
  gravityTopologicalBFCoefficient (physicalIIPlusBivector e) (sourceCurvaturePolarization omega eta)

def sourceLorentzHessian (e : LorentzianCoframe) : Matrix LorentzIndex LorentzIndex ℝ:=fun i j=>
  sourceLorentzBilinear e (sourceConnectionBasis i) (sourceConnectionBasis j)

def sourceLorentzQuadratic (e : LorentzianCoframe) (omega : LorentzBivectorOneForm) : ℝ:=
  gravityTopologicalBFCoefficient (physicalIIPlusBivector e) (sourceCurvatureQuadratic omega)

def sourceConnectionConfiguration (u : JointParameter) (e : LorentzianCoframe) (omega : LorentzBivectorOneForm) :
    StageNineHolonomicConfiguration:=
  {primitiveFamily u with coframe:=fun _=>e,gravityConnection:=fun _=>sourceConnectionMatrix omega}

theorem sourceCurvatureQuadratic_original (u : JointParameter) (e : LorentzianCoframe) (omega : LorentzBivectorOneForm) :
    holonomicGravityCurvature (sourceConnectionConfiguration u e omega) 0=sourceCurvatureQuadratic omega :=by
  funext i p
  simp [holonomicGravityCurvature,sourceConnectionConfiguration,sourceCurvatureQuadratic,
    gravityConnectionDerivative,fieldDirectionalDerivative,Matrix.mul_apply]

theorem sourceLorentzQuadratic_original (u : JointParameter) (e : LorentzianCoframe) (omega : LorentzBivectorOneForm) :
    reducedGravityDensity ((e,(primitiveFamily u).gravityAuxiliary 0,(primitiveFamily u).gravitySimplicityMultiplier 0),
      holonomicGravityCurvature (sourceConnectionConfiguration u e omega) 0)=sourceLorentzQuadratic e omega-3*e.det :=by
  rw [reducedGravityDensity_volume,sourceCurvatureQuadratic_original]
  rfl

theorem sourceCurvaturePolarization_original (omega eta : LorentzBivectorOneForm) :
    sourceCurvatureQuadratic (omega+eta)-sourceCurvatureQuadratic omega-sourceCurvatureQuadratic eta=
      sourceCurvaturePolarization omega eta :=by
  funext i p
  simp only [sourceCurvatureQuadratic,sourceCurvaturePolarization,sourceConnectionMatrix,
    lorentzSkewConnectionOfBivectorOneForm_add,Pi.add_apply,Pi.sub_apply,Matrix.add_apply,
    Matrix.sub_apply,mul_add,add_mul]
  ring

theorem sourceCurvaturePolarization_diagonal (omega : LorentzBivectorOneForm) :
    sourceCurvaturePolarization omega omega=(2:ℝ) • sourceCurvatureQuadratic omega :=by
  funext i p
  simp only [sourceCurvaturePolarization,sourceCurvatureQuadratic,Matrix.add_apply,Matrix.sub_apply,
    Pi.smul_apply,smul_eq_mul]
  ring

theorem sourceLorentzBilinear_symmetric (e : LorentzianCoframe) (omega eta : LorentzBivectorOneForm) :
    sourceLorentzBilinear e omega eta=sourceLorentzBilinear e eta omega :=by
  unfold sourceLorentzBilinear
  congr 1
  funext i p
  simp only [sourceCurvaturePolarization,Matrix.add_apply,Matrix.sub_apply]
  ring

theorem sourceLorentzHessian_symmetric (e : LorentzianCoframe) (i j : LorentzIndex) :
    sourceLorentzHessian e i j=sourceLorentzHessian e j i:=
  sourceLorentzBilinear_symmetric e (sourceConnectionBasis i) (sourceConnectionBasis j)

private def connectionEntry (mu i j : Fin 4) : LorentzBivectorOneForm→ₗ[ℝ] ℝ where
  toFun omega:=sourceConnectionMatrix omega mu i j
  map_add' omega eta:=by
    simp only [sourceConnectionMatrix,lorentzSkewConnectionOfBivectorOneForm_add,Pi.add_apply,Matrix.add_apply]
  map_smul' r omega:=by
    simp only [sourceConnectionMatrix,lorentzSkewConnectionOfBivectorOneForm_smul,Pi.smul_apply,Matrix.smul_apply,smul_eq_mul]
    rfl

private def sourceCurvatureReader (e : LorentzianCoframe) : PhysicalBivector→ₗ[ℝ] ℝ where
  toFun R:=gravityTopologicalBFCoefficient (physicalIIPlusBivector e) R
  map_add' R S:=gravityTopologicalBFCoefficient_add_right _ R S
  map_smul' r R:=gravityTopologicalBFCoefficient_smul_right r _ R

theorem sourceCurvatureQuadratic_first (omega eta : LorentzBivectorOneForm) :
    HasDerivAt (fun r : ℝ=>sourceCurvatureQuadratic (omega+r • eta)) (sourceCurvaturePolarization omega eta) 0 :=by
  have line : HasDerivAt (fun r : ℝ=>omega+r • eta) eta 0:=by
    convert! ((hasDerivAt_id (0:ℝ)).smul_const eta).const_add omega using 1
    simp
  have entry (mu i j : Fin 4) : HasDerivAt (fun r : ℝ=>sourceConnectionMatrix (omega+r • eta) mu i j)
      (sourceConnectionMatrix eta mu i j) 0:=
    (connectionEntry mu i j).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 line
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro p
  have each (k : Fin 4):=((entry (pairFirst p) (pairFirst i) k).mul (entry (pairSecond p) k (pairSecond i))).sub
    ((entry (pairSecond p) (pairFirst i) k).mul (entry (pairFirst p) k (pairSecond i)))
  have generated:=(HasDerivAt.fun_sum (fun k (_ : k∈(Finset.univ : Finset (Fin 4)))=>each k)).const_mul (minkowskiInternalSign (pairFirst i))
  convert! generated using 1
  · funext r
    simp only [sourceCurvatureQuadratic,Matrix.sub_apply,Matrix.mul_apply,Finset.sum_sub_distrib,Pi.sub_apply,Pi.mul_apply]
  · simp only [sourceCurvaturePolarization,zero_smul,add_zero,Matrix.add_apply,Matrix.sub_apply,
      Matrix.mul_apply,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem sourceLorentzQuadratic_first (e : LorentzianCoframe) (omega eta : LorentzBivectorOneForm) :
    HasDerivAt (fun r : ℝ=>sourceLorentzQuadratic e (omega+r • eta)) (sourceLorentzBilinear e omega eta) 0 :=
  (sourceCurvatureReader e).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0
    (sourceCurvatureQuadratic_first omega eta)

private def sourceCurvaturePolarizationLeft (eta : LorentzBivectorOneForm) :
    LorentzBivectorOneForm→ₗ[ℝ] PhysicalBivector where
  toFun omega:=sourceCurvaturePolarization omega eta
  map_add' omega theta:=by
    funext i p
    simp only [sourceCurvaturePolarization,sourceConnectionMatrix,lorentzSkewConnectionOfBivectorOneForm_add,
      Pi.add_apply,Matrix.add_apply,Matrix.sub_apply,mul_add,add_mul]
    ring
  map_smul' r omega:=by
    funext i p
    simp only [sourceCurvaturePolarization,sourceConnectionMatrix,lorentzSkewConnectionOfBivectorOneForm_smul,
      Pi.smul_apply,Matrix.smul_apply,smul_eq_mul,smul_mul_assoc,mul_smul_comm,
      Matrix.add_apply,Matrix.sub_apply,RingHom.id_apply]
    ring

def sourceLorentzLinear (e : LorentzianCoframe) (eta : LorentzBivectorOneForm) : LorentzBivectorOneForm→ₗ[ℝ] ℝ:=
  (sourceCurvatureReader e).comp (sourceCurvaturePolarizationLeft eta)

theorem sourceLorentzHessian_generated (e : LorentzianCoframe) (i j : LorentzIndex) :
    HasDerivAt (fun r : ℝ=>sourceLorentzBilinear e (r • sourceConnectionBasis i) (sourceConnectionBasis j))
      (sourceLorentzHessian e i j) 0 :=by
  have source : HasDerivAt (fun r : ℝ=>r • sourceConnectionBasis i) (sourceConnectionBasis i) 0:=by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (sourceConnectionBasis i))
  exact (sourceLorentzLinear e (sourceConnectionBasis j)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 source

theorem sourceConnection_fullBasis (omega : LorentzBivectorOneForm) :
    omega=∑i : LorentzIndex,omega i.1 i.2 • sourceConnectionBasis i :=by
  funext mu a
  simp [sourceConnectionBasis,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]

theorem sourceLorentzQuadratic_fullMatrix (e : LorentzianCoframe) (omega : LorentzBivectorOneForm) :
    sourceLorentzQuadratic e omega=(1/2:ℝ)*
      ∑i : LorentzIndex,∑j : LorentzIndex,omega i.1 i.2*sourceLorentzHessian e i j*omega j.1 j.2 :=by
  have diagonal : sourceLorentzBilinear e omega omega=2*sourceLorentzQuadratic e omega:=by
    rw [sourceLorentzBilinear,sourceCurvaturePolarization_diagonal,gravityTopologicalBFCoefficient_smul_right]
    rfl
  have basis : sourceLorentzBilinear e omega omega=
      ∑i : LorentzIndex,∑j : LorentzIndex,omega i.1 i.2*sourceLorentzHessian e i j*omega j.1 j.2:=by
    change sourceLorentzLinear e omega omega=_
    have expansion : sourceLorentzLinear e omega omega=
        ∑i : LorentzIndex,omega i.1 i.2*sourceLorentzLinear e omega (sourceConnectionBasis i):=by
      calc
        sourceLorentzLinear e omega omega=sourceLorentzLinear e omega
          (∑i : LorentzIndex,omega i.1 i.2 • sourceConnectionBasis i):=
            congrArg (sourceLorentzLinear e omega) (sourceConnection_fullBasis omega)
        _= _:=by simp only [map_sum,map_smul,smul_eq_mul]
    rw [expansion]
    apply Finset.sum_congr rfl
    intro i _
    rw [show sourceLorentzLinear e omega (sourceConnectionBasis i)=
      sourceLorentzLinear e (sourceConnectionBasis i) omega from sourceLorentzBilinear_symmetric e _ _]
    have expansion2 : sourceLorentzLinear e (sourceConnectionBasis i) omega=
        ∑j : LorentzIndex,omega j.1 j.2*sourceLorentzLinear e (sourceConnectionBasis i) (sourceConnectionBasis j):=by
      calc
        sourceLorentzLinear e (sourceConnectionBasis i) omega=sourceLorentzLinear e (sourceConnectionBasis i)
          (∑j : LorentzIndex,omega j.1 j.2 • sourceConnectionBasis j):=
            congrArg (sourceLorentzLinear e (sourceConnectionBasis i)) (sourceConnection_fullBasis omega)
        _= _:=by simp only [map_sum,map_smul,smul_eq_mul]
    rw [expansion2,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [sourceLorentzHessian_symmetric]
    change omega i.1 i.2*(omega j.1 j.2*sourceLorentzHessian e j i)=
      omega i.1 i.2*sourceLorentzHessian e j i*omega j.1 j.2
    ring
  rw [diagonal] at basis
  linarith

end LowEnergy.PreparationVacuumGravityLegendreSource
