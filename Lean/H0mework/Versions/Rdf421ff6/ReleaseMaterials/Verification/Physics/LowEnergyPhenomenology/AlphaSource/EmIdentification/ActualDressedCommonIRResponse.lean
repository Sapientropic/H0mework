import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRSourceOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformMaterialCoefficients
open Polynomial GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumNoetherChart
open PreparationVacuumCurrentSignalOperator PreparationVacuumPropagationPencil PreparationVacuumActionFieldLift
open SourcePropagationAlgebraicResponse PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalFeedback PreparationVacuumOriginalGreenFeedback ActualEMAction
open ActualDressedNoether ActualDressedFullCoulomb ActualDressedFrequencyHalf ActualDressedUniformRayCoefficients ActualDressedPhysicalRayNumerator
open scoped Matrix BigOperators
private theorem drive_eval {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (B C X : CoefficientAlgebra A) :
    coefficientEval v (-((MvPolynomial.C (-Complex.I) : Parameters) • B)*X+
      X*((MvPolynomial.C (-Complex.I) : Parameters) • C))=
      -((-Complex.I) • (coefficientEval v B*coefficientEval v X))+
        (-Complex.I) • (coefficientEval v X*coefficientEval v C) := by
  simp only [map_add,map_mul,map_neg,coefficient_eval_smul,MvPolynomial.eval_C,
    neg_mul,smul_mul_assoc,mul_smul_comm]
private theorem observed_response_clear {E : Type*} [AddCommGroup E] [Module ℂ E]
    (observer : E→ₗ[ℂ]ℂ) (L R D : E→ₗ[ℂ]E) (M C B M' C' B' : E) (l r d : ℂ)
    (hm : M'=d • M) (hc : C'=d • C) (hb : B'=d • B) :
    observer (r • L M'+l • R C'+R (D (L B')))=d*observer (r • L M+l • R C+R (D (L B))) := by
  rw [hm,hc,hb]
  simp only [map_smul]
  have factor : r • (d • L M)+l • (d • R C)+d • R (D (L B))=
      d • (r • L M+l • R C+R (D (L B))) := by module
  rw [factor,map_smul,smul_eq_mul]
@[instance_reducible] private def coefficientRing {A : Type*} [Ring A] [Algebra ℂ A] : Ring (CoefficientAlgebra A):=inferInstance
local instance : Ring ParameterOp:=coefficientRing (A:=Op)
local instance : AddCommGroup ParameterOp:=(inferInstance : Ring ParameterOp).toAddCommGroup
local instance : AddGroup ParameterOp:=(inferInstance : AddCommGroup ParameterOp).toAddGroup
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointCurrent jointResolvent rawReader noetherReader rawInitial
  sourceMaterialMap sourceContactMap dressedKinematicPoint dressedEulerObserver frequencyHalfPolarization
  uniformClockPolynomial uniformClockNumerator frequencyResponsePencil emOriginalJacobi originalJacobiTerms
def irClock : Parameters:=MvPolynomial.X 1-MvPolynomial.C Complex.I*(MvPolynomial.X 0)^2*MvPolynomial.X 2
def leftMaterialDenominator (event : DressedEvent) (n : PhysicalMomentum) : Parameters:=
  (commonJointPolynomial event n).eval (MvPolynomial.C event.energy)
def rightMaterialDenominator (event : DressedEvent) : Parameters:=
  MvPolynomial.C ((jointPolynomial event.momentum event.frame).eval event.energy)
def materialDenominator (event : DressedEvent) (n : PhysicalMomentum) : Parameters:=
  (leftMaterialDenominator event n)^2*(rightMaterialDenominator event)^2
def rightMaterialNumerator (event : DressedEvent) : ParameterOp:=
  constantOp (materialJointNumerator event.momentum event.frame event.energy)
def materialRawNumerator (event : DressedEvent) (n : PhysicalMomentum) (reader : Field289) : ParameterOp:=
  (leftMaterialDenominator event n*rightMaterialDenominator event) •
    (commonMaterialLeft event n*constantOp (rawReader reader event.momentum event.frame 0)*rightMaterialNumerator event)
def materialContactNumerator (event : DressedEvent) (n : PhysicalMomentum) (reader force : Field289) : ParameterOp:=
  (leftMaterialDenominator event n*rightMaterialDenominator event) •
    (commonMaterialLeft event n*constantOp (fderiv ℝ (noetherReader reader event.momentum event.frame) 0 force)*rightMaterialNumerator event)
def materialFullNumerator (event : DressedEvent) (n : PhysicalMomentum) (reader force : Field289) : ParameterOp:=
  -(rightMaterialDenominator event) • (commonMaterialLeft event n*commonLeftCurrent event n event.energy force*
    commonMaterialLeft event n*constantOp (rawReader reader event.momentum event.frame 0)*rightMaterialNumerator event)-
  (leftMaterialDenominator event n) • (commonMaterialLeft event n*constantOp (rawReader reader event.momentum event.frame 0)*
    rightMaterialNumerator event*constantOp (jointCurrent event.momentum event.frame event.energy 0 force)*rightMaterialNumerator event)
def commonDrive (event : DressedEvent) (n : PhysicalMomentum) (force : Field289) : Module.End Parameters ParameterOp:=
  -(LinearMap.mul Parameters ParameterOp ((MvPolynomial.C (-Complex.I) : Parameters) • commonLeftCurrent event n 0 force))+
    (LinearMap.mul Parameters ParameterOp).flip
      ((MvPolynomial.C (-Complex.I) : Parameters) • constantOp (jointCurrent event.momentum event.frame 0 0 force))
attribute [local irreducible] commonLeftGenerator commonLeftCurrent commonMaterialLeft commonClockAction constantOp
private theorem polynomial_value_eval (P : Parameters[X]) (v : Fin 3→ℂ) (z : Parameters) :
    MvPolynomial.eval v (P.eval z)=(P.map (MvPolynomial.eval v)).eval (MvPolynomial.eval v z) :=
  (eval_map_apply (p:=P) (MvPolynomial.eval v) z).symm
theorem left_material_denominator_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) :
    MvPolynomial.eval (irValues eps sigma s) (leftMaterialDenominator event n)=
      (jointPolynomial (event.momentum-(eps^2:ℝ) • n) event.frame).eval event.energy := by
  rw [leftMaterialDenominator,polynomial_value_eval,common_joint_polynomial_eval,MvPolynomial.eval_C]
theorem material_denominator_nonzero (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) :
    MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n)≠0 := by
  simp only [materialDenominator,map_mul,map_pow,left_material_denominator_eval,rightMaterialDenominator,MvPolynomial.eval_C]
  exact mul_ne_zero (pow_ne_zero 2 (source_joint_polynomial_nonreal _ _ _ event.nonreal))
    (pow_ne_zero 2 (source_joint_polynomial_nonreal _ _ _ event.nonreal))
private theorem clear_raw {A : Type*} [Ring A] [Algebra ℂ A]
    (L R KL KR J : A) (dl dr : ℂ) (left : dl • L=KL) (right : dr • R=KR) :
    (dl^2*dr^2) • (L*J*R)=(dl*dr) • (KL*J*KR) := by
  rw [←left,←right];simp only [smul_mul_assoc,mul_smul_comm,smul_smul,pow_two]
  congr 1;ring
private theorem clear_material {A : Type*} [Ring A] [Algebra ℂ A]
    (L R KL KR J JL JR : A) (dl dr : ℂ) (left : dl • L=KL) (right : dr • R=KR) :
    (dl^2*dr^2) • ((-L)*JL*(L*J*R)+(L*J*R)*JR*(-R))=
      -dr • (KL*JL*KL*J*KR)-dl • (KL*J*KR*JR*KR) := by
  rw [←left,←right];simp only [smul_mul_assoc,mul_smul_comm,smul_smul,smul_add,smul_neg,neg_mul,mul_neg,mul_assoc,pow_two]
  module
private theorem material_data_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ)
    (reader force : Field289) :
    coefficientEval (irValues eps sigma s) (materialFullNumerator event n reader force)=
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        sourceMaterialMap (dressedKinematicPoint event ((eps^2:ℝ) • n)) reader force ∧
    coefficientEval (irValues eps sigma s) (materialContactNumerator event n reader force)=
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        sourceContactMap (dressedKinematicPoint event ((eps^2:ℝ) • n)) reader force ∧
    coefficientEval (irValues eps sigma s) (materialRawNumerator event n reader)=
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        rawInitial (dressedKinematicPoint event ((eps^2:ℝ) • n)) reader := by
  let p:=event.momentum-(eps^2:ℝ) • n
  let L:=jointResolvent p event.frame event.energy 0
  let R:=jointResolvent event.momentum event.frame event.energy 0
  let KL:=materialJointNumerator p event.frame event.energy
  let KR:=materialJointNumerator event.momentum event.frame event.energy
  let dl:=(jointPolynomial p event.frame).eval event.energy
  let dr:=(jointPolynomial event.momentum event.frame).eval event.energy
  have left : dl • L=KL:=actual_material_joint_inverse_clear p event.frame event.energy event.nonreal
  have right : dr • R=KR:=actual_material_joint_inverse_clear event.momentum event.frame event.energy event.nonreal
  have material : sourceMaterialMap (dressedKinematicPoint event ((eps^2:ℝ) • n)) reader force=
      (-L)*jointCurrent p event.frame event.energy 0 force*(L*rawReader reader event.momentum event.frame 0*R)+
        (L*rawReader reader event.momentum event.frame 0*R)*jointCurrent event.momentum event.frame event.energy 0 force*(-R) := by
    unfold sourceMaterialMap dressedKinematicPoint;rfl
  have contact : sourceContactMap (dressedKinematicPoint event ((eps^2:ℝ) • n)) reader force=
      L*fderiv ℝ (noetherReader reader event.momentum event.frame) 0 force*R := by
    unfold sourceContactMap dressedKinematicPoint;rfl
  have initial : rawInitial (dressedKinematicPoint event ((eps^2:ℝ) • n)) reader=L*rawReader reader event.momentum event.frame 0*R := by
    unfold rawInitial dressedKinematicPoint;rfl
  simp only [materialFullNumerator,materialContactNumerator,materialRawNumerator,map_sub,map_neg,map_mul,
    coefficient_eval_smul,left_material_denominator_eval,rightMaterialDenominator,MvPolynomial.eval_C,
    common_material_left_eval,common_left_current_eval,constantOp,coefficient_eval_constant,rightMaterialNumerator,
    materialDenominator,map_pow,material,contact,initial]
  constructor
  · exact (clear_material L R KL KR _ _ _ dl dr left right).symm
  exact ⟨(clear_raw L R KL KR _ dl dr left right).symm,(clear_raw L R KL KR _ dl dr left right).symm⟩
theorem common_drive_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ)
    (force : Field289) (A : ParameterOp) :
    coefficientEval (irValues eps sigma s) (commonDrive event n force A)=
      driveOperator (dressedKinematicPoint event ((eps^2:ℝ) • n)) force (coefficientEval (irValues eps sigma s) A) := by
  have evaluated:=drive_eval (A:=Op) (irValues eps sigma s) (commonLeftCurrent event n 0 force)
    (constantOp (jointCurrent event.momentum event.frame 0 0 force)) A
  have aligned : coefficientEval (irValues eps sigma s) (commonDrive event n force A)=
      -((-Complex.I) • (jointCurrent (event.momentum-(eps^2:ℝ) • n) event.frame 0 0 force*coefficientEval (irValues eps sigma s) A))+
      (-Complex.I) • (coefficientEval (irValues eps sigma s) A*jointCurrent event.momentum event.frame 0 0 force) := by
    simpa only [commonDrive,LinearMap.add_apply,LinearMap.neg_apply,LinearMap.mul_apply',LinearMap.flip_apply,
      neg_mul,common_left_current_eval,constantOp,coefficient_eval_constant] using evaluated
  have returned : driveOperator (dressedKinematicPoint event ((eps^2:ℝ) • n)) force (coefficientEval (irValues eps sigma s) A)=
      -((-Complex.I) • (jointCurrent (event.momentum-(eps^2:ℝ) • n) event.frame 0 0 force*coefficientEval (irValues eps sigma s) A))+
      (-Complex.I) • (coefficientEval (irValues eps sigma s) A*jointCurrent event.momentum event.frame 0 0 force) := by
    unfold driveOperator leftCurrent rightCurrent dressedKinematicPoint
    simp only [add_apply,neg_apply,ContinuousLinearMap.mul_apply',
      ContinuousLinearMap.flip_apply,smul_mul_assoc,mul_smul_comm,sub_eq_add_neg]
  exact aligned.trans returned.symm
def commonDenominator (event : DressedEvent) (n : PhysicalMomentum) : Parameters:=
  (commonClockPolynomial event n).eval irClock*(commonClockPolynomial event n).eval (MvPolynomial.X 1)*materialDenominator event n
def commonNumerator (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) Parameters:=fun i j=>
  coefficientObserver (dressedEulerObserver event).toLinearMap
    ((commonClockPolynomial event n).eval (MvPolynomial.X 1) •
        commonClockAction event n irClock (materialFullNumerator event n (fieldUnit i) (fieldUnit j))+
      (commonClockPolynomial event n).eval irClock •
        commonClockAction event n (MvPolynomial.X 1) (materialContactNumerator event n (fieldUnit i) (fieldUnit j))+
      commonClockAction event n (MvPolynomial.X 1)
        (commonDrive event n (fieldUnit j) (commonClockAction event n irClock (materialRawNumerator event n (fieldUnit i)))))
private theorem ir_clock_eval (eps sigma s : ℝ) :
    MvPolynomial.eval (irValues eps sigma s) irClock=dampedFourierClock (sourceFrequency eps s) sigma := by
  simp [irClock,irValues,dampedFourierClock,sourceFrequency,Complex.ofReal_mul,Complex.ofReal_pow,mul_assoc]
private theorem clock_value_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) (lambda : Parameters) :
    MvPolynomial.eval (irValues eps sigma s) ((commonClockPolynomial event n).eval lambda)=
      (uniformClockPolynomial (dressedKinematicPoint event ((eps^2:ℝ) • n))).eval (MvPolynomial.eval (irValues eps sigma s) lambda) := by
  rw [polynomial_value_eval,common_clock_polynomial_eval]
theorem common_numerator_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) :
    (commonNumerator event n).map (MvPolynomial.eval (irValues eps sigma s))=
      MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) •
        uniformRayNumerator event eps s sigma n := by
  funext i j
  let q:=dressedKinematicPoint event ((eps^2:ℝ) • n)
  let lambda:=dampedFourierClock (sourceFrequency eps s) sigma
  let v:=irValues eps sigma s
  let d:=MvPolynomial.eval v (materialDenominator event n)
  have data:=material_data_eval event n eps sigma s (fieldUnit i) (fieldUnit j)
  have evaluated : (commonNumerator event n).map (MvPolynomial.eval v) i j=
      dressedEulerObserver event
        (((uniformClockPolynomial q).eval (sigma:ℂ)) • uniformClockNumerator q lambda (coefficientEval v (materialFullNumerator event n (fieldUnit i) (fieldUnit j)))+
          ((uniformClockPolynomial q).eval lambda) • uniformClockNumerator q (sigma:ℂ) (coefficientEval v (materialContactNumerator event n (fieldUnit i) (fieldUnit j)))+
          uniformClockNumerator q (sigma:ℂ) (driveOperator q (fieldUnit j) (uniformClockNumerator q lambda (coefficientEval v (materialRawNumerator event n (fieldUnit i)))))) := by
    dsimp only [v,q,lambda]
    simp only [Matrix.map_apply,commonNumerator,coefficient_observer_eval,map_add,coefficient_eval_smul,
      clock_value_eval,common_clock_action_eval,common_drive_eval,ir_clock_eval,MvPolynomial.eval_X,irValues,one_ne_zero,ite_false,ite_true,ContinuousLinearMap.coe_coe]
  have returned:=observed_response_clear (dressedEulerObserver event).toLinearMap
    (uniformClockNumerator q lambda).toLinearMap (uniformClockNumerator q (sigma:ℂ)).toLinearMap
    (driveOperator q (fieldUnit j)).toLinearMap
    (sourceMaterialMap q (fieldUnit i) (fieldUnit j)) (sourceContactMap q (fieldUnit i) (fieldUnit j)) (rawInitial q (fieldUnit i))
    _ _ _ ((uniformClockPolynomial q).eval lambda) ((uniformClockPolynomial q).eval (sigma:ℂ)) d data.1 data.2.1 data.2.2
  exact evaluated.trans returned
theorem actual_common_ir_pi_clear (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) (positive : 0<sigma) :
    MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n) •
      frequencyHalfPolarization event ((eps^2:ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)=(commonNumerator event n).map (MvPolynomial.eval (irValues eps sigma s)) := by
  rw [common_numerator_eval]
  have denominator : MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n)=
      uniformRayDenominator event eps s sigma n*MvPolynomial.eval (irValues eps sigma s) (materialDenominator event n) := by
    simp only [commonDenominator,map_mul,clock_value_eval,ir_clock_eval,MvPolynomial.eval_X,irValues,one_ne_zero,ite_false,ite_true,
      uniformRayDenominator,actual_uniform_clock_charge_coefficients]
  rw [denominator,mul_comm,←smul_smul,actual_uniform_physical_ray_pi_clear event eps s sigma n positive]
def commonIRMomentum (n : PhysicalMomentum) : Fin 4→Parameters:=
  Fin.cases (-MvPolynomial.C Complex.I*(MvPolynomial.X 0)^2*MvPolynomial.X 2)
    (fun i=>MvPolynomial.C Complex.I*(MvPolynomial.X 0)^2*MvPolynomial.C (n i:ℂ))
private theorem common_momentum_eval (n : PhysicalMomentum) (eps sigma s : ℝ) :
    (fun i=>MvPolynomial.eval (irValues eps sigma s) (commonIRMomentum n i))=frequencyRay eps s n := by
  funext i
  refine Fin.cases ?_ (fun j=>?_) i <;> simp [commonIRMomentum,frequencyRay,physicalFrequencyMomentum,irValues,
    Complex.ofReal_mul,Complex.ofReal_pow] <;> ring
private def polynomialTerm (q : Fin 4→Parameters) (a : SourceTerm) : Matrix (Fin 289) (Fin 289) Parameters:=
  Matrix.single a.row a.column (MvPolynomial.C (coefficientValue a.coefficient)*
    q 0^a.powers.temporal*q 1^a.powers.first*q 2^a.powers.second*q 3^a.powers.third)
def commonJacobi (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) Parameters:=
  (originalJacobiTerms.map (polynomialTerm (commonIRMomentum n))).sum
private theorem polynomial_terms_eval (terms : List SourceTerm) (q : Fin 4→Parameters) (v : Fin 3→ℂ) :
    (terms.map (polynomialTerm q)).sum.map (MvPolynomial.eval v)=sourceMatrix terms (fun i=>MvPolynomial.eval v (q i)) := by
  induction terms with
  | nil=>simp [sourceMatrix]
  | cons a rest ih=>
    simp only [List.map_cons,List.sum_cons]
    rw [Matrix.map_add _ (fun a b=>(MvPolynomial.eval v).map_add a b),ih]
    simp only [sourceMatrix,List.map_cons,List.sum_cons]
    congr 1
    rw [polynomialTerm,Matrix.map_single]
    simp only [map_mul,map_pow,MvPolynomial.eval_C,SourceTerm.matrix,Powers.value,mul_assoc]
theorem common_jacobi_eval (n : PhysicalMomentum) (eps sigma s : ℝ) :
    (commonJacobi n).map (MvPolynomial.eval (irValues eps sigma s))=emOriginalJacobi (frequencyRay eps s n) := by
  rw [commonJacobi,polynomial_terms_eval,common_momentum_eval,em_jacobi_source]
  rfl
def commonClearedPencil (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) Parameters:=
  commonDenominator event n • commonJacobi n-(MvPolynomial.X 1 : Parameters) • commonNumerator event n
theorem actual_common_ir_pencil_clear (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) (positive : 0<sigma) :
    MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n) •
      frequencyResponsePencil event ((eps^2:ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)=(commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s)) := by
  rw [damped_source_sheet_response event eps s sigma n positive,smul_sub]
  have cleared:=actual_common_ir_pi_clear event n eps sigma s positive;unfold commonClearedPencil
  rw [Matrix.map_sub _ (fun a b=>(MvPolynomial.eval (irValues eps sigma s)).map_sub a b),
    Matrix.map_smul' _ _ _ (fun a b=>(MvPolynomial.eval (irValues eps sigma s)).map_mul a b),
    Matrix.map_smul' _ _ _ (fun a b=>(MvPolynomial.eval (irValues eps sigma s)).map_mul a b),common_jacobi_eval]
  simp only [MvPolynomial.eval_X,irValues,one_ne_zero,ite_false,ite_true]
  congr 1;rw [smul_comm,cleared]
end LowEnergy.GaussComposite.ActualDressedUniformMaterialCoefficients
