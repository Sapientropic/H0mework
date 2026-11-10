import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularOperatorCoefficients
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRResponse
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonDenominatorNonzero

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
open Polynomial GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalHalfAxis
open PreparationVacuumNoetherChart PreparationVacuumCurrentSignalOperator PreparationVacuumPropagationPencil
open PreparationVacuumRawJointFeedback PreparationVacuumOriginalGreenFeedback
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedFrequencyHalf ActualDressedUniformRayCoefficients
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator ActualEMAction
open scoped TensorProduct Matrix BigOperators
@[instance_reducible] private def angularRing {A : Type*} [Ring A] [Algebra ℂ A] : Ring (AngularCoefficients A) := inferInstance
@[instance_reducible] private def legacyRing {A : Type*} [Ring A] [Algebra ℂ A] : Ring (CoefficientAlgebra A) := inferInstance
local instance : Ring AngularOp := angularRing (A:=SourceOp)
local instance : AddCommGroup AngularOp := (inferInstance : Ring AngularOp).toAddCommGroup
local instance : AddGroup AngularOp := (inferInstance : AddCommGroup AngularOp).toAddGroup
local instance : Ring ParameterOp := legacyRing (A:=SourceOp)
local instance : AddCommGroup ParameterOp := (inferInstance : Ring ParameterOp).toAddCommGroup
local instance : AddGroup ParameterOp := (inferInstance : AddCommGroup ParameterOp).toAddGroup
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem specialize_C (n : PhysicalMomentum) (c : ℂ) : angularSpecialize n (MvPolynomial.C c)=MvPolynomial.C c := by
  simp only [angularSpecialize,MvPolynomial.eval₂Hom_C]
private theorem specialize_ir (n : PhysicalMomentum) (i : Fin 3) :
    angularSpecialize n (MvPolynomial.X (Fin.castAdd 3 i))=MvPolynomial.X i := by
  simp only [angularSpecialize,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_X,Fin.addCases_left]
private theorem specialize_value (n : PhysicalMomentum) (P : AngularParameters[X]) (z : AngularParameters) :
    angularSpecialize n (P.eval z)=(P.map (angularSpecialize n)).eval (angularSpecialize n z) :=
  (eval_map_apply (p:=P) (angularSpecialize n) z).symm

def angularObserver {A : Type*} [AddCommGroup A] [Module ℂ A] (observer : A→ₗ[ℂ]ℂ) :
    AngularCoefficients A→ₗ[ℂ]AngularParameters :=
  (TensorProduct.AlgebraTensorModule.rid ℂ ℂ AngularParameters).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : AngularParameters→ₗ[ℂ]AngularParameters) observer)

theorem angular_observer_specialize {A : Type*} [Ring A] [Algebra ℂ A]
    (observer : A→ₗ[ℂ]ℂ) (n : PhysicalMomentum) (B : AngularCoefficients A) :
    angularSpecialize n (angularObserver observer B)=coefficientObserver observer (angularCoefficientSpecialize n B) := by
  induction B using TensorProduct.induction_on with
  | zero => simp
  | tmul P B =>
    simp only [angularObserver,angularCoefficientSpecialize,coefficientObserver,angularSpecializeAlg,
      LinearMap.comp_apply,TensorProduct.map_tmul,LinearMap.id_apply,Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    change angularSpecialize n (observer B • P)=observer B • angularSpecialize n P
    exact (angularSpecializeAlg n).toLinearMap.map_smul (observer B) P
  | add B C hB hC => simp only [map_add,hB,hC]

def angularIRClock : AngularParameters :=
  MvPolynomial.X 1-MvPolynomial.C Complex.I*(MvPolynomial.X 0)^2*MvPolynomial.X 2
private theorem specialize_clock (n : PhysicalMomentum) : angularSpecialize n angularIRClock=irClock := by
  simp only [angularIRClock,map_sub,map_mul,map_pow,specialize_C]
  rw [show (0 : Fin 6)=Fin.castAdd 3 (0 : Fin 3) from rfl,
    show (1 : Fin 6)=Fin.castAdd 3 (1 : Fin 3) from rfl,
    show (2 : Fin 6)=Fin.castAdd 3 (2 : Fin 3) from rfl]
  simp only [specialize_ir,irClock]

def angularLeftMaterialDenominator (event : DressedEvent) : AngularParameters :=
  (angularJointPolynomial event.momentum event.frame).eval (MvPolynomial.C event.energy)
def angularRightMaterialDenominator (event : DressedEvent) : AngularParameters :=
  MvPolynomial.C ((SourcePropagationAlgebraicResponse.jointPolynomial event.momentum event.frame).eval event.energy)
def angularMaterialDenominator (event : DressedEvent) : AngularParameters :=
  (angularLeftMaterialDenominator event)^2*(angularRightMaterialDenominator event)^2
private theorem left_denominator_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    angularSpecialize n (angularLeftMaterialDenominator event)=leftMaterialDenominator event n := by
  rw [angularLeftMaterialDenominator,specialize_value,angular_joint_specialize,specialize_C]
  rfl
private theorem right_denominator_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    angularSpecialize n (angularRightMaterialDenominator event)=rightMaterialDenominator event := by
  rw [angularRightMaterialDenominator,specialize_C]
  rfl

def angularRightMaterialNumerator (event : DressedEvent) : AngularOp :=
  angularConstantOp (materialJointNumerator event.momentum event.frame event.energy)
def angularMaterialRaw (event : DressedEvent) (reader : Field289) : AngularOp :=
  (angularLeftMaterialDenominator event*angularRightMaterialDenominator event) •
    (angularMaterialLeft event*angularConstantOp (rawReader reader event.momentum event.frame 0)*angularRightMaterialNumerator event)
def angularMaterialContact (event : DressedEvent) (reader force : Field289) : AngularOp :=
  (angularLeftMaterialDenominator event*angularRightMaterialDenominator event) •
    (angularMaterialLeft event*angularConstantOp (fderiv ℝ (noetherReader reader event.momentum event.frame) 0 force)*angularRightMaterialNumerator event)
def angularMaterialFull (event : DressedEvent) (reader force : Field289) : AngularOp :=
  -(angularRightMaterialDenominator event) • (angularMaterialLeft event*angularLeftCurrent event event.energy force*
    angularMaterialLeft event*angularConstantOp (rawReader reader event.momentum event.frame 0)*angularRightMaterialNumerator event)-
  (angularLeftMaterialDenominator event) • (angularMaterialLeft event*angularConstantOp (rawReader reader event.momentum event.frame 0)*
    angularRightMaterialNumerator event*angularConstantOp (jointCurrent event.momentum event.frame event.energy 0 force)*angularRightMaterialNumerator event)

private theorem material_data_specialize (event : DressedEvent) (n : PhysicalMomentum) (reader force : Field289) :
    angularCoefficientSpecialize n (angularMaterialFull event reader force)=materialFullNumerator event n reader force ∧
    angularCoefficientSpecialize n (angularMaterialContact event reader force)=materialContactNumerator event n reader force ∧
    angularCoefficientSpecialize n (angularMaterialRaw event reader)=materialRawNumerator event n reader := by
  simp only [angularMaterialFull,angularMaterialContact,angularMaterialRaw,map_sub,angular_coefficient_smul,
    map_neg,map_mul,angular_material_left_specialize,angular_left_current_specialize,angularRightMaterialNumerator,
    angularConstantOp,angular_coefficient_constant,left_denominator_specialize,right_denominator_specialize,
    materialFullNumerator,materialContactNumerator,materialRawNumerator,rightMaterialNumerator,constantOp]
  trivial

def angularEvolution (event : DressedEvent) : Module.End AngularParameters AngularOp :=
  LinearMap.mul AngularParameters AngularOp ((MvPolynomial.C Complex.I : AngularParameters) • angularLeftGenerator event)+
    (LinearMap.mul AngularParameters AngularOp).flip
      ((MvPolynomial.C (-Complex.I) : AngularParameters) • angularConstantOp (jointGenerator event.momentum event.frame 0 0))
def angularDrive (event : DressedEvent) (force : Field289) : Module.End AngularParameters AngularOp :=
  -(LinearMap.mul AngularParameters AngularOp ((MvPolynomial.C (-Complex.I) : AngularParameters) • angularLeftCurrent event 0 force))+
    (LinearMap.mul AngularParameters AngularOp).flip
      ((MvPolynomial.C (-Complex.I) : AngularParameters) • angularConstantOp (jointCurrent event.momentum event.frame 0 0 force))
private theorem evolution_specialize (event : DressedEvent) (n : PhysicalMomentum) (B : AngularOp) :
    angularCoefficientSpecialize n (angularEvolution event B)=commonEvolution event n (angularCoefficientSpecialize n B) := by
  simp only [angularEvolution,commonEvolution,LinearMap.add_apply,LinearMap.mul_apply',LinearMap.flip_apply,
    map_add,map_mul,angular_coefficient_smul,specialize_C,angular_left_generator_specialize,
    angularConstantOp,angular_coefficient_constant,constantOp]
private theorem drive_specialize (event : DressedEvent) (n : PhysicalMomentum) (force : Field289) (B : AngularOp) :
    angularCoefficientSpecialize n (angularDrive event force B)=commonDrive event n force (angularCoefficientSpecialize n B) := by
  simp only [angularDrive,commonDrive,LinearMap.add_apply,LinearMap.neg_apply,LinearMap.mul_apply',LinearMap.flip_apply,
    map_add,map_neg,map_mul,angular_coefficient_smul,specialize_C,angular_left_current_specialize,
    angularConstantOp,angular_coefficient_constant,constantOp]

def angularClockAction (event : DressedEvent) (lambda : AngularParameters) : Module.End AngularParameters AngularOp :=
  aeval (angularEvolution event) ((angularClockPolynomial event)/ₘ(X-C lambda))
private theorem action_specialize (event : DressedEvent) (n : PhysicalMomentum) (lambda : AngularParameters) (B : AngularOp) :
    angularCoefficientSpecialize n (angularClockAction event lambda B)=
      commonClockAction event n (angularSpecialize n lambda) (angularCoefficientSpecialize n B) := by
  unfold angularClockAction commonClockAction
  have moved:=polynomial_action_natural (angularSpecialize n) (angularCoefficientSpecialize n).toAddMonoidHom
    (angular_coefficient_smul n) (angularEvolution event) (commonEvolution event n) (evolution_specialize event n)
    ((angularClockPolynomial event)/ₘ(X-C lambda)) B
  have polynomial : ((angularClockPolynomial event)/ₘ(X-C lambda)).map (angularSpecialize n)=
      (commonClockPolynomial event n)/ₘ(X-C (angularSpecialize n lambda)) := by
    rw [map_divByMonic _ (monic_X_sub_C _),angular_clock_specialize,Polynomial.map_sub,map_X,map_C]
  exact moved.trans (congrArg (fun P : Parameters[X] => aeval (commonEvolution event n) P
    (angularCoefficientSpecialize n B)) polynomial)

def angularDenominator (event : DressedEvent) : AngularParameters :=
  (angularClockPolynomial event).eval angularIRClock*(angularClockPolynomial event).eval (MvPolynomial.X 1)*angularMaterialDenominator event
def angularNumerator (event : DressedEvent) : Matrix (Fin 289) (Fin 289) AngularParameters := fun i j =>
  angularObserver (dressedEulerObserver event).toLinearMap
    ((angularClockPolynomial event).eval (MvPolynomial.X 1) •
      angularClockAction event angularIRClock (angularMaterialFull event (fieldUnit i) (fieldUnit j))+
    (angularClockPolynomial event).eval angularIRClock •
      angularClockAction event (MvPolynomial.X 1) (angularMaterialContact event (fieldUnit i) (fieldUnit j))+
    angularClockAction event (MvPolynomial.X 1)
      (angularDrive event (fieldUnit j) (angularClockAction event angularIRClock (angularMaterialRaw event (fieldUnit i)))))

theorem angular_denominator_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    angularSpecialize n (angularDenominator event)=commonDenominator event n := by
  simp only [angularDenominator,map_mul,specialize_value,angular_clock_specialize,specialize_clock,
    angularMaterialDenominator,map_pow,left_denominator_specialize,right_denominator_specialize]
  have one : angularSpecialize n (MvPolynomial.X (1 : Fin 6))=MvPolynomial.X (1 : Fin 3) := specialize_ir n 1
  rw [one]
  rfl

theorem angular_numerator_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    (angularNumerator event).map (angularSpecialize n)=commonNumerator event n := by
  funext i j
  rw [Matrix.map_apply,angularNumerator,angular_observer_specialize]
  have one : angularSpecialize n (MvPolynomial.X (1 : Fin 6))=MvPolynomial.X (1 : Fin 3) := specialize_ir n 1
  simp only [map_add,angular_coefficient_smul,specialize_value,angular_clock_specialize,specialize_clock,one,
    action_specialize,drive_specialize,(material_data_specialize event n (fieldUnit i) (fieldUnit j)).1,
    (material_data_specialize event n (fieldUnit i) (fieldUnit j)).2.1,
    (material_data_specialize event n (fieldUnit i) (fieldUnit j)).2.2]
  simp only [commonNumerator,map_add]

def angularIRMomentum : Fin 4→AngularParameters :=
  Fin.cases (-MvPolynomial.C Complex.I*(MvPolynomial.X 0)^2*MvPolynomial.X 2)
    (fun j => MvPolynomial.C Complex.I*(MvPolynomial.X 0)^2*MvPolynomial.X (Fin.natAdd 3 j))
private theorem angular_momentum_specialize (n : PhysicalMomentum) :
    (fun i => angularSpecialize n (angularIRMomentum i))=commonIRMomentum n := by
  have zero : angularSpecialize n (MvPolynomial.X (0 : Fin 6))=MvPolynomial.X (0 : Fin 3) := specialize_ir n 0
  have two : angularSpecialize n (MvPolynomial.X (2 : Fin 6))=MvPolynomial.X (2 : Fin 3) := specialize_ir n 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [angularIRMomentum,commonIRMomentum,Fin.cases_zero,map_mul,map_neg,map_pow]
    exact congrArg₂ (fun a b : Parameters => a*b)
      (congrArg₂ (fun a b : Parameters => a*b) (congrArg (fun a : Parameters => -a) (specialize_C n Complex.I))
        (congrArg (fun a : Parameters => a^2) zero)) two
  · simp only [angularIRMomentum,commonIRMomentum,Fin.cases_succ,map_mul,map_pow]
    have value : angularSpecialize n (MvPolynomial.X (Fin.natAdd 3 j))=MvPolynomial.C (n j : ℂ) := by
      simp only [angularSpecialize,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_X,Fin.addCases_right]
    exact congrArg₂ (fun a b : Parameters => a*b)
      (congrArg₂ (fun a b : Parameters => a*b) (specialize_C n Complex.I) (congrArg (fun a : Parameters => a^2) zero)) value

private def polynomialTerm {R : Type*} [CommRing R] (c : ℂ→+*R) (q : Fin 4→R) (a : SourceTerm) :
    Matrix (Fin 289) (Fin 289) R :=
  Matrix.single a.row a.column (c (coefficientValue a.coefficient)*
    q 0^a.powers.temporal*q 1^a.powers.first*q 2^a.powers.second*q 3^a.powers.third)
private theorem terms_specialize (terms : List SourceTerm) (n : PhysicalMomentum) (q : Fin 4→AngularParameters) :
    (terms.map (polynomialTerm MvPolynomial.C q)).sum.map (angularSpecialize n)=
      (terms.map (polynomialTerm MvPolynomial.C (fun i => angularSpecialize n (q i)))).sum := by
  induction terms with
  | nil => simp
  | cons a rest ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [Matrix.map_add _ (fun a b => (angularSpecialize n).map_add a b),ih]
    congr 1
    rw [polynomialTerm,Matrix.map_single]
    simp only [map_mul,map_pow,specialize_C]
    rfl

def angularJacobi : Matrix (Fin 289) (Fin 289) AngularParameters :=
  (originalJacobiTerms.map (polynomialTerm MvPolynomial.C angularIRMomentum)).sum

theorem angular_jacobi_specialize (n : PhysicalMomentum) :
    angularJacobi.map (angularSpecialize n)=commonJacobi n := by
  rw [angularJacobi,terms_specialize,angular_momentum_specialize]
  rfl

def angularClearedPencil (event : DressedEvent) : Matrix (Fin 289) (Fin 289) AngularParameters :=
  angularDenominator event • angularJacobi-(MvPolynomial.X 1 : AngularParameters) • angularNumerator event

theorem angular_pencil_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    (angularClearedPencil event).map (angularSpecialize n)=commonClearedPencil event n := by
  rw [angularClearedPencil,Matrix.map_sub _ (fun a b => (angularSpecialize n).map_sub a b),
    Matrix.map_smul' _ _ _ (fun a b => (angularSpecialize n).map_mul a b),
    Matrix.map_smul' _ _ _ (fun a b => (angularSpecialize n).map_mul a b),
    angular_denominator_specialize,angular_jacobi_specialize,angular_numerator_specialize]
  have one : angularSpecialize n (MvPolynomial.X (1 : Fin 6))=MvPolynomial.X (1 : Fin 3) := specialize_ir n 1
  rw [one]
  rfl

/-- The six-variable material/contact/drive expression clears the original complete halfline Pi. -/
theorem actual_angular_pi_clear (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) (positive : 0<sigma) :
    angularRealEval eps sigma s n (angularDenominator event) •
      frequencyHalfPolarization event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)=
      (angularNumerator event).map (angularRealEval eps sigma s n) := by
  have source:=actual_common_ir_pi_clear event n eps sigma s positive
  have denominator : angularRealEval eps sigma s n (angularDenominator event)=
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n) := by
    rw [angularRealEval,RingHom.comp_apply,angular_denominator_specialize]
  have mapped : (angularNumerator event).map (angularRealEval eps sigma s n)=
      (commonNumerator event n).map (MvPolynomial.eval (irValues eps sigma s)) := by
    rw [←angular_numerator_specialize]
    rfl
  rw [denominator,mapped]
  exact source

/-- All physical directions and the original frequency/IR parameters restrict one complete source polynomial pencil. -/
theorem actual_angular_pencil_clear (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) (positive : 0<sigma) :
    angularRealEval eps sigma s n (angularDenominator event) •
      frequencyResponsePencil event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
        (dampedFourierClock (sourceFrequency eps s) sigma)=
      (angularClearedPencil event).map (angularRealEval eps sigma s n) := by
  have source:=actual_common_ir_pencil_clear event n eps sigma s positive
  have denominator : angularRealEval eps sigma s n (angularDenominator event)=
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n) := by
    rw [angularRealEval,RingHom.comp_apply,angular_denominator_specialize]
  have mapped : (angularClearedPencil event).map (angularRealEval eps sigma s n)=
      (commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s)) := by
    rw [←angular_pencil_specialize]
    rfl
  rw [denominator,mapped]
  exact source

/-- Positive damping pays the six-variable source denominator for every actual real physical direction. -/
theorem actual_angular_denominator_nonzero (event : DressedEvent) (n : PhysicalMomentum)
    (eps sigma s : ℝ) (positive : 0<sigma) :
    angularRealEval eps sigma s n (angularDenominator event)≠0 := by
  rw [angularRealEval,RingHom.comp_apply,angular_denominator_specialize]
  exact ActualDressedUniformClockNonzero.actual_common_ir_denominator_nonzero event n eps sigma s positive

end LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
