import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularClock

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
abbrev SourceOp := GaussCoreHilbert.H→L[ℂ]GaussCoreHilbert.H
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedUniformRayCoefficients
open ActualDressedUniformMaterialCoefficients SourcePropagationCommonMomentum
open PreparationVacuumJointFieldResponse ActualEMJointCurrentMomentum GaussCoreHilbert
open scoped TensorProduct BigOperators

abbrev AngularCoefficients (A : Type*) [AddCommGroup A] [Module ℂ A] := AngularParameters⊗[ℂ]A

def angularSpecializeAlg (n : PhysicalMomentum) : AngularParameters→ₐ[ℂ]Parameters where
  toRingHom := angularSpecialize n
  commutes' := fun c => by simp [angularSpecialize]

def angularCoefficientSpecialize {A : Type*} [Ring A] [Algebra ℂ A] (n : PhysicalMomentum) :
    AngularCoefficients A→ₐ[ℂ]CoefficientAlgebra A :=
  Algebra.TensorProduct.map (angularSpecializeAlg n) (AlgHom.id ℂ A)

theorem angular_coefficient_constant {A : Type*} [Ring A] [Algebra ℂ A]
    (n : PhysicalMomentum) (B : A) :
    angularCoefficientSpecialize n (Algebra.TensorProduct.includeRight B : AngularCoefficients A)=
      (Algebra.TensorProduct.includeRight B : CoefficientAlgebra A) := by
  exact AlgHom.congr_fun (Algebra.TensorProduct.map_comp_includeRight (angularSpecializeAlg n) (AlgHom.id ℂ A)) B

theorem angular_coefficient_scalar {A : Type*} [Ring A] [Algebra ℂ A]
    (n : PhysicalMomentum) (P : AngularParameters) :
    angularCoefficientSpecialize n (algebraMap AngularParameters (AngularCoefficients A) P)=
      algebraMap Parameters (CoefficientAlgebra A) (angularSpecialize n P) := by
  simp only [Algebra.TensorProduct.algebraMap_def]
  exact RingHom.congr_fun (Algebra.TensorProduct.map_comp_includeLeftRingHom
    (angularSpecializeAlg n) (AlgHom.id ℂ A)) P

theorem angular_coefficient_smul {A : Type*} [Ring A] [Algebra ℂ A]
    (n : PhysicalMomentum) (P : AngularParameters) (B : AngularCoefficients A) :
    angularCoefficientSpecialize n (P • B)=angularSpecialize n P • angularCoefficientSpecialize n B := by
  have normalized:=congrArg (angularCoefficientSpecialize (A:=A) n) (Algebra.smul_def P B)
  calc
    _=angularCoefficientSpecialize n (algebraMap AngularParameters (AngularCoefficients A) P*B) := normalized
    _=angularCoefficientSpecialize n (algebraMap AngularParameters (AngularCoefficients A) P)*angularCoefficientSpecialize n B :=
      (angularCoefficientSpecialize n).map_mul _ _
    _=_ := by rw [angular_coefficient_scalar];exact (Algebra.smul_def _ _).symm


theorem angular_coefficient_aeval {A : Type*} [Ring A] [Algebra ℂ A]
    (n : PhysicalMomentum) (T : AngularCoefficients A) (P : AngularParameters[X]) :
    angularCoefficientSpecialize n (aeval T P)=
      aeval (angularCoefficientSpecialize n T) (P.map (angularSpecialize n)) := by
  have hom : (angularCoefficientSpecialize (A:=A) n).toRingHom.comp
      (algebraMap AngularParameters (AngularCoefficients A))=
      (algebraMap Parameters (CoefficientAlgebra A)).comp (angularSpecialize n) :=
    RingHom.ext (angular_coefficient_scalar n)
  have mapped:=hom_eval₂ (p:=P) (f:=algebraMap AngularParameters (AngularCoefficients A))
    (g:=(angularCoefficientSpecialize n).toRingHom) T
  rw [hom] at mapped
  simpa only [aeval_def,eval₂_map,AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom] using mapped

private theorem direction_coordinates {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
    (L : (Fin 3→ℝ)→ₗ[ℝ]E) (n : Fin 3→ℝ) :
    L n=∑j : Fin 3,(n j : ℂ) • L (Pi.single j 1) := by
  have basis : (∑j : Fin 3,n j • Pi.single j (1 : ℝ))=n := by
    ext i
    simp only [Finset.sum_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul]
    simp
  conv_lhs => rw [←basis,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  rfl

/-- This uses the differentiated full-field current source, including its momentum-dependent left leg. -/
theorem actual_current_direction_coordinates (F : GaussUnitaryHistory.Index) (z : ℂ)
    (n : PhysicalMomentum) (force : Field289) :
    jointCurrent n F z 0 force-jointCurrent 0 F z 0 force=
      ∑j : Fin 3,(n j : ℂ) • (jointCurrent (Pi.single j 1) F z 0 force-jointCurrent 0 F z 0 force) := by
  let L : PhysicalMomentum→L[ℝ]SourceOp := (ContinuousLinearMap.apply ℝ SourceOp force).comp (jointCurrentMomentum F z)
  have same (p : PhysicalMomentum) : L p=jointCurrent p F z 0 force-jointCurrent 0 F z 0 force := by
    change (jointCurrent p F z 0-jointCurrent 0 F z 0) force=_
    rfl
  have generated:=direction_coordinates L.toLinearMap n
  simpa only [ContinuousLinearMap.coe_coe,same] using generated

theorem actual_generator_direction_coordinates (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    momentumCompression n F=∑j : Fin 3,(n j : ℂ) • momentumCompression (Pi.single j 1) F := by
  have generated:=direction_coordinates (momentumCompressionMap F).toLinearMap n
  exact generated

private theorem constant_smul {A : Type*} [Ring A] [Algebra ℂ A] (c : ℂ) (B : A) :
    (MvPolynomial.C c : Parameters) • (Algebra.TensorProduct.includeRight B : CoefficientAlgebra A)=
      Algebra.TensorProduct.includeRight (c • B) := by
  rw [←MvPolynomial.algebraMap_eq,algebraMap_smul]
  exact ((Algebra.TensorProduct.includeRight : A→ₐ[ℂ]CoefficientAlgebra A).toLinearMap.map_smul c B).symm

def angularDirection {A : Type*} [Ring A] [Algebra ℂ A] (B : Fin 3→A) : AngularCoefficients A :=
  ∑j : Fin 3,(MvPolynomial.X (Fin.natAdd 3 j) : AngularParameters) •
    (Algebra.TensorProduct.includeRight (B j) : AngularCoefficients A)

private theorem direction_specialize {A : Type*} [Ring A] [Algebra ℂ A] (n : PhysicalMomentum) (B : Fin 3→A) :
    angularCoefficientSpecialize n (angularDirection B)=
      (Algebra.TensorProduct.includeRight (∑j : Fin 3,(n j : ℂ) • B j) : CoefficientAlgebra A) := by
  simp only [angularDirection,map_sum,angular_coefficient_smul,angular_coefficient_constant]
  have value (j : Fin 3) : angularSpecialize n (MvPolynomial.X (Fin.natAdd 3 j))=MvPolynomial.C (n j : ℂ) := by
    simp only [angularSpecialize,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_X,Fin.addCases_right]
  simp only [value,constant_smul]

abbrev AngularOp := AngularCoefficients SourceOp
@[instance_reducible] private def coefficientRing {A : Type*} [Ring A] [Algebra ℂ A] :
    Ring (AngularCoefficients A) := inferInstance
local instance : Ring AngularOp := coefficientRing (A:=SourceOp)
local instance : AddCommGroup AngularOp := (inferInstance : Ring AngularOp).toAddCommGroup
local instance : AddGroup AngularOp := (inferInstance : AddCommGroup AngularOp).toAddGroup
local instance : NormedAlgebra ℝ SourceOp := NormedAlgebra.restrictScalars ℝ ℂ _

def angularConstantOp (B : SourceOp) : AngularOp := Algebra.TensorProduct.includeRight B

def angularLeftGenerator (event : DressedEvent) : AngularOp :=
  angularConstantOp (jointGenerator event.momentum event.frame 0 0)-
    ((MvPolynomial.X (0 : Fin 6) : AngularParameters)^2) •
      angularDirection (fun j => momentumCompression (Pi.single j 1) event.frame)

def angularLeftCurrent (event : DressedEvent) (z : ℂ) (force : Field289) : AngularOp :=
  angularConstantOp (jointCurrent event.momentum event.frame z 0 force)-
    ((MvPolynomial.X (0 : Fin 6) : AngularParameters)^2) •
      angularDirection (fun j => jointCurrent (Pi.single j 1) event.frame z 0 force-jointCurrent 0 event.frame z 0 force)

private theorem ir_zero_specialize (n : PhysicalMomentum) :
    angularSpecialize n (MvPolynomial.X (0 : Fin 6))=MvPolynomial.X (0 : Fin 3) := by
  simp only [angularSpecialize,MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_X]
  rfl

private theorem affine_direction_specialize {A : Type*} [Ring A] [Algebra ℂ A]
    (n : PhysicalMomentum) (U V : A) (B : Fin 3→A) (paid : V=∑j : Fin 3,(n j : ℂ) • B j) :
    angularCoefficientSpecialize n ((Algebra.TensorProduct.includeRight U : AngularCoefficients A)-
      ((MvPolynomial.X (0 : Fin 6) : AngularParameters)^2) • angularDirection B)=
    (Algebra.TensorProduct.includeRight U : CoefficientAlgebra A)-
      ((MvPolynomial.X (0 : Fin 3) : Parameters)^2) • Algebra.TensorProduct.includeRight V := by
  simp only [map_sub,angular_coefficient_constant,angular_coefficient_smul,map_pow,ir_zero_specialize,direction_specialize]
  exact congrArg (fun W : CoefficientAlgebra A => Algebra.TensorProduct.includeRight U-
      ((MvPolynomial.X (0 : Fin 3) : Parameters)^2) • W)
    (congrArg (Algebra.TensorProduct.includeRight : A→ₐ[ℂ]CoefficientAlgebra A) paid.symm)

attribute [local irreducible] jointGenerator jointCurrent momentumCompression

theorem angular_left_generator_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    angularCoefficientSpecialize n (angularLeftGenerator event)=commonLeftGenerator event n := by
  unfold angularLeftGenerator commonLeftGenerator angularConstantOp constantOp
  exact affine_direction_specialize (A:=SourceOp) n (jointGenerator event.momentum event.frame 0 0)
    (momentumCompression n event.frame) (fun j => momentumCompression (Pi.single j 1) event.frame)
    (actual_generator_direction_coordinates event.frame n)

theorem angular_left_current_specialize (event : DressedEvent) (n : PhysicalMomentum) (z : ℂ) (force : Field289) :
    angularCoefficientSpecialize n (angularLeftCurrent event z force)=commonLeftCurrent event n z force := by
  unfold angularLeftCurrent commonLeftCurrent angularConstantOp constantOp
  exact affine_direction_specialize (A:=SourceOp) n (jointCurrent event.momentum event.frame z 0 force)
    (jointCurrent n event.frame z 0 force-jointCurrent 0 event.frame z 0 force)
    (fun j => jointCurrent (Pi.single j 1) event.frame z 0 force-jointCurrent 0 event.frame z 0 force)
    (actual_current_direction_coordinates event.frame z n force)

def angularMaterialLeft (event : DressedEvent) : AngularOp :=
  -(aeval (angularLeftGenerator event)
    ((angularJointPolynomial event.momentum event.frame)/ₘ(X-C (MvPolynomial.C event.energy))))

private theorem negative_polynomial_specialize {A : Type*} [Ring A] [Algebra ℂ A]
    (n : PhysicalMomentum) (T : AngularCoefficients A) (S : CoefficientAlgebra A)
    (P : AngularParameters[X]) (Q : Parameters[X]) (z : ℂ)
    (operator : angularCoefficientSpecialize n T=S) (polynomial : P.map (angularSpecialize n)=Q) :
    angularCoefficientSpecialize n (-(aeval T (P/ₘ(X-C (MvPolynomial.C z)))))=
      -(aeval S (Q/ₘ(X-C (MvPolynomial.C z)))) := by
  have denominator : ((P/ₘ(X-C (MvPolynomial.C z))).map (angularSpecialize n))=Q/ₘ(X-C (MvPolynomial.C z)) := by
    rw [map_divByMonic _ (monic_X_sub_C _),polynomial,Polynomial.map_sub,map_X,map_C]
    simp only [angularSpecialize,MvPolynomial.eval₂Hom_C]
  have first:=angular_coefficient_aeval (A:=A) n T (P/ₘ(X-C (MvPolynomial.C z)))
  have second:=congrArg₂ (fun U : CoefficientAlgebra A => fun R : Parameters[X] => aeval U R) operator denominator
  exact ((angularCoefficientSpecialize n).map_neg _).trans (congrArg (fun x : CoefficientAlgebra A => -x) (first.trans second))

theorem angular_material_left_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    angularCoefficientSpecialize n (angularMaterialLeft event)=commonMaterialLeft event n := by
  unfold angularMaterialLeft commonMaterialLeft
  exact negative_polynomial_specialize n _ _ _ _ event.energy
    (angular_left_generator_specialize event n) (angular_joint_specialize event n)

end LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
