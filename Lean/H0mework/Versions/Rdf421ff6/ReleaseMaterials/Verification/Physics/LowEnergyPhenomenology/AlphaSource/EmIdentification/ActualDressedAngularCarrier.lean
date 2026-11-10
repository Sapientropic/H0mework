import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCommonIRSourceOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
open Polynomial GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open ActualDressedUniformRayCoefficients ActualDressedUniformMaterialCoefficients
open scoped Matrix BigOperators

abbrev AngularParameters := MvPolynomial (Fin 6) ℂ

def angularSpecialize (n : PhysicalMomentum) : AngularParameters→+*Parameters :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    (Fin.addCases (motive := fun _ => Parameters) (fun i : Fin 3 => MvPolynomial.X i) (fun i : Fin 3 => MvPolynomial.C (n i : ℂ)))

private theorem affine_add {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : PhysicalMomentum→E) (law : ∀(p n : PhysicalMomentum) (r : ℝ),f (p-r • n)=f p-(r : ℂ) • (f n-f 0)) (p k : PhysicalMomentum) :
    f (p+k)-f 0=(f p-f 0)+(f k-f 0) := by
  have endpoint : p+k-(1 : ℝ) • k=p := by module
  have paid:=law (p+k) k 1
  rw [endpoint,Complex.ofReal_one,one_smul] at paid
  rw [paid]
  abel

private theorem affine_smul {E : Type*} [AddCommGroup E] [Module ℂ E]
    (f : PhysicalMomentum→E) (law : ∀(p n : PhysicalMomentum) (r : ℝ),f (p-r • n)=f p-(r : ℂ) • (f n-f 0)) (p : PhysicalMomentum) (r : ℝ) :
    f (r • p)-f 0=(r : ℂ) • (f p-f 0) := by
  have endpoint : (0 : PhysicalMomentum)-(-r) • p=r • p := by module
  have paid:=law 0 p (-r)
  rw [endpoint,Complex.ofReal_neg,neg_smul,sub_neg_eq_add] at paid
  rw [paid,add_sub_cancel_left]

/-- This real linear map is generated from the paid full source compression germ on the fixed carrier. -/
def carrierMomentum (F : GaussUnitaryHistory.Index) :
    PhysicalMomentum→ₗ[ℝ]Module.End ℂ (compressionCarrier F) where
  toFun := fun n => sourceCompressionEnd n F-sourceCompressionEnd 0 F
  map_add' := fun p k => affine_add (fun n => sourceCompressionEnd n F)
    (fun p n r => source_carrier_affine p n F r) p k
  map_smul' := fun r p => (affine_smul (fun n => sourceCompressionEnd n F)
    (fun p n r => source_carrier_affine p n F r) p r).trans
      (RCLike.real_smul_eq_coe_smul (K:=ℂ) r _).symm

def carrierMomentumMatrix (F : GaussUnitaryHistory.Index) : PhysicalMomentum→ₗ[ℝ]
    Matrix (Fin (Module.finrank ℂ (compressionCarrier F))) (Fin (Module.finrank ℂ (compressionCarrier F))) ℂ :=
  ((LinearMap.toMatrix (Module.finBasis ℂ (compressionCarrier F))
    (Module.finBasis ℂ (compressionCarrier F))).toLinearMap.restrictScalars ℝ).comp (carrierMomentum F)

theorem carrier_momentum_matrix (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    carrierMomentumMatrix F n=sourceCarrierMatrix n F-sourceCarrierMatrix 0 F := by
  simp only [carrierMomentumMatrix,LinearMap.comp_apply,LinearMap.restrictScalars_apply,
    LinearEquiv.coe_toLinearMap,carrierMomentum,LinearMap.coe_mk,AddHom.coe_mk,map_sub,sourceCarrierMatrix]

private theorem coordinates {E : Type*} [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
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

private theorem matrix_coordinates (d : ℕ) (L : (Fin 3→ℝ)→ₗ[ℝ]Matrix (Fin d) (Fin d) ℂ) (n : Fin 3→ℝ) :
    L n=∑j : Fin 3,(n j : ℂ) • L (Pi.single j 1) := coordinates L n

attribute [local irreducible] sourceCarrierMatrix carrierMomentumMatrix

theorem carrier_coordinates (F : GaussUnitaryHistory.Index) (n : PhysicalMomentum) :
    sourceCarrierMatrix n F-sourceCarrierMatrix 0 F=
      ∑j : Fin 3,(n j : ℂ) • (sourceCarrierMatrix (Pi.single j 1) F-sourceCarrierMatrix 0 F) := by
  have generated:=matrix_coordinates _ (carrierMomentumMatrix F) n
  refine (carrier_momentum_matrix F n).symm.trans (generated.trans ?_)
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun M => (n j : ℂ) • M) (carrier_momentum_matrix F (Pi.single j 1))

/-- Direction variables are coefficients of the original source matrix, not interpolation samples. -/
def angularCompressionMatrix (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Matrix (Fin (Module.finrank ℂ (compressionCarrier F))) (Fin (Module.finrank ℂ (compressionCarrier F))) AngularParameters :=
  fun i k => MvPolynomial.C (sourceCarrierMatrix p F i k)-
    (MvPolynomial.X (0 : Fin 6))^2*(∑j : Fin 3,MvPolynomial.X (Fin.natAdd 3 j)*
      MvPolynomial.C ((sourceCarrierMatrix (Pi.single j 1) F-sourceCarrierMatrix 0 F) i k))

theorem angular_compression_specialize (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (angularCompressionMatrix p F).map (angularSpecialize n)=
      (chargeCompressionMatrix p n F).map irCoefficientMap := by
  funext i k
  have coordinates:=congrFun (congrFun (carrier_coordinates F n) i) k
  change sourceCarrierMatrix n F i k-sourceCarrierMatrix 0 F i k=
    ∑j : Fin 3,(n j : ℂ)*((sourceCarrierMatrix (Pi.single j 1) F-sourceCarrierMatrix 0 F) i k) at coordinates
  simp only [Matrix.map_apply,angularCompressionMatrix,angularSpecialize,map_sub,map_pow,map_mul,map_sum,
    chargeCompressionMatrix]
  simp only [MvPolynomial.coe_eval₂Hom,MvPolynomial.eval₂_C,MvPolynomial.eval₂_X,
    Fin.addCases_right,irCoefficientMap,coe_eval₂RingHom,eval₂_C,eval₂_X]
  have fixed:=congrArg (MvPolynomial.C : ℂ→Parameters) coordinates
  simp only [map_sub,map_sum,map_mul] at fixed
  rw [←fixed]
  have zero : Fin.addCases (motive := fun _ => Parameters) (fun i : Fin 3 => MvPolynomial.X i)
    (fun i : Fin 3 => MvPolynomial.C (n i : ℂ)) (0 : Fin 6)=MvPolynomial.X (0 : Fin 3) := rfl
  rw [zero]
  ring

def angularJointPolynomial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : AngularParameters[X] :=
  ((angularCompressionMatrix p F).charpoly*X)^57

theorem angular_joint_monic (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (angularJointPolynomial p F).Monic := ((Matrix.charpoly_monic _).mul monic_X).pow _

/-- Every direction specialization returns the original common joint source polynomial on its same fixed carrier. -/
theorem angular_joint_specialize (event : ActualDressedFullCoulomb.DressedEvent) (n : PhysicalMomentum) :
    (angularJointPolynomial event.momentum event.frame).map (angularSpecialize n)=commonJointPolynomial event n := by
  rw [angularJointPolynomial,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_X,←Matrix.charpoly_map,angular_compression_specialize,
    Matrix.charpoly_map]
  simp only [commonJointPolynomial,chargeJointPolynomial,Polynomial.map_pow,Polynomial.map_mul,Polynomial.map_X]

end LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
