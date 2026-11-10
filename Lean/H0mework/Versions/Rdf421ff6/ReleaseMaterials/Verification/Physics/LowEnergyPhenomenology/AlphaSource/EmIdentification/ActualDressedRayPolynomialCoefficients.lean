import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedCanonicalClockMatrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformRayCoefficients
open Polynomial GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource
open SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open PreparationVacuumGradedTransport PreparationVacuumPhysicalFeedback ActualDressedNoether ActualDressedFullCoulomb ActualDressedPhysicalRayNumerator
open scoped Matrix
local instance : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] compression physicalFrame GaussCoreHilbert.coreEquiv

/-- The basis belongs to the fixed source carrier F; it never depends on momentum or charge. -/
def sourceCarrierMatrix (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Matrix (Fin (Module.finrank ℂ (compressionCarrier F))) (Fin (Module.finrank ℂ (compressionCarrier F))) ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ (compressionCarrier F))
    (Module.finBasis ℂ (compressionCarrier F)) (sourceCompressionEnd p F)

private theorem affine_difference {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A B C D : E) (r : ℂ) (linear : D-C= -r • (B-C)) :
    A+D-C=A-r • (B-C) := by
  calc
    _=A+(D-C) := by abel
    _=A+(-r) • (B-C) := by rw [linear]
    _=_ := by rw [neg_smul,←sub_eq_add_neg]

theorem source_compression_affine (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) :
    compression (p-r • n) F=compression p F-(r:ℂ) • (compression n F-compression 0 F) := by
  have linear:=momentumCompression_smul (-r) n F
  change compression ((-r) • n) F-compression 0 F=
    (-r) • (compression n F-compression 0 F) at linear
  have cast := RCLike.real_smul_eq_coe_smul (K:=ℂ) (E:=H→L[ℂ]H) (-r) (compression n F-compression 0 F)
  have linearC := (linear.trans cast).trans
    (congrArg (fun c : ℂ=>c • (compression n F-compression 0 F)) (Complex.ofReal_neg r))
  have endpoint : p-r • n=p+(-r) • n := by rw [sub_eq_add_neg,neg_smul]
  have affine:=compression_affine p ((-r) • n) F
  have original := (congrArg (fun k=>compression k F) endpoint).trans
    (affine.trans (affine_difference (compression p F) (compression n F) (compression 0 F)
      (compression ((-r) • n) F) (r:ℂ) linearC))
  exact original

theorem source_carrier_affine (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) :
    sourceCompressionEnd (p-r • n) F=
      sourceCompressionEnd p F-(r:ℂ) • (sourceCompressionEnd n F-sourceCompressionEnd 0 F) := by
  have original:=source_compression_affine p n F r
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change compression (p-r • n) F x=(compression p F-(r:ℂ) • (compression n F-compression 0 F)) x
  exact congrArg (fun A : H→L[ℂ]H=>A x) original

private theorem shifted_difference {E : Type*} [AddCommGroup E] (C A Z B : E) :
    (C-B)+A-Z=(C+A-Z)-B := by abel

/-- Both physical Hamiltonian endpoints use the same uncut A(0), before any clock numerator is read. -/
theorem actual_joint_charge_affine (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (r : ℝ) :
    PreparationVacuumJointFieldResponse.jointGenerator (p-r • n) F 0 0=
      PreparationVacuumJointFieldResponse.jointGenerator p F 0 0-
        (r:ℂ) • (compression n F-compression 0 F) := by
  let A:=PreparationVacuumPhysicalHalfAxis.actualA 0 F
  let Z:=(0:ℂ) • (1:H→L[ℂ]H)
  let B:=(r:ℂ) • (compression n F-compression 0 F)
  have compressionStep:=congrArg (fun C : H→L[ℂ]H=>C+A-Z) (source_compression_affine p n F r)
  exact (jointGenerator_base (p-r • n) F 0).trans (compressionStep.trans
    ((shifted_difference (compression p F) A Z B).trans
      (congrArg (fun J : H→L[ℂ]H=>J-B) (jointGenerator_base p F 0).symm)))

def chargeCompressionMatrix (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Matrix (Fin (Module.finrank ℂ (compressionCarrier F))) (Fin (Module.finrank ℂ (compressionCarrier F))) ℂ[X] :=
  fun i j=>C (sourceCarrierMatrix p F i j)-C (sourceCarrierMatrix n F i j-sourceCarrierMatrix 0 F i j)*X^2

private theorem matrix_affine {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (b : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E)
    (A B C : Module.End ℂ E) (r : ℂ) :
    LinearMap.toMatrix b b (A-r • (B-C))=
      LinearMap.toMatrix b b A-r • (LinearMap.toMatrix b b B-LinearMap.toMatrix b b C) := by
  rw [map_sub,map_smul,map_sub]

theorem charge_matrix_eval (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (e : ℝ) :
    (chargeCompressionMatrix p n F).map (evalRingHom (e:ℂ))=sourceCarrierMatrix (p-(e^2:ℝ) • n) F := by
  let b:=Module.finBasis ℂ (compressionCarrier F)
  have original:=congrArg (LinearMap.toMatrix b b) (source_carrier_affine p n F (e^2))
  have matrices : sourceCarrierMatrix (p-(e^2:ℝ) • n) F=
      sourceCarrierMatrix p F-((e^2:ℝ):ℂ) • (sourceCarrierMatrix n F-sourceCarrierMatrix 0 F) :=
    original.trans (matrix_affine b (sourceCompressionEnd p F) (sourceCompressionEnd n F)
      (sourceCompressionEnd 0 F) ((e^2:ℝ):ℂ))
  apply Eq.trans _ matrices.symm
  funext i j
  change (evalRingHom (e:ℂ)) (C _-C _*X^2)=_-((e^2:ℝ):ℂ)*(_-_)
  simp only [coe_evalRingHom,eval_sub,eval_mul,eval_C,eval_pow,eval_X,Complex.ofReal_pow]
  ring

def chargeJointPolynomial (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : Polynomial ℂ[X] :=
  ((chargeCompressionMatrix p n F).charpoly*X)^57

def fixedJointPolynomial (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) : Polynomial ℂ[X] :=
  (jointPolynomial p F).map C

theorem charge_joint_monic (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (chargeJointPolynomial p n F).Monic :=
  ((Matrix.charpoly_monic _).mul monic_X).pow _

theorem charge_joint_eval (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (e : ℝ) :
    (chargeJointPolynomial p n F).map (evalRingHom (e:ℂ))=jointPolynomial (p-(e^2:ℝ) • n) F := by
  rw [chargeJointPolynomial,Polynomial.map_pow,Polynomial.map_mul,map_X,←Matrix.charpoly_map,charge_matrix_eval]
  unfold jointPolynomial compressionPolynomial sourceCarrierMatrix
  rw [LinearMap.charpoly_toMatrix]

def sourceClockDegree (F : GaussUnitaryHistory.Index) : ℕ :=
  57*(Module.finrank ℂ (compressionCarrier F)+1)

theorem joint_degree_source (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    (jointPolynomial p F).natDegree=sourceClockDegree F := by
  rw [jointPolynomial,natDegree_pow,compressionPolynomial,natDegree_mul_X (LinearMap.charpoly_monic _).ne_zero,
    LinearMap.charpoly_natDegree]
  rfl

private def clockEntries {R : Type*} [CommRing R] (d : ℕ) (P Q : R[X]) (imag : R) :
    Matrix (Fin d×Fin d) (Fin d×Fin d) R :=
  fun i j=>imag*(X^(j.1.val+1)%ₘP).coeff i.1.val*(if i.2=j.2 then 1 else 0)+
    (-imag)*(if i.1=j.1 then 1 else 0)*(X^(j.2.val+1)%ₘQ).coeff i.2.val

private theorem clock_entries_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (d : ℕ) (P Q : R[X]) (hP : P.Monic) (hQ : Q.Monic) (imag : R) :
    (clockEntries d P Q imag).map f=clockEntries d (P.map f) (Q.map f) (f imag) := by
  funext i j
  simp only [Matrix.map_apply,clockEntries,map_add,map_mul,map_neg,apply_ite,map_one,map_zero]
  have left:=congrArg (fun T : S[X]=>T.coeff i.1.val)
    (map_modByMonic (p:=X^(j.1.val+1)) f hP)
  have right:=congrArg (fun T : S[X]=>T.coeff i.2.val)
    (map_modByMonic (p:=X^(j.2.val+1)) f hQ)
  simp only [coeff_map,Polynomial.map_pow,map_X] at left right
  rw [left,right]

private theorem clock_charpoly_fixed (P Q : ℂ[X]) (d : ℕ)
    (hP : P.natDegree=d) (hQ : Q.natDegree=d) :
    (canonicalClockMatrix P Q).charpoly=(clockEntries d P Q Complex.I).charpoly := by
  let e:=Equiv.prodCongr (finCongr hP) (finCongr hQ)
  have matrix : Matrix.reindex e e (canonicalClockMatrix P Q)=clockEntries d P Q Complex.I := by
    ext i j
    simp [Matrix.reindex_apply,e,canonicalClockMatrix,canonicalCompanion,clockEntries,Fin.ext_iff]
  rw [←matrix,Matrix.charpoly_reindex]

/-- A polynomial matrix on the two canonical clock power bases, with a charge-independent index type. -/
def chargeClockMatrix (event : DressedEvent) (n : PhysicalMomentum) :
    Matrix (Fin (sourceClockDegree event.frame)×Fin (sourceClockDegree event.frame))
      (Fin (sourceClockDegree event.frame)×Fin (sourceClockDegree event.frame)) ℂ[X] :=
  clockEntries (sourceClockDegree event.frame)
    (chargeJointPolynomial event.momentum n event.frame)
    (fixedJointPolynomial event.momentum event.frame) (C Complex.I)

def chargeClockPolynomial (event : DressedEvent) (n : PhysicalMomentum) : Polynomial ℂ[X] :=
  (chargeClockMatrix event n).charpoly

theorem actual_uniform_clock_charge_coefficients (event : DressedEvent) (n : PhysicalMomentum) (e : ℝ) :
    (chargeClockPolynomial event n).map (evalRingHom (e:ℂ))=
      uniformClockPolynomial (dressedKinematicPoint event ((e^2:ℝ) • n)) := by
  rw [chargeClockPolynomial,←Matrix.charpoly_map]
  have mapped : (chargeClockMatrix event n).map (evalRingHom (e:ℂ))=
      clockEntries (sourceClockDegree event.frame)
        (jointPolynomial (event.momentum-(e^2:ℝ) • n) event.frame)
        (jointPolynomial event.momentum event.frame) Complex.I := by
    rw [chargeClockMatrix,fixedJointPolynomial,clock_entries_map _ _ _ _ (charge_joint_monic _ _ _) ((jointPolynomial_monic _ _).map C),
      charge_joint_eval]
    simp [map_map,evalRingHom,eval₂RingHom_comp_C]
  rw [mapped,actual_uniform_clock_canonical_matrix]
  change _=(canonicalClockMatrix (jointPolynomial (event.momentum+ -((e^2:ℝ) • n)) event.frame)
    (jointPolynomial event.momentum event.frame)).charpoly
  rw [←sub_eq_add_neg]
  exact (clock_charpoly_fixed _ _ _ (joint_degree_source _ _) (joint_degree_source _ _)).symm

theorem charge_clock_fixed_degree (event : DressedEvent) (n : PhysicalMomentum) :
    (chargeClockPolynomial event n).natDegree=(sourceClockDegree event.frame)^2 := by
  rw [chargeClockPolynomial,Matrix.charpoly_natDegree_eq_dim,Fintype.card_prod,Fintype.card_fin,pow_two]

end LowEnergy.GaussComposite.ActualDressedUniformRayCoefficients
