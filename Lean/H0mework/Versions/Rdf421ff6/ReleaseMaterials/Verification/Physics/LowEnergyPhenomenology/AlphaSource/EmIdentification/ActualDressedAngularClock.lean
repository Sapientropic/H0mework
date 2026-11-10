import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedAngularCarrier

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedUniformRayCoefficients
open ActualDressedUniformMaterialCoefficients ActualDressedPhysicalRayNumerator SourcePropagationAlgebraicResponse ActualDressedNoether
open scoped Matrix

private def clockEntries {R : Type*} [CommRing R] (d : ℕ) (P Q : R[X]) (imag : R) :
    Matrix (Fin d×Fin d) (Fin d×Fin d) R :=
  fun i j => imag*(X^(j.1.val+1)%ₘP).coeff i.1.val*(if i.2=j.2 then 1 else 0)+
    (-imag)*(if i.1=j.1 then 1 else 0)*(X^(j.2.val+1)%ₘQ).coeff i.2.val

private theorem clock_entries_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R→+*S) (d : ℕ) (P Q : R[X]) (hP : P.Monic) (hQ : Q.Monic) (imag : R) :
    (clockEntries d P Q imag).map f=clockEntries d (P.map f) (Q.map f) (f imag) := by
  funext i j
  simp only [Matrix.map_apply,clockEntries,map_add,map_mul,map_neg,apply_ite,map_one,map_zero]
  have left:=congrArg (fun T : S[X] => T.coeff i.1.val)
    (map_modByMonic (p:=X^(j.1.val+1)) f hP)
  have right:=congrArg (fun T : S[X] => T.coeff i.2.val)
    (map_modByMonic (p:=X^(j.2.val+1)) f hQ)
  simp only [coeff_map,Polynomial.map_pow,map_X] at left right
  rw [left,right]

def angularClockMatrix (event : DressedEvent) :
    Matrix (Fin (sourceClockDegree event.frame)×Fin (sourceClockDegree event.frame))
      (Fin (sourceClockDegree event.frame)×Fin (sourceClockDegree event.frame)) AngularParameters :=
  clockEntries (sourceClockDegree event.frame) (angularJointPolynomial event.momentum event.frame)
    ((jointPolynomial event.momentum event.frame).map MvPolynomial.C) (MvPolynomial.C Complex.I)

def angularClockPolynomial (event : DressedEvent) : AngularParameters[X] :=
  (angularClockMatrix event).charpoly

/-- Both power bases have the original fixed source degree; every angular specialization returns the same complete clock polynomial. -/
theorem angular_clock_specialize (event : DressedEvent) (n : PhysicalMomentum) :
    (angularClockPolynomial event).map (angularSpecialize n)=commonClockPolynomial event n := by
  rw [angularClockPolynomial,←Matrix.charpoly_map]
  have constant : (angularSpecialize n).comp (MvPolynomial.C : ℂ→+*AngularParameters)=MvPolynomial.C := by
    ext c
    simp only [RingHom.comp_apply,angularSpecialize,MvPolynomial.eval₂Hom_C]
  have oldConstant : irCoefficientMap.comp (C : ℂ→+*ℂ[X])=MvPolynomial.C := by
    ext c
    simp only [RingHom.comp_apply,irCoefficientMap,coe_eval₂RingHom,eval₂_C]
  have mapped : (angularClockMatrix event).map (angularSpecialize n)=
      clockEntries (sourceClockDegree event.frame) (commonJointPolynomial event n)
        ((jointPolynomial event.momentum event.frame).map MvPolynomial.C) (MvPolynomial.C Complex.I) := by
    rw [angularClockMatrix,clock_entries_map _ _ _ _ (angular_joint_monic _ _) ((jointPolynomial_monic _ _).map _),
      angular_joint_specialize]
    rw [Polynomial.map_map,constant]
    simp only [angularSpecialize,MvPolynomial.eval₂Hom_C]
  have old : (chargeClockMatrix event n).map irCoefficientMap=
      clockEntries (sourceClockDegree event.frame) (commonJointPolynomial event n)
        ((jointPolynomial event.momentum event.frame).map MvPolynomial.C) (MvPolynomial.C Complex.I) := by
    change (clockEntries (sourceClockDegree event.frame) (chargeJointPolynomial event.momentum n event.frame)
      (fixedJointPolynomial event.momentum event.frame) (C Complex.I)).map irCoefficientMap=_
    have monic : (fixedJointPolynomial event.momentum event.frame).Monic :=
      (jointPolynomial_monic _ _).map C
    rw [clock_entries_map irCoefficientMap _ _ _ (charge_joint_monic _ _ _) monic]
    rw [fixedJointPolynomial,Polynomial.map_map,oldConstant]
    simp only [commonJointPolynomial,irCoefficientMap,coe_eval₂RingHom,eval₂_C]
  rw [mapped,←old,Matrix.charpoly_map]
  rfl

theorem angular_clock_degree (event : DressedEvent) :
    (angularClockPolynomial event).natDegree=(sourceClockDegree event.frame)^2 := by
  rw [angularClockPolynomial,Matrix.charpoly_natDegree_eq_dim,Fintype.card_prod,Fintype.card_fin,pow_two]

def angularRealEval (eps sigma s : ℝ) (n : PhysicalMomentum) : AngularParameters→+*ℂ :=
  (MvPolynomial.eval (irValues eps sigma s)).comp (angularSpecialize n)

theorem actual_angular_joint_coefficients (event : DressedEvent) (eps sigma s : ℝ) (n : PhysicalMomentum) :
    (angularJointPolynomial event.momentum event.frame).map (angularRealEval eps sigma s n)=
      jointPolynomial (event.momentum-(eps^2 : ℝ) • n) event.frame := by
  rw [angularRealEval,←Polynomial.map_map,angular_joint_specialize,common_joint_polynomial_eval]

theorem actual_angular_clock_coefficients (event : DressedEvent) (eps sigma s : ℝ) (n : PhysicalMomentum) :
    (angularClockPolynomial event).map (angularRealEval eps sigma s n)=
      uniformClockPolynomial (dressedKinematicPoint event ((eps^2 : ℝ) • n)) := by
  rw [angularRealEval,←Polynomial.map_map,angular_clock_specialize,common_clock_polynomial_eval]

end LowEnergy.GaussComposite.ActualDressedAngularSourceCoefficients
