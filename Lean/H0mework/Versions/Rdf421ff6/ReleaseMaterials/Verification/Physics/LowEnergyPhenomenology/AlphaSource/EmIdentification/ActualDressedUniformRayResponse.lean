import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedRayPolynomialCoefficients
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedPhysicalRayPencil
import Mathlib.Algebra.MvPolynomial.Eval

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformRayCoefficients
open Polynomial GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumPhysicalHalfAxis
open PreparationVacuumCurrentSignalOperator PreparationVacuumPropagationPencil
open SourcePropagationResolvent SourcePropagationAlgebraicResponse
open ActualDressedNoether ActualDressedFrequencyHalf ActualDressedFrequencyInverse ActualDressedFullCoulomb
open ActualDressedPhysicalRayNumerator PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open ActualEMAction PreparationVacuumActionFieldLift
open scoped Matrix
attribute [local irreducible] sourceInverse propagationPencil evolutionGenerator uniformClockPolynomial
  frequencyHalfPolarization dressedKinematicPoint dressedEulerObserver sourceMaterialMap sourceContactMap
  rawInitial driveOperator frequencyResponsePencil emOriginalJacobi

def uniformClockNumerator (q : PhysicalResponsePoint) (lambda : ℂ) : SourcePropagationResolvent.TransferOp :=
  aeval (evolutionGenerator q) ((uniformClockPolynomial q)/ₘ(X-C lambda))

attribute [local irreducible] uniformClockNumerator chargeClockPolynomial

private theorem annihilator_pencil {A : Type*} [Ring A] [Algebra ℂ A]
    (T : A) (P : ℂ[X]) (annihilated : aeval T P=0) (lambda : ℂ) :
    (algebraMap ℂ A lambda-T)*aeval T (P/ₘ(X-C lambda))=algebraMap ℂ A (P.eval lambda) := by
  have divide:=congrArg (aeval T) (modByMonic_add_div P (X-C lambda))
  rw [modByMonic_X_sub_C_eq_C_eval,map_add,map_mul,map_sub,aeval_C,aeval_X,aeval_C,annihilated] at divide
  apply sub_eq_zero.mp
  calc
    _= -(algebraMap ℂ A (P.eval lambda)+(T-algebraMap ℂ A lambda)*aeval T (P/ₘ(X-C lambda))) := by noncomm_ring
    _=0 := by rw [divide,neg_zero]

private theorem inverse_clear {A : Type*} [Ring A] [Algebra ℂ A]
    (U P N : A) (d : ℂ) (pencil : P*N=d • (1:A)) (inverse : U*P=1) : d • U=N := by
  have closed:=congrArg (fun B : A=>U*B) pencil
  rw [←mul_assoc,inverse,one_mul,mul_smul_comm,mul_one] at closed
  exact closed.symm

private theorem clm_inverse_clear {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T U : E→L[ℂ]E) (P : ℂ[X]) (lambda : ℂ) (annihilated : aeval T P=0)
    (inverse : U*(lambda • ContinuousLinearMap.id ℂ E-T)=1) :
    P.eval lambda • U=aeval T (P/ₘ(X-C lambda)) := by
  have generated:=annihilator_pencil T P annihilated lambda
  have pencil : (lambda • ContinuousLinearMap.id ℂ E-T)*aeval T (P/ₘ(X-C lambda))=
      P.eval lambda • (1:E→L[ℂ]E) := by
    simpa only [Algebra.algebraMap_eq_smul_one,ContinuousLinearMap.one_def] using generated
  exact inverse_clear _ _ _ _ pencil inverse

/-- The fixed-degree source annihilator clears the actual half-line inverse without a regularity witness. -/
theorem actual_uniform_source_inverse_clear (q : PhysicalResponsePoint) (lambda : ℂ)
    (positive : 0<lambda.re) :
    (uniformClockPolynomial q).eval lambda • sourceInverse q lambda=uniformClockNumerator q lambda := by
  have inverse:=sourceInverse_right q lambda positive
  unfold propagationPencil at inverse
  unfold uniformClockNumerator
  exact clm_inverse_clear (evolutionGenerator q) (sourceInverse q lambda) (uniformClockPolynomial q)
    lambda (actual_evolution_uniform_annihilated q) inverse

private theorem clear_two_clock {E : Type*} [AddCommGroup E] [Module ℂ E]
    (L R NL NR D : E→ₗ[ℂ]E) (M C B : E) (dl dr : ℂ)
    (left : dl • L=NL) (right : dr • R=NR) :
    (dl*dr) • (L M+R (C+D (L B)))=dr • NL M+dl • NR C+NR (D (NL B)) := by
  calc
    _=dr • (dl • L) M+dl • (dr • R) C+(dr • R) (D ((dl • L) B)) := by
      simp only [map_add,map_smul,LinearMap.smul_apply,smul_add,smul_smul]
      module
    _=_ := by rw [left,right]

def uniformTwoClockNumerator (event : DressedEvent) (transfer : PhysicalMomentum) (lambda delta : ℂ) :
    Matrix (Fin 289) (Fin 289) ℂ := fun i j=>
  let q:=dressedKinematicPoint event transfer
  dressedEulerObserver event
    (((uniformClockPolynomial q).eval delta) •
        uniformClockNumerator q lambda (sourceMaterialMap q (fieldUnit i) (fieldUnit j))+
      ((uniformClockPolynomial q).eval lambda) •
        uniformClockNumerator q delta (sourceContactMap q (fieldUnit i) (fieldUnit j))+
      uniformClockNumerator q delta
        (driveOperator q (fieldUnit j) (uniformClockNumerator q lambda (rawInitial q (fieldUnit i)))))

def uniformRayDenominator (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) : ℂ :=
  let P:=(chargeClockPolynomial event n).map (evalRingHom (e:ℂ))
  P.eval (dampedFourierClock (sourceFrequency e s) sigma)*P.eval (sigma:ℂ)

private def chargeCoefficientEmbedding : ℂ[X]→+*MvPolynomial (Fin 3) ℂ :=
  eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)

/-- One source polynomial in the independent charge, damping and sheet-frequency parameters. -/
def commonRayDenominatorPolynomial (event : DressedEvent) (n : PhysicalMomentum) : MvPolynomial (Fin 3) ℂ :=
  let P:=(chargeClockPolynomial event n).map chargeCoefficientEmbedding
  P.eval (MvPolynomial.X 1-MvPolynomial.C Complex.I*(MvPolynomial.X 0)^2*MvPolynomial.X 2)*
    P.eval (MvPolynomial.X 1)

theorem actual_common_ray_denominator_polynomial (event : DressedEvent) (n : PhysicalMomentum)
    (e sigma s : ℝ) :
    MvPolynomial.eval (fun i : Fin 3=>if i=0 then (e:ℂ) else if i=1 then (sigma:ℂ) else (s:ℂ))
      (commonRayDenominatorPolynomial event n)=uniformRayDenominator event e s sigma n := by
  let values : Fin 3→ℂ:=fun i=>if i=0 then (e:ℂ) else if i=1 then (sigma:ℂ) else (s:ℂ)
  let read:=MvPolynomial.eval values
  have hom : read.comp chargeCoefficientEmbedding=evalRingHom (e:ℂ) := by
    apply Polynomial.ringHom_ext
    · intro c; simp [read,chargeCoefficientEmbedding]
    · simp [read,chargeCoefficientEmbedding,values]
  have coefficients : ((chargeClockPolynomial event n).map chargeCoefficientEmbedding).map read=
      (chargeClockPolynomial event n).map (evalRingHom (e:ℂ)) := by rw [map_map,hom]
  change read _=_
  unfold commonRayDenominatorPolynomial uniformRayDenominator
  rw [map_mul,←eval_map_apply,←eval_map_apply,coefficients]
  simp [read,values,dampedFourierClock,sourceFrequency,Complex.ofReal_mul,Complex.ofReal_pow,mul_assoc]

def uniformRayNumerator (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  uniformTwoClockNumerator event ((e^2:ℝ) • n) (dampedFourierClock (sourceFrequency e s) sigma) (sigma:ℂ)

def uniformRayClearedPencil (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  uniformRayDenominator event e s sigma n • emOriginalJacobi (frequencyRay e s n)-
    (sigma:ℂ) • uniformRayNumerator event e s sigma n

attribute [local irreducible] uniformTwoClockNumerator uniformRayDenominator uniformRayNumerator uniformRayClearedPencil

private theorem observed_clear (q : PhysicalResponsePoint) (observer : (H→L[ℂ]H)→L[ℂ]ℂ)
    (lambda delta : ℂ) (positive : 0<lambda.re) (shifted : 0<delta.re)
    (M C B : H→L[ℂ]H) (D : SourcePropagationResolvent.TransferOp) :
    ((uniformClockPolynomial q).eval lambda*(uniformClockPolynomial q).eval delta)*observer
      (sourceInverse q lambda M+sourceInverse q delta (C+D (sourceInverse q lambda B)))=
    observer (((uniformClockPolynomial q).eval delta) • uniformClockNumerator q lambda M+
      ((uniformClockPolynomial q).eval lambda) • uniformClockNumerator q delta C+
      uniformClockNumerator q delta (D (uniformClockNumerator q lambda B))) := by
  have left:=congrArg ContinuousLinearMap.toLinearMap (actual_uniform_source_inverse_clear q lambda positive)
  have right:=congrArg ContinuousLinearMap.toLinearMap (actual_uniform_source_inverse_clear q delta shifted)
  have cleared:=clear_two_clock (sourceInverse q lambda).toLinearMap (sourceInverse q delta).toLinearMap
    (uniformClockNumerator q lambda).toLinearMap (uniformClockNumerator q delta).toLinearMap D.toLinearMap
    M C B ((uniformClockPolynomial q).eval lambda) ((uniformClockPolynomial q).eval delta) left right
  have observed:=congrArg observer cleared
  simpa only [map_smul,smul_eq_mul,ContinuousLinearMap.coe_coe] using observed

private theorem uniform_half_clear (event : DressedEvent) (transfer : PhysicalMomentum)
    (omega sigma : ℝ) (k : PhysicalMomentum) (positive : 0<sigma) :
    ((uniformClockPolynomial (dressedKinematicPoint event transfer)).eval (dampedFourierClock omega sigma)*
      (uniformClockPolynomial (dressedKinematicPoint event transfer)).eval (sigma:ℂ)) •
      frequencyHalfPolarization event transfer (physicalFrequencyMomentum omega k)
        (dampedFourierClock omega sigma)=uniformTwoClockNumerator event transfer (dampedFourierClock omega sigma) (sigma:ℂ) := by
  have damped : 0<(dampedFourierClock omega sigma).re := by
    simpa only [dampedFourierClock,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] using positive
  funext i j
  rw [Matrix.smul_apply,smul_eq_mul,damped_fourier_polarization_inverse event transfer omega sigma k positive i j]
  unfold uniformTwoClockNumerator
  exact observed_clear _ (dressedEulerObserver event) _ _ damped positive _ _ _ _

theorem actual_uniform_physical_ray_pi_clear (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) :
    uniformRayDenominator event e s sigma n •
      frequencyHalfPolarization event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma)=uniformRayNumerator event e s sigma n := by
  have frequency : sourceFrequency e s=s*e^2 := by unfold sourceFrequency;ring
  simpa only [uniformRayDenominator,actual_uniform_clock_charge_coefficients,uniformRayNumerator,
    frequency,frequencyRay] using
    uniform_half_clear event ((e^2:ℝ) • n) (sourceFrequency e s) sigma ((e^2:ℝ) • n) positive

/-- Full material, contact and driven response at the common physical ray, with source-polynomial coefficients. -/
theorem actual_uniform_physical_ray_pencil_clear (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) :
    uniformRayDenominator event e s sigma n •
      frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
        (dampedFourierClock (sourceFrequency e s) sigma)=uniformRayClearedPencil event e s sigma n := by
  rw [damped_source_sheet_response event e s sigma n positive,uniformRayClearedPencil,smul_sub]
  congr 1
  rw [smul_comm,actual_uniform_physical_ray_pi_clear event e s sigma n positive]

/-- A computable source polynomial condition; it contains no corrected inverse or realization premise. -/
def uniformRayRegular (event : DressedEvent) (e s sigma : ℝ) (n : PhysicalMomentum) : Prop :=
  uniformRayDenominator event e s sigma n≠0

theorem actual_uniform_physical_ray_equation_iff (event : DressedEvent) (e s sigma : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (regular : uniformRayRegular event e s sigma n)
    (forcing a : Fin 289→ℂ) :
    frequencyResponsePencil event ((e^2:ℝ) • n) (frequencyRay e s n)
      (dampedFourierClock (sourceFrequency e s) sigma)*ᵥa=forcing ↔
      uniformRayClearedPencil event e s sigma n*ᵥa=uniformRayDenominator event e s sigma n • forcing := by
  rw [←actual_uniform_physical_ray_pencil_clear event e s sigma n positive,Matrix.smul_mulVec]
  exact (smul_right_injective _ regular).eq_iff.symm

end LowEnergy.GaussComposite.ActualDressedUniformRayCoefficients
