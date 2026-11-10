import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedFourierInverse
import H0mework.Versions.R9c73a630.Physics.LowEnergy.AlphaSource.CanonicalSourcePropagationPreparedMeromorphicResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedPhysicalRayNumerator
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalHalfAxis SourcePropagationResolvent SourcePropagationNoetherTime
open PreparationVacuumCurrentSignalOperator PreparationVacuumPropagationPencil
open PreparationVacuumPhysicalCharacteristic
open SourcePropagationAlgebraicResponse ActualDressedFrequencyHalf ActualDressedFrequencyInverse
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedHistoryKernel ActualDressedClockMoment
open scoped Matrix Topology
attribute [local irreducible] sourceInverse propagationNumerator propagationPolynomial polynomialResolvent
  dressedEulerObserver dressedKinematicPoint sourceMaterialMap sourceContactMap rawInitial driveOperator
  frequencyHalfPolarization dampedFourierClock physicalFrequencyMomentum

def twoClockDenominator (q : PhysicalResponsePoint) (lambda delta : ℂ) : ℂ :=
  (propagationPolynomial q).eval lambda*(propagationPolynomial q).eval delta

def twoClockNumerator (event : DressedEvent) (transfer : PhysicalMomentum) (lambda delta : ℂ) :
    Matrix (Fin 289) (Fin 289) ℂ := fun i j=>
  let q:=dressedKinematicPoint event transfer
  dressedEulerObserver event
    (((propagationPolynomial q).eval delta) •
        propagationNumerator q lambda (sourceMaterialMap q (fieldUnit i) (fieldUnit j))+
      ((propagationPolynomial q).eval lambda) •
        propagationNumerator q delta (sourceContactMap q (fieldUnit i) (fieldUnit j))+
      propagationNumerator q delta
        (driveOperator q (fieldUnit j) (propagationNumerator q lambda (rawInitial q (fieldUnit i)))))

attribute [local irreducible] twoClockDenominator twoClockNumerator

private theorem clear_linear_two_clock {E : Type*} [AddCommGroup E] [Module ℂ E]
    (observer : E→ₗ[ℂ]ℂ) (L R D : E→ₗ[ℂ]E) (M C B : E) (dl dr : ℂ)
    (left : dl≠0) (right : dr≠0) :
    (dl*dr)*observer (dl⁻¹ • L M+dr⁻¹ • R (C+D (dl⁻¹ • L B)))=
      observer (dr • L M+dl • R C+R (D (L B))) := by
  simp only [map_add,map_smul]
  calc
    _=(dl*dl⁻¹)*(dr*observer (L M))+(dl*dl⁻¹)*(dr*dr⁻¹)*observer (R (D (L B)))+
        (dr*dr⁻¹)*(dl*observer (R C)) := by ring
    _=_ := by rw [mul_inv_cancel₀ left,mul_inv_cancel₀ right];ring

theorem two_clock_denominator_nonzero (q : PhysicalResponsePoint) (lambda delta : ℂ)
    (positive : 0<lambda.re) (shifted : 0<delta.re) : twoClockDenominator q lambda delta≠0 := by
  unfold twoClockDenominator
  exact mul_ne_zero (propagationPolynomial_offAxis q lambda positive.ne')
    (propagationPolynomial_offAxis q delta shifted.ne')

private theorem observed_source_two_clock_clear (q : PhysicalResponsePoint)
    (observer : (H→L[ℂ]H)→L[ℂ]ℂ) (lambda delta : ℂ) (positive : 0<lambda.re) (shifted : 0<delta.re)
    (M C B : H→L[ℂ]H) (D : SourcePropagationResolvent.TransferOp) :
    twoClockDenominator q lambda delta*observer
      (sourceInverse q lambda M+sourceInverse q delta (C+D (sourceInverse q lambda B)))=
    observer (((propagationPolynomial q).eval delta) • propagationNumerator q lambda M+
      ((propagationPolynomial q).eval lambda) • propagationNumerator q delta C+
      propagationNumerator q delta (D (propagationNumerator q lambda B))) := by
  have left : sourceInverse q lambda=((propagationPolynomial q).eval lambda)⁻¹ • propagationNumerator q lambda := by
    simpa only [polynomialResolvent] using (polynomialResolvent_future q lambda positive).symm
  have right : sourceInverse q delta=((propagationPolynomial q).eval delta)⁻¹ • propagationNumerator q delta := by
    simpa only [polynomialResolvent] using (polynomialResolvent_future q delta shifted).symm
  have lifted:=congrArg₂ (fun L R : SourcePropagationResolvent.TransferOp=>
    twoClockDenominator q lambda delta*observer (L M+R (C+D (L B)))) left right
  refine lifted.trans ?_
  simpa only [twoClockDenominator,smul_apply,ContinuousLinearMap.coe_coe] using clear_linear_two_clock (E:=H→L[ℂ]H) observer.toLinearMap
    (propagationNumerator q lambda).toLinearMap (propagationNumerator q delta).toLinearMap D.toLinearMap
    M C B ((propagationPolynomial q).eval lambda) ((propagationPolynomial q).eval delta)
    (propagationPolynomial_offAxis q lambda positive.ne') (propagationPolynomial_offAxis q delta shifted.ne')

theorem actual_two_clock_clear (event : DressedEvent) (transfer : PhysicalMomentum)
    (omega sigma : ℝ) (k : PhysicalMomentum) (positive : 0<sigma) :
    twoClockDenominator (dressedKinematicPoint event transfer) (dampedFourierClock omega sigma) (sigma:ℂ) •
      frequencyHalfPolarization event transfer (physicalFrequencyMomentum omega k)
        (dampedFourierClock omega sigma)=
      twoClockNumerator event transfer (dampedFourierClock omega sigma) (sigma:ℂ) := by
  have damped : 0<(dampedFourierClock omega sigma).re := by
    simpa only [dampedFourierClock,Complex.sub_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] using positive
  funext i j
  rw [Matrix.smul_apply,smul_eq_mul,damped_fourier_polarization_inverse event transfer omega sigma k positive i j]
  unfold twoClockNumerator
  exact observed_source_two_clock_clear (dressedKinematicPoint event transfer) (dressedEulerObserver event)
    (dampedFourierClock omega sigma) (sigma:ℂ) damped positive _ _ _ _

end LowEnergy.GaussComposite.ActualDressedPhysicalRayNumerator
