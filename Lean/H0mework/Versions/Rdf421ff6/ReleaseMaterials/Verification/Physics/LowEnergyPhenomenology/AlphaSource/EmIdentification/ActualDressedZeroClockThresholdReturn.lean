import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedZeroClockVectorSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedZeroClockVector
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open LowEnergy.GaussComposite.ActualDressedPoleWardMode LowEnergy.ActualDressedPoleWardMode
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualCompositeFieldCurrent ActualDressedFrequencyHalf Filter Set
open scoped Topology
open scoped Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant sourceCommonVector

private theorem factor_product_coefficient {R : Type*} [CommRing R]
    (P Q : R[X]) (a b : ℕ) (pFactor : X^a∣P) (qFactor : X^b∣Q) :
    (P*Q).coeff (a+b)=P.coeff a*Q.coeff b := by
  obtain ⟨p,rfl⟩ := pFactor
  obtain ⟨q,rfl⟩ := qFactor
  have product : (X^a*p)*(X^b*q)=X^(a+b)*(p*q) := by rw [pow_add];ring
  have cp : (X^a*p).coeff a=p.coeff 0 := by simpa only [zero_add] using coeff_X_pow_mul p a 0
  have cq : (X^b*q).coeff b=q.coeff 0 := by simpa only [zero_add] using coeff_X_pow_mul q b 0
  rw [product,cp,cq]
  simpa only [zero_add] using (coeff_X_pow_mul (p*q) (a+b) 0).trans (mul_coeff_zero p q)

private theorem leading_equation {ι : Type*} [Fintype ι]
    (H : Matrix ι ι (ℂ[X])[X]) (V : ι → (ℂ[X])[X]) (D d : (ℂ[X])[X])
    (fs : ι → ℂ) (m b : ℕ)
    (paid : H*ᵥV=D • (d • fun i => Polynomial.C (Polynomial.C (fs i))))
    (hFactor : ∀i j, X^b∣H i j) (vFactor : ∀i, X^m∣V i)
    (dFactor : X^m∣D) (clearingFactor : X^b∣d) :
    (fun i j => (H i j).coeff b)*ᵥ(fun i => (V i).coeff m)=
      D.coeff m • (d.coeff b • fun i => Polynomial.C (fs i)) := by
  funext i
  have coefficient := congrArg (fun P : (ℂ[X])[X] => P.coeff (m+b)) (congrFun paid i)
  simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,← mul_assoc,
    finsetSum_coeff,coeff_mul_C] at coefficient
  have each (j : ι) : (H i j*V j).coeff (m+b)=(H i j).coeff b*(V j).coeff m := by
    simpa only [Nat.add_comm] using factor_product_coefficient _ _ b m (hFactor i j) (vFactor j)
  simp only [each,factor_product_coefficient D d m b dFactor clearingFactor] at coefficient
  simp only [Matrix.mulVec,dotProduct,Pi.smul_apply,smul_eq_mul,← mul_assoc]
  exact coefficient

theorem source_clearing_clock_factor (event : DressedEvent) (eps : ℝ) (n : PhysicalMomentum) :
    X^clearingClockOrder event eps n∣fullClockClearing event eps n :=
  X_pow_dvd_iff.mpr (fun _ less => coeff_eq_zero_of_lt_natTrailingDegree less)

/-- Both source checks are paid before turning the coefficient module into a threshold pencil equation. -/
theorem actual_zero_clock_threshold_equation (event : DressedEvent) (eps : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg)
    (balanced : PencilClockBalanced event eps n) (finite : FullVectorClockFinite event eps n ps sL sR) :
    zeroClockPencil event eps n*ᵥzeroClockSourceVector event eps n ps sL sR=
      zeroClockFrequencyDenominator event eps n • (zeroClockClearing event eps n •
        fun i => Polynomial.C (ActualCompositeFieldCurrent.compositeCurrent ps sL sR i)) :=
  leading_equation _ _ _ _ _ _ _ (actual_full_clock_equation event eps n ps sL sR)
    balanced finite (source_frequency_clock_factor event eps n) (source_clearing_clock_factor event eps n)

private theorem coefficient_after_factor (Q : (ℂ[X])[X]) (m : ℕ) (s : ℝ) :
    (clockSpecialize s Q).eval 0=((X^m*Q).coeff m).eval (s : ℂ) := by
  have coefficient : (X^m*Q).coeff m=Q.coeff 0 := by
    simpa only [zero_add] using coeff_X_pow_mul Q m 0
  rw [coefficient,← coeff_zero_eq_eval_zero]
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,coeff_map]
  rfl

private theorem factored_ratio_limit (N D : (ℂ[X])[X]) (m : ℕ) (s : ℝ)
    (nFactor : X^m∣N) (dFactor : X^m∣D) (regular : (D.coeff m).eval (s : ℂ)≠0) :
    Tendsto (fun sigma : ℝ => (clockSpecialize s N).eval (sigma : ℂ)/
      (clockSpecialize s D).eval (sigma : ℂ)) (nhdsWithin 0 (Ioi 0))
      (𝓝 ((N.coeff m).eval (s : ℂ)/(D.coeff m).eval (s : ℂ))) := by
  obtain ⟨Nq,nEq⟩ := nFactor
  obtain ⟨Dq,dEq⟩ := dFactor
  have nValue := coefficient_after_factor Nq m s
  have dValue := coefficient_after_factor Dq m s
  rw [← nEq] at nValue
  rw [← dEq] at dValue
  have qRegular : (clockSpecialize s Dq).eval 0≠0 := by rw [dValue];exact regular
  have cn : Continuous (fun sigma : ℝ => (clockSpecialize s Nq).eval (sigma : ℂ)) := by fun_prop
  have cd : Continuous (fun sigma : ℝ => (clockSpecialize s Dq).eval (sigma : ℂ)) := by fun_prop
  have base := (cn.continuousAt.div cd.continuousAt qRegular).tendsto.mono_left
    (show nhdsWithin (0 : ℝ) (Ioi 0)≤𝓝 0 from inf_le_left)
  simp only [Pi.div_apply,Complex.ofReal_zero] at base
  rw [nValue,dValue] at base
  apply Tendsto.congr' _ base
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  have nonzero : (sigma : ℂ)^m≠0 := pow_ne_zero m (Complex.ofReal_ne_zero.mpr (ne_of_gt positive))
  rw [nEq,dEq,map_mul,map_mul]
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_pow,Polynomial.map_X,eval_mul,eval_pow,eval_X,Pi.div_apply]
  exact (mul_div_mul_left _ _ nonzero).symm

def zeroClockVectorRead (event : DressedEvent) (eps s : ℝ) (n ps : PhysicalMomentum)
    (sL sR : CompositeLeg) : Fin 289 → ℂ :=
  fun i => (zeroClockVectorFraction event eps n ps sL sR i).num.eval (s : ℂ)/
    (zeroClockVectorFraction event eps n ps sL sR i).denom.eval (s : ℂ)

def zeroClockThresholdPencil (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) :
    Matrix (Fin 289) (Fin 289) ℂ :=
  fun i j => (zeroClockPencil event eps n i j).eval (s : ℂ)/(zeroClockClearing event eps n).eval (s : ℂ)

private theorem evaluated_source_vector (event : DressedEvent) (eps sigma s : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg) (i : Fin 289) :
    MvPolynomial.eval (irValues eps sigma s) (sourceCommonVector event n ps sL sR i)=
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n)*
        (((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate*ᵥ
          ActualCompositeFieldCurrent.compositeCurrent ps sL sR) i := by
  have mapped : (commonClearedPencil event n).adjugate.map (MvPolynomial.eval (irValues eps sigma s))=
      ((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate :=
    (MvPolynomial.eval (irValues eps sigma s)).map_adjugate (commonClearedPencil event n)
  unfold sourceCommonVector
  rw [← mapped]
  simp only [Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,map_mul,map_sum,
    Matrix.map_apply,MvPolynomial.eval_C]

theorem actual_corrected_vector_clock_fraction (event : DressedEvent) (eps sigma s : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg) (positive : 0<sigma)
    (regular : correctedDet event eps s sigma n≠0) (i : Fin 289) :
    correctedProbeResponse event eps s sigma n ps sL sR i=
      (clockSpecialize s (fullClockSourceVector event eps n ps sL sR i)).eval (sigma : ℂ)/
        (clockSpecialize s (frequencyClockDeterminant event eps n)).eval (sigma : ℂ) := by
  have determinant := actual_common_determinant_nonzero event eps sigma s n positive regular
  have vector := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ =>
    M*ᵥActualCompositeFieldCurrent.compositeCurrent ps sL sR)
      (actual_common_green_adjugate event eps sigma s n positive regular)
  rw [Matrix.smul_mulVec,Matrix.smul_mulVec] at vector
  rw [fullClockSourceVector,frequency_clock_specialize,frequencyClockDeterminant,
    frequency_clock_specialize,frequency_damping_eval,frequency_damping_eval]
  rw [evaluated_source_vector,corrected_probe_response_original]
  apply (eq_div_iff determinant).mpr
  exact (mul_comm _ _).trans (congrFun vector i)

/-- Complete coordinate limits are paid from the original adjugate response, not reconstructed from an EM reader. -/
theorem actual_zero_clock_full_vector (event : DressedEvent) (eps s : ℝ)
    (n ps : PhysicalMomentum) (sL sR : CompositeLeg)
    (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (finite : FullVectorClockFinite event eps n ps sL sR) :
    Tendsto (fun sigma : ℝ => correctedProbeResponse event eps s sigma n ps sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockVectorRead event eps s n ps sL sR)) := by
  apply tendsto_pi_nhds.2
  intro i
  have base := factored_ratio_limit (fullClockSourceVector event eps n ps sL sR i)
    (frequencyClockDeterminant event eps n) (frequencyClockOrder event eps n) s
    (finite i) (source_frequency_clock_factor event eps n) regular
  have value := reduced_read_at_regular (zeroClockSourceVector event eps n ps sL sR i)
    (zeroClockFrequencyDenominator event eps n) (s : ℂ) regular
  dsimp only [zeroClockSourceVector,zeroClockFrequencyDenominator] at value
  rw [← value] at base
  apply Tendsto.congr' _ base
  filter_upwards [source_zero_clock_frequency_chart event eps n s regular] with sigma chart
  exact (actual_corrected_vector_clock_fraction event eps sigma s n ps sL sR chart.1 chart.2 i).symm

theorem actual_pencil_clock_fraction (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (positive : 0<sigma) (i j : Fin 289) :
    frequencyResponsePencil event ((eps^2 : ℝ) • n) (frequencyRay eps s n)
      (dampedFourierClock (sourceFrequency eps s) sigma) i j=
      (clockSpecialize s (fullClockPencil event eps n i j)).eval (sigma : ℂ)/
        (clockSpecialize s (fullClockClearing event eps n)).eval (sigma : ℂ) := by
  have denominator := ActualDressedUniformClockNonzero.actual_common_ir_denominator_nonzero event n eps sigma s positive
  have paid := congrFun (congrFun (actual_common_ir_pencil_clear event n eps sigma s positive) i) j
  have raw : frequencyResponsePencil event ((eps^2 : ℝ) • n)
      (frequencyRay eps s n) (dampedFourierClock (sourceFrequency eps s) sigma) i j=
      MvPolynomial.eval (irValues eps sigma s) (commonClearedPencil event n i j)/
        MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n) := by
    apply (eq_div_iff denominator).mpr
    exact (mul_comm _ _).trans paid
  rw [fullClockPencil,Matrix.map_apply,frequency_clock_specialize,fullClockClearing,
    frequency_clock_specialize,frequency_damping_eval,frequency_damping_eval]
  exact raw

/-- Clock-balanced leading H/d is the actual original P limit; no cleared zero matrix is named a physical kernel. -/
theorem actual_zero_clock_threshold_pencil (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (regular : (zeroClockClearing event eps n).eval (s : ℂ)≠0)
    (balanced : PencilClockBalanced event eps n) :
    Tendsto (fun sigma : ℝ => frequencyResponsePencil event ((eps^2 : ℝ) • n)
      (frequencyRay eps s n) (dampedFourierClock (sourceFrequency eps s) sigma))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockThresholdPencil event eps s n)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  have base := factored_ratio_limit (fullClockPencil event eps n i j)
    (fullClockClearing event eps n) (clearingClockOrder event eps n) s
    (balanced i j) (source_clearing_clock_factor event eps n) regular
  apply Tendsto.congr' _ base
  filter_upwards [self_mem_nhdsWithin] with sigma positive
  exact (actual_pencil_clock_fraction event eps sigma s n positive i j).symm

end LowEnergy.GaussComposite.ActualDressedZeroClockVector
