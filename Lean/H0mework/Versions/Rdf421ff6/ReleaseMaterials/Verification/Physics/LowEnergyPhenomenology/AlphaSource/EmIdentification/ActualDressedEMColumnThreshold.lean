import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMClockColumns

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMZeroClockColumns
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalFeedback ActualDressedFullCoulomb ActualDressedCorrectedGreen
open ActualDressedCorrectedElectronRead ActualDressedUniformMaterialCoefficients
open LowEnergy.GaussComposite.ActualDressedVisiblePole LowEnergy.ActualDressedVisiblePole
open ActualDressedEMTensorClock ActualDressedOrderedStatic ActualDressedZeroClockFrequency
open ActualDressedZeroClockVector ActualEMCurrentSplit ActualEMCarrierOwn ActualEMResponseSplit
open ActualDressedFrequencyHalf Filter Set
open scoped Topology Matrix BigOperators
attribute [local irreducible] commonClearedPencil commonDenominator commonDeterminant
  commonEMSourceColumn emInsertion correctedGreen frequencyResponsePencil

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

theorem actual_zero_clock_em_threshold_equation (event : DressedEvent) (eps : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4)
    (balanced : PencilClockBalanced event eps n) (finite : EMColumnsClockFinite event eps n) :
    zeroClockPencil event eps n*ᵥzeroClockEMColumn event eps n nu=
      zeroClockFrequencyDenominator event eps n • (zeroClockClearing event eps n •
        fun i => Polynomial.C (emInsertion i nu)) :=
  leading_equation _ _ _ _ _ _ _ (actual_full_clock_em_column_equation event eps n nu)
    balanced (finite nu) (source_frequency_clock_factor event eps n) (source_clearing_clock_factor event eps n)

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
  simp only [clockSpecialize,Polynomial.coe_mapRingHom,Polynomial.map_pow,Polynomial.map_X,
    eval_mul,eval_pow,eval_X,Pi.div_apply]
  exact (mul_div_mul_left _ _ nonzero).symm

def zeroClockEMColumnRead (event : DressedEvent) (eps s : ℝ) (n : PhysicalMomentum) (nu : Fin 4) :
    Fin 289 → ℂ :=
  fun i => (zeroClockEMColumnFraction event eps n nu i).num.eval (s : ℂ)/
    (zeroClockEMColumnFraction event eps n nu i).denom.eval (s : ℂ)

private theorem evaluated_em_column (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (i : Fin 289) :
    MvPolynomial.eval (irValues eps sigma s) (commonEMSourceColumn event n nu i)=
      MvPolynomial.eval (irValues eps sigma s) (commonDenominator event n)*
        (((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate*ᵥ
          fun j => emInsertion j nu) i := by
  have mapped : (commonClearedPencil event n).adjugate.map (MvPolynomial.eval (irValues eps sigma s))=
      ((commonClearedPencil event n).map (MvPolynomial.eval (irValues eps sigma s))).adjugate :=
    (MvPolynomial.eval (irValues eps sigma s)).map_adjugate (commonClearedPencil event n)
  unfold commonEMSourceColumn
  rw [← mapped]
  simp only [Pi.smul_apply,smul_eq_mul,Matrix.mulVec,dotProduct,map_mul,map_sum,
    Matrix.map_apply,MvPolynomial.eval_C]

theorem actual_corrected_em_column_clock_fraction (event : DressedEvent) (eps sigma s : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4) (positive : 0<sigma)
    (regular : correctedDet event eps s sigma n≠0) (i : Fin 289) :
    correctedEMColumn event eps s sigma n nu i=
      (clockSpecialize s (fullClockEMColumn event eps n nu i)).eval (sigma : ℂ)/
        (clockSpecialize s (frequencyClockDeterminant event eps n)).eval (sigma : ℂ) := by
  have determinant := actual_common_determinant_nonzero event eps sigma s n positive regular
  have vector := congrArg (fun M : Matrix (Fin 289) (Fin 289) ℂ => M*ᵥfun j => emInsertion j nu)
    (actual_common_green_adjugate event eps sigma s n positive regular)
  rw [Matrix.smul_mulVec,Matrix.smul_mulVec] at vector
  rw [fullClockEMColumn,frequency_clock_specialize,frequencyClockDeterminant,
    frequency_clock_specialize,frequency_damping_eval,frequency_damping_eval]
  rw [evaluated_em_column]
  apply (eq_div_iff determinant).mpr
  exact (mul_comm _ _).trans (congrFun vector i)

/-- All coordinates of each actual Green column return before any EM compression. -/
theorem actual_zero_clock_em_column (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (nu : Fin 4)
    (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (finite : EMColumnsClockFinite event eps n) :
    Tendsto (fun sigma : ℝ => correctedEMColumn event eps s sigma n nu)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroClockEMColumnRead event eps s n nu)) := by
  apply tendsto_pi_nhds.2
  intro i
  have base := factored_ratio_limit (fullClockEMColumn event eps n nu i)
    (frequencyClockDeterminant event eps n) (frequencyClockOrder event eps n) s
    (finite nu i) (source_frequency_clock_factor event eps n) regular
  have value := reduced_read_at_regular (zeroClockEMColumn event eps n nu i)
    (zeroClockFrequencyDenominator event eps n) (s : ℂ) regular
  dsimp only [zeroClockEMColumn,zeroClockFrequencyDenominator] at value
  rw [← value] at base
  apply Tendsto.congr' _ base
  filter_upwards [source_zero_clock_frequency_chart event eps n s regular] with sigma chart
  exact (actual_corrected_em_column_clock_fraction event eps sigma s n nu chart.1 chart.2 i).symm

theorem actual_corrected_em_column_tensor (event : DressedEvent) (eps s sigma : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4) :
    dotProduct (fun i => emInsertion i mu) (correctedEMColumn event eps s sigma n nu)=
      correctedEMTensor event eps s sigma n mu nu := by
  unfold correctedEMColumn correctedEMTensor emResponseTensor
  rw [Matrix.mul_assoc]
  rfl

/-- The existing sigma-first EM16 response is consumed by the same actual four-column return. -/
theorem actual_zero_clock_em_column_tensor (event : DressedEvent) (eps s : ℝ)
    (n : PhysicalMomentum) (mu nu : Fin 4)
    (regular : (zeroClockFrequencyDenominator event eps n).eval (s : ℂ)≠0)
    (finite : EMColumnsClockFinite event eps n) :
    dotProduct (fun i => emInsertion i mu) (zeroClockEMColumnRead event eps s n nu)=
      zeroClockFrequencyEMRead event eps s n mu nu := by
  have continuous : Continuous (fun v : Fin 289 → ℂ => dotProduct (fun i => emInsertion i mu) v) := by
    unfold dotProduct
    fun_prop
  have limit := (continuous.tendsto _).comp (actual_zero_clock_em_column event eps s n nu regular finite)
  simp only [Function.comp_def,actual_corrected_em_column_tensor] at limit
  exact tendsto_nhds_unique limit
    (actual_zero_clock_frequency_em_entry event eps s n mu nu regular
      (source_em_columns_pay_tensor_factors event eps n finite mu nu))

end LowEnergy.GaussComposite.ActualDressedEMZeroClockColumns
