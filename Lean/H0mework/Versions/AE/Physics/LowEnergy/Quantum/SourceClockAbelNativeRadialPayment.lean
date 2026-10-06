import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockAbelNativeCurvature
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeJointPayment
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeRadialContraction
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockAbelNativeRadialPayment
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm
open GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussFockWeights GaussDensityCore GaussLiveMomentum
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumScalarChart SourceQuantumFockGauge
open SourceCoframeVolume SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff
open SourceClockYukawaCubicCurrent SourceScalarDoubleCurrent SourceRelativePowerTail
open SourceClockPhiSecondPressure SourceScalarInverseNativeEnergy SourceClockReflectedForm SourceScalarPairedTransport
open FullYSourceResolventGraphSplice SourceResolventBandLimit SourceLocalizedInverseFormPayment
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusResponseAffine GaussNativePotential SourceRetardedBandCurrent
open MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
abbrev Op := H →L[ℂ] H
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
private abbrev n : ℝ := sourceTime 0
private abbrev U : End := SourcePhysicalKineticSquare.inverseVolumeAction
private abbrev S : End := phiInverseAction
private abbrev Q : End := 1-S
private abbrev T (m ell : ℕ) : End := phiThetaAction m ell
private abbrev B (m ell : ℕ) : End := SourceClockPhiRadiusResponseHessian.phiFirstPeak m ell
private abbrev D (a : ScalarIndex) : End := phiDirectionAction (scalarBasis a)
private abbrev L (a : ScalarIndex) : End := U*covariantMomentum (scalarDirection a)
private abbrev A (μ : ℝ) (F : Index) : End := BoundedClockNativeCore.abelCore μ F
private abbrev E (a : ScalarIndex) (i j : Fin 2) (m ell : ℕ) : End :=
  BoundedClockNativeCore.nativeColumnCore a i j m ell
attribute [local irreducible] resolventCore finiteResolvent

private theorem phi_inverse_core (f:QuantumTest) : phiInverseBounded (embed f)=embed (phiInverseAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem phi_inverse_norm : ‖phiInverseBounded‖ ≤ 1 := GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem phi_inverse_pair (x y:H) : inner ℂ (phiInverseBounded x) y=inner ℂ x (phiInverseBounded y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  obtain ⟨g,rfl⟩:=coreEquiv.surjective b
  change inner ℂ (phiInverseBounded (embed f)) (embed g)=inner ℂ (embed f) (phiInverseBounded (embed g))
  rw [phi_inverse_core,phi_inverse_core]
  exact (multiply_pair _ _ _ _).symm
private theorem phi_inverse_positive : 0 ≤ phiInverseBounded := by
  apply (ContinuousLinearMap.nonneg_iff_isPositive _).mpr
  refine ⟨phi_inverse_pair,?_⟩
  intro x
  change 0 ≤ (inner ℂ (phiInverseBounded x) x).re
  rw [phi_inverse_pair]
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_le continuous_const (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩:=coreEquiv.surjective a
  change 0 ≤ (inner ℂ (embed f) (phiInverseBounded (embed f))).re
  rw [phi_inverse_core]
  change 0 ≤ (sourcePair f (phiInverseAction f)).re
  rw [sourcePair_integral]
  have hr:(∫z,densityPair f (phiInverseAction f) z ∂GaussHistoryHilbert.configurationMeasure).re=
      ∫z,(densityPair f (phiInverseAction f) z).re ∂GaussHistoryHilbert.configurationMeasure := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re (densityPair_integrable f (phiInverseAction f))).symm
  rw [hr]
  apply integral_nonneg
  intro z
  change 0 ≤ (densityPair f (phiInverseAction f) z).re
  by_cases hz:z∈physicalChart
  · have hp:0 ≤ (densityPair f f z).re := by
      change 0 ≤ RCLike.re (inner ℂ (weight (fun N=>(density N z:ℂ)) (f z)) (f z))
      rw [GaussBoundedMultiplier.weighted_square _ (fun N=>(density_pos N ⟨z,hz⟩).le)]
      exact sq_nonneg _
    have he:densityPair f (phiInverseAction f) z=(phiReciprocal z:ℂ)*densityPair f f z :=
      inner_smul_right _ _ _
    rw [he,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) hp
  · have hf:f z=0 := image_eq_zero_of_notMem_tsupport (fun h=>hz (f.tsupport_subset h))
    simp only [densityPair,hf,map_zero,inner_zero_left,Complex.zero_re,le_refl]
private def phiComplement : Op := 1-phiInverseBounded
private theorem phi_complement_positive : 0 ≤ phiComplement :=
  sub_nonneg.mpr ((CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_inverse_positive).mp phi_inverse_norm)
private theorem phi_complement_le_one : phiComplement ≤ 1 := sub_le_self _ phi_inverse_positive
/-- The same actual affine radial powers, on the full weighted Hilbert space. -/
private def phiTail (m ell:ℕ) : Op := phiComplement^(m+1)-phiComplement^(ell+1)
private theorem phi_power_core (n:ℕ) (f:QuantumTest) :
    (phiComplement^n) (embed f)=embed (((1-phiInverseAction)^n) f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ',pow_succ']
    change phiComplement ((phiComplement^n) (embed f))=embed ((1-phiInverseAction) (((1-phiInverseAction)^n) f))
    rw [ih]
    change embed (((1-phiInverseAction)^n) f)-phiInverseBounded (embed (((1-phiInverseAction)^n) f))=_
    rw [phi_inverse_core,←map_sub]
    rfl
private theorem phi_tail_core (m ell:ℕ) (f:QuantumTest) :
    phiTail m ell (embed f)=embed (phiThetaAction m ell f) := by
  simp only [phiTail,sub_apply,phi_power_core,phiThetaAction,LinearMap.sub_apply,map_sub]

private def boundary (n:ℕ) : Op := PositiveContractionRitt.gradient phiComplement n
private def peak (m ell:ℕ) : Op := boundary ell-boundary m
private theorem boundary_norm (n:ℕ) : ‖boundary n‖ ≤ 1 :=
  PositiveContractionRitt.gradient_norm phiComplement phi_complement_positive phi_complement_le_one n
private theorem peak_norm (m ell:ℕ) : ‖peak m ell‖ ≤ 2 := by
  exact (norm_sub_le _ _).trans ((add_le_add (boundary_norm ell) (boundary_norm m)).trans_eq (by norm_num))
private theorem theta_norm (m ell:ℕ) : ‖phiTail m ell‖ ≤ 2 := by
  have hQ:‖phiComplement‖ ≤ 1 := (CStarAlgebra.norm_le_one_iff_of_nonneg _ phi_complement_positive).mpr phi_complement_le_one
  have hpow (k:ℕ):‖phiComplement^k‖ ≤ 1 := by
    induction k with
    | zero =>
      rw [pow_zero]
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro x
      change ‖x‖ ≤ 1*‖x‖
      rw [one_mul]
    | succ k ih =>
      rw [pow_succ]
      exact (norm_mul_le _ _).trans ((mul_le_mul ih hQ (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  unfold phiTail
  exact (norm_sub_le _ _).trans ((add_le_add (hpow _) (hpow _)).trans_eq (by norm_num))
private def coefficient (m ell:ℕ) : Fin 2 → Fin 2 → Op :=
  !![(2:ℂ) • peak m ell-phiTail m ell,(-2:ℂ) • (phiInverseBounded*peak m ell);
    (-2:ℂ) • (phiInverseBounded*peak m ell),phiInverseBounded^2*(phiTail m ell+(2:ℂ) • peak m ell)]
private theorem coefficient_norm (m ell:ℕ) (i j:Fin 2) : ‖coefficient m ell i j‖ ≤ 6 := by
  have hs:‖phiInverseBounded‖ ≤ 1:=phi_inverse_norm
  have hs2:‖phiInverseBounded^2‖ ≤ 1 := by
    rw [pow_two]
    exact (norm_mul_le _ _).trans ((mul_le_mul hs hs (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
  have hp:=peak_norm m ell
  have ht:=theta_norm m ell
  have h2:‖(2:ℂ) • peak m ell‖ ≤ 4 := by simpa only [norm_smul,Complex.norm_ofNat,show (2:ℝ)*2=4 by norm_num] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 2)
  have hS:‖phiInverseBounded*peak m ell‖ ≤ 2 := (norm_mul_le _ _).trans ((mul_le_mul hs hp (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  fin_cases i <;> fin_cases j
  · exact (norm_sub_le _ _).trans ((add_le_add h2 ht).trans_eq (by norm_num))
  · change ‖(-2:ℂ) • (phiInverseBounded*peak m ell)‖ ≤ 6
    rw [norm_smul,norm_neg,Complex.norm_ofNat]
    linarith
  · change ‖(-2:ℂ) • (phiInverseBounded*peak m ell)‖ ≤ 6
    rw [norm_smul,norm_neg,Complex.norm_ofNat]
    linarith
  · exact (norm_mul_le _ _).trans ((mul_le_mul hs2 ((norm_add_le _ _).trans (add_le_add ht h2))
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num))

private def profileCore (m ell:ℕ) : Fin 2 → Fin 2 → End :=
  !![(2:ℂ) • (B m ell*S)-T m ell,(-2:ℂ) • (S*(B m ell*S));
    (-2:ℂ) • (S*(B m ell*S)),S^2*(T m ell+(2:ℂ) • (B m ell*S))]
private def CoreReturn (A:Op) (a:End) : Prop := ∀f:QuantumTest,A (embed f)=embed (a f)
private theorem core_mul {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A*B) (a*b) := by intro f;change A (B (embed f))=embed (a (b f));rw [hb,ha]
private theorem core_add {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A+B) (a+b) := by intro f;change A (embed f)+B (embed f)=embed (a f+b f);rw [ha,hb,map_add]
private theorem core_sub {A B:Op} {a b:End} (ha:CoreReturn A a) (hb:CoreReturn B b) :
    CoreReturn (A-B) (a-b) := by intro f;change A (embed f)-B (embed f)=embed (a f-b f);rw [ha,hb,map_sub]
private theorem core_smul {A:Op} {a:End} (ha:CoreReturn A a) (c:ℂ) :
    CoreReturn (c • A) (c • a) := by intro f;change c • A (embed f)=embed (c • a f);rw [ha,map_smul]
private theorem gradient_complex {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (Q:E →L[ℂ] E) (n:ℕ) :
    PositiveContractionRitt.gradient Q n=(n+1:ℂ) • (Q^n*(1-Q)) := by
  unfold PositiveContractionRitt.gradient
  have hr:=RCLike.real_smul_eq_coe_smul (K:=ℂ) (n+1:ℝ) (Q^n*(1-Q))
  simpa only [RCLike.ofReal_add,RCLike.ofReal_natCast,RCLike.ofReal_one] using hr
private theorem boundary_core (j:ℕ) : CoreReturn (boundary j) ((j+1:ℂ) • (Q^j*S)) := by
  unfold boundary
  rw [gradient_complex]
  have hS:(1:Op)-phiComplement=phiInverseBounded:=by unfold phiComplement;abel
  rw [hS]
  exact core_smul (core_mul (phi_power_core j) phi_inverse_core) _
private theorem peak_core (m ell:ℕ) : CoreReturn (peak m ell) (B m ell*S) := by
  have h:=core_sub (boundary_core ell) (boundary_core m)
  simpa only [peak,B,SourceClockPhiRadiusResponseHessian.phiFirstPeak,sub_mul,smul_mul_assoc] using h
private theorem coefficient_core (i j:Fin 2) (m ell:ℕ) : CoreReturn (coefficient m ell i j) (profileCore m ell i j) := by
  have hs:CoreReturn phiInverseBounded S:=phi_inverse_core
  have ht:CoreReturn (phiTail m ell) (T m ell):=phi_tail_core m ell
  have hb:=peak_core m ell
  fin_cases i <;> fin_cases j
  · exact core_sub (core_smul hb 2) ht
  · exact core_smul (core_mul hs hb) (-2)
  · exact core_smul (core_mul hs hb) (-2)
  · have hs2:CoreReturn (phiInverseBounded^2) (S^2):=by simpa only [pow_two] using core_mul hs hs
    exact core_mul hs2 (core_add ht (core_smul hb 2))

private theorem abel_norm (μ : ℝ) (hμ : 0<μ) (F : Index) :
    ‖SourceBoundedClockAbel.abelObservable μ F‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (SourceBoundedClockAbel.actual_bounded_clock_abel_source μ hμ F).2.1).mpr
    (SourceBoundedClockAbel.actual_bounded_clock_abel_source μ hμ F).2.2.1
private theorem two_square {E : Type*} [NormedAddCommGroup E] (x y : E) :
    ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private abbrev directionOp (a : ScalarIndex) : H →L[ℂ] H :=
  SourceClockPhiRadiusSourceCurrent.phiDirectionOperator (scalarBasis a)
private def frameColumn (μ : ℝ) (F : Index) (a : ScalarIndex) : H →L[ℂ] H :=
  directionOp a*SourceBoundedClockAbel.abelObservable μ F-
    SourceBoundedClockAbel.abelObservable μ F*directionOp a

private theorem frame_column_gram (μ : ℝ) (hμ : 0<μ) (F : Index) (x : H) :
    (∑a : ScalarIndex,‖frameColumn μ F a x‖^2) ≤ ‖x‖^2 := by
  let A := SourceBoundedClockAbel.abelObservable μ F
  have ha (y : H) : ‖A y‖ ≤ ‖y‖ := (A.le_opNorm y).trans
    ((mul_le_mul_of_nonneg_right (abel_norm μ hμ F) (norm_nonneg y)).trans_eq (one_mul _))
  have hrow (a : ScalarIndex) : ‖frameColumn μ F a x‖^2 ≤
      2*‖directionOp a (A x)‖^2+2*‖directionOp a x‖^2 := by
    have h := two_square (directionOp a (A x)) (-(A (directionOp a x)))
    rw [norm_neg,←sub_eq_add_neg] at h
    have hA := pow_le_pow_left₀ (norm_nonneg _) (ha (directionOp a x)) 2
    change ‖directionOp a (A x)-A (directionOp a x)‖^2 ≤ _
    nlinarith only [h,hA]
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun a (_:a∈(Finset.univ:Finset ScalarIndex))=>hrow a)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at h
  have hq := SourceClockPhiRadiusSourceCurrent.original_phi_gradient_energy (A x)
  have hx := SourceClockPhiRadiusSourceCurrent.original_phi_gradient_energy x
  change (∑a : ScalarIndex,‖directionOp a (A x)‖^2)=_ at hq
  change (∑a : ScalarIndex,‖directionOp a x‖^2)=_ at hx
  rw [hq,hx] at h
  have hA := pow_le_pow_left₀ (norm_nonneg _) (ha x) 2
  nlinarith only [h,hA,sq_nonneg ‖SourceClockPhiRadiusSourceCurrent.phiInverseBounded (A x)‖,
    sq_nonneg ‖SourceClockPhiRadiusSourceCurrent.phiInverseBounded x‖]

private theorem frame_two_seed_gram (μ : ℝ) (hμ : 0<μ) (F : Index)
    (Z : Fin 2 → Fin 2 → H) :
    (∑i : Fin 2,∑a : ScalarIndex,‖∑j : Fin 2,frameColumn μ F a (Z i j)‖^2) ≤
      2*∑i : Fin 2,∑j : Fin 2,‖Z i j‖^2 := by
  have hrow (i : Fin 2) (a : ScalarIndex) :
      ‖∑j : Fin 2,frameColumn μ F a (Z i j)‖^2 ≤
        2*∑j : Fin 2,‖frameColumn μ F a (Z i j)‖^2 := by
    rw [Fin.sum_univ_two,Fin.sum_univ_two,mul_add]
    exact two_square _ _
  calc
    _ ≤ ∑i : Fin 2,∑a : ScalarIndex,2*∑j : Fin 2,‖frameColumn μ F a (Z i j)‖^2 :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun a _=>hrow i a))
    _ = 2*∑i : Fin 2,∑j : Fin 2,∑a : ScalarIndex,‖frameColumn μ F a (Z i j)‖^2 := by
      simp only [←Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl;intro i _
      exact Finset.sum_comm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>frame_column_gram μ hμ F (Z i j))))
      (by norm_num)

-- Once Z_ij=e_ij X_j and e_ij=coefficient_ij theta are identified from the
-- exact original nativeColumn_core, coefficient_norm≤6 yields 144Σ_j||theta X_j||².
-- This is the two fixed-source error, not a weighted graph bound for A X.


private def profile (i j : Fin 2) (m ell : ℕ) : End := profileCore m ell i j*T m ell
private def profileOp (i j : Fin 2) (m ell : ℕ) : Op := coefficient m ell i j*phiTail m ell
private theorem profile_core (i j : Fin 2) (m ell : ℕ) (f : QuantumTest) :
    profileOp i j m ell (embed f)=embed (profile i j m ell f) :=
  core_mul (coefficient_core i j m ell) (phi_tail_core m ell) f
private theorem source_column_profile (a : ScalarIndex) (i j : Fin 2) (m ell : ℕ) :
    E a i j m ell=D a*profile i j m ell := by
  apply LinearMap.ext;intro f;apply embed_injective
  calc
    embed (E a i j m ell f)=SourceClockPhiNativeJointPayment.nativeColumn a i j m ell (embed f) :=
      (SourceClockPhiNativeJointPayment.actual_native_column_core a i j m ell f).symm
    _=phiDirectionOperator (scalarBasis a) (profileOp i j m ell (embed f)) := rfl
    _=embed (D a (profile i j m ell f)) := by rw [profile_core,original_phi_direction_core]
private theorem profile_norm (i j : Fin 2) (m ell : ℕ) (x : H) :
    ‖profileOp i j m ell x‖ ≤ 6*‖phiTail m ell x‖ :=
  ((coefficient m ell i j).le_opNorm (phiTail m ell x)).trans
    (mul_le_mul_of_nonneg_right (coefficient_norm m ell i j) (norm_nonneg _))

private def sourceState (i:Fin 2) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : QuantumTest :=
  resolventCore F z hz (coreEquiv.symm (SourceClockPhiNativeJointPayment.inputSeed g i))
private def nativeInput (a:ScalarIndex) (i:Fin 2) (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) : H :=
  embed (SourcePhysicalKineticSquare.inverseVolumeAction
    (covariantMomentum (scalarDirection a) (sourceState i F z hz g)))

private theorem debit_source (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    SourceClockPhiNativeJointPayment.nativePressureDebit F z hz g=∑i:Fin 2,SourceClockPhiSecondPressure.pressure (sourceState i F z hz g) := by
  unfold SourceClockPhiNativeJointPayment.nativePressureDebit
  rw [SourceClockPhiSecondBulk.actual_second_compression_source]
  rfl
private theorem lapse_pos : 0 < sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos
private theorem native_debit (F:Index) (z:ℂ) (hz:z.im≠0) (g:diagonal.domain) :
    sourceTime 0*(∑i:Fin 2,∑a:ScalarIndex,‖nativeInput a i F z hz g‖^2) ≤ SourceClockPhiNativeJointPayment.nativePressureDebit F z hz g := by
  rw [debit_source,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hc (a:ScalarIndex):‖nativeInput a i F z hz g‖=
      ‖embed (covariantMomentum (scalarDirection a)
        (SourcePhysicalKineticSquare.inverseVolumeAction (sourceState i F z hz g)))‖ := by
    have h:=LinearMap.congr_fun (SourceScalarInverseNativeEnergy.original_native_inverse_commute (scalarDirection a)).eq
      (sourceState i F z hz g)
    exact congrArg (fun f:QuantumTest=>‖embed f‖) h.symm
  simp_rw [hc]
  have h:=SourceClockPhiSecondPressure.original_second_pressure_payment (sourceState i F z hz g)
  have hn:0 ≤ shiftedMoment (sourceState i F z hz g):=Finset.sum_nonneg (fun _ _=>sq_nonneg _)
  have hm:=mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) lapse_pos.le) hn
  exact (le_add_of_nonneg_right hm).trans h
private theorem young_native (μ η x y:ℝ) (hη:0 < η) :
    (2*sourceTime 0*μ)*(x*y) ≤ η*sourceTime 0*x^2+(sourceTime 0*μ^2/η)*y^2 := by
  apply (mul_le_mul_iff_left₀ hη).mp
  have he:(η*sourceTime 0*x^2+(sourceTime 0*μ^2/η)*y^2)*η=
      η^2*sourceTime 0*x^2+sourceTime 0*μ^2*y^2 := by field_simp
  rw [he]
  have h:=mul_nonneg lapse_pos.le (sq_nonneg (η*x-μ*y))
  nlinarith only [h]


private def frameInput (a : ScalarIndex) (i : Fin 2) (m ell : ℕ) (μ : ℝ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : H :=
  ∑j : Fin 2,frameColumn μ F a (profileOp i j m ell (embed (sourceState j F z hz g)))
private def frameEnergy (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ := ∑i : Fin 2,∑a : ScalarIndex,‖frameInput a i m ell μ F z hz g‖^2
private def errorEnergy (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  ∑j : Fin 2,‖phiTail m ell (embed (sourceState j F z hz g))‖^2
private def frameHalf (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  (2*n*μ)*(∑i : Fin 2,∑a : ScalarIndex,inner ℂ (nativeInput a i F z hz g)
    (frameInput a i m ell μ F z hz g)).im

def radialGenerator : End := (Complex.I/4:ℂ) •
  (U*S*SourceScalarVirialBulk.phiEulerAction)
/-- The remaining operator is the original scalar61 Euler current, on the same two source legs. -/
def radialHalf (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  (2*n*μ)*(∑i : Fin 2,∑j : Fin 2,sourcePair
    (bracket radialGenerator (A μ F) (sourceState i F z hz g))
    (profile i j m ell (sourceState j F z hz g))).im

private theorem frame_energy_price (m ell : ℕ) (μ : ℝ) (hμ : 0<μ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    frameEnergy m ell μ F z hz g ≤ 144*errorEnergy m ell F z hz g := by
  have h := frame_two_seed_gram μ hμ F (fun i j=>profileOp i j m ell (embed (sourceState j F z hz g)))
  have hp (i j : Fin 2) : ‖profileOp i j m ell (embed (sourceState j F z hz g))‖^2 ≤
      36*‖phiTail m ell (embed (sourceState j F z hz g))‖^2 := by
    have he := pow_le_pow_left₀ (norm_nonneg _)
      (profile_norm i j m ell (embed (sourceState j F z hz g))) 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using he
  calc
    _ ≤ 2*∑i : Fin 2,∑j : Fin 2,‖profileOp i j m ell (embed (sourceState j F z hz g))‖^2 := h
    _ ≤ 2*∑i : Fin 2,∑j : Fin 2,36*‖phiTail m ell (embed (sourceState j F z hz g))‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>hp i j)))
        (by norm_num)
    _ = _ := by simp only [errorEnergy,Fin.sum_univ_two];ring
private theorem frame_point_price (m ell : ℕ) (μ : ℝ) (hμ : 0<μ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    |frameHalf m ell μ F z hz g|-η*SourceClockPhiNativeJointPayment.nativePressureDebit F z hz g ≤
      (144*n*μ^2/η)*errorEnergy m ell F z hz g := by
  have hI : |(∑i : Fin 2,∑a : ScalarIndex,inner ℂ (nativeInput a i F z hz g)
      (frameInput a i m ell μ F z hz g)).im| ≤
      ∑i : Fin 2,∑a : ScalarIndex,‖nativeInput a i F z hz g‖*‖frameInput a i m ell μ F z hz g‖ := by
    apply (Complex.abs_im_le_norm _).trans
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>(norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun a _=>norm_inner_le_norm _ _))))
  have h0 : 0 ≤ 2*n*μ := by have hn:=lapse_pos;positivity
  have h1 := mul_le_mul_of_nonneg_left hI h0
  have h2 := Finset.sum_le_sum (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Fin 2)))=>
    Finset.sum_le_sum (s:=Finset.univ) (fun a (_:a∈(Finset.univ:Finset ScalarIndex))=>
      young_native μ η ‖nativeInput a i F z hz g‖ ‖frameInput a i m ell μ F z hz g‖ hη))
  have h3 := mul_le_mul_of_nonneg_left (native_debit F z hz g) hη.le
  have h4 := mul_le_mul_of_nonneg_left (frame_energy_price m ell μ hμ F z hz g)
    (show 0 ≤ n*μ^2/η by have hn:=lapse_pos;positivity)
  rw [frameHalf,abs_mul,abs_of_nonneg h0]
  unfold frameEnergy at h4
  simp only [Finset.mul_sum,Finset.sum_add_distrib,←mul_assoc] at h1 h2 h3 h4 ⊢
  dsimp only [n] at h1 h4 ⊢
  have hc : sourceTime 0*μ^2/η*144*errorEnergy m ell F z hz g=
      (144*sourceTime 0*μ^2/η)*errorEnergy m ell F z hz g := by ring
  rw [hc] at h4
  linarith only [h1,h2,h3,h4]


private theorem pair_sub_left (p q r : QuantumTest) : sourcePair (p-q) r=sourcePair p r-sourcePair q r := by
  simp only [sourcePair,map_sub,inner_sub_left]
private theorem pair_sub_right (p q r : QuantumTest) : sourcePair p (q-r)=sourcePair p q-sourcePair p r := by
  simp only [sourcePair,map_sub,inner_sub_right]
private theorem pair_sum_left {ι : Type*} [Fintype ι] (p : ι → QuantumTest) (q : QuantumTest) :
    sourcePair (∑i,p i) q=∑i,sourcePair (p i) q := by simp only [sourcePair,map_sum,sum_inner]

private theorem direction_pair (a : ScalarIndex) (p q : QuantumTest) :
    sourcePair (D a p) q=sourcePair p (D a q) := (multiply_pair _ _ _ _).symm
private theorem abel_pair (μ : ℝ) (hμ : 0<μ) (F : Index) (p q : QuantumTest) :
    sourcePair (A μ F p) q=sourcePair p (A μ F q) := by
  have h := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (SourceBoundedClockAbel.actual_bounded_clock_abel_source μ hμ F).2.1).isSymmetric
  change inner ℂ (embed (A μ F p)) (embed q)=inner ℂ (embed p) (embed (A μ F q))
  rw [BoundedClockNativeCore.abelCore_embed μ hμ F,BoundedClockNativeCore.abelCore_embed μ hμ F]
  exact h _ _
private theorem frame_pair (μ : ℝ) (hμ : 0<μ) (F : Index) (a : ScalarIndex) (p q : QuantumTest) :
    sourcePair (bracket (D a) (A μ F) p) q= -sourcePair p (bracket (D a) (A μ F) q) := by
  change sourcePair (D a (A μ F p)-A μ F (D a p)) q=
    -sourcePair p (D a (A μ F q)-A μ F (D a q))
  rw [pair_sub_left,pair_sub_right,direction_pair,abel_pair μ hμ F,abel_pair μ hμ F,direction_pair]
  ring
private theorem frame_core (μ : ℝ) (hμ : 0<μ) (F : Index) (a : ScalarIndex) (f : QuantumTest) :
    embed (bracket (D a) (A μ F) f)=frameColumn μ F a (embed f) := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  rw [←original_phi_direction_core,BoundedClockNativeCore.abelCore_embed μ hμ F,
    BoundedClockNativeCore.abelCore_embed μ hμ F,←original_phi_direction_core]
  rfl
private theorem radial_contraction : (∑a : ScalarIndex,D a*L a)=radialGenerator :=
  ClockPhiNativeRadialContraction.original_native_radial_contraction
private theorem radial_frame_source (μ : ℝ) (F : Index) :
    (∑a : ScalarIndex,D a*bracket (L a) (A μ F))=
      bracket radialGenerator (A μ F)-(∑a : ScalarIndex,bracket (D a) (A μ F)*L a) := by
  rw [←radial_contraction]
  simp only [bracket,mul_sub,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum,mul_assoc]
  abel
private theorem radial_frame_pair (μ : ℝ) (hμ : 0<μ) (F : Index) (p q : QuantumTest) :
    (∑a : ScalarIndex,sourcePair (bracket (L a) (A μ F) p) (D a q))=
      sourcePair (bracket radialGenerator (A μ F) p) q+
        ∑a : ScalarIndex,sourcePair (L a p) (bracket (D a) (A μ F) q) := by
  have h := LinearMap.congr_fun (radial_frame_source μ F) p
  simp only [LinearMap.sum_apply,LinearMap.sub_apply,Module.End.mul_apply] at h
  calc
    _=sourcePair (∑a : ScalarIndex,D a (bracket (L a) (A μ F) p)) q := by
      simp only [sourcePair,map_sum,sum_inner]
      apply Finset.sum_congr rfl;intro a _
      exact (direction_pair a _ _).symm
    _=sourcePair (bracket radialGenerator (A μ F) p-(∑a : ScalarIndex,
        bracket (D a) (A μ F) (L a p))) q := by rw [h];rfl
    _=_ := by
      rw [pair_sub_left,pair_sum_left]
      simp_rw [frame_pair μ hμ F]
      simp only [Finset.sum_neg_distrib,sub_neg_eq_add]

/-- The full seventy-column curvature has one actual radial Euler remainder;
the bounded frame commutator is kept with its exact sign before payment. -/
theorem actual_native_radial_return (μ : ℝ) (hμ : 0<μ) (m ell : ℕ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    SourceClockAbelNativeCurvature.curvatureHalf m ell μ F z hz g=
      radialHalf m ell μ F z hz g+frameHalf m ell μ F z hz g := by
  let X : Fin 2 → QuantumTest := fun i=>sourceState i F z hz g
  have hswap (Z : Fin 2 → Fin 2 → ScalarIndex → ℂ) :
      (∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,Z i j a)=∑i:Fin 2,∑a:ScalarIndex,∑j:Fin 2,Z i j a := by
    apply Finset.sum_congr rfl;intro i _;exact Finset.sum_comm
  have hc : SourceClockAbelNativeCurvature.curvatureHalf m ell μ F z hz g=
      (2*n*μ)*(∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
        sourcePair (bracket (L a) (A μ F) (X i)) (E a i j m ell (X j))).im := by
    rw [hswap]
    simp only [SourceClockAbelNativeCurvature.curvatureHalf,sourcePair,map_sum,inner_sum]
    rfl
  have hf : frameHalf m ell μ F z hz g=
      (2*n*μ)*(∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
        sourcePair (L a (X i)) (bracket (D a) (A μ F) (profile i j m ell (X j)))).im := by
    rw [hswap]
    unfold frameHalf
    congr 1
    apply congrArg Complex.im
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro a _
    simp only [frameInput,inner_sum]
    apply Finset.sum_congr rfl;intro j _
    change inner ℂ (embed (L a (X i))) (frameColumn μ F a (profileOp i j m ell (embed (X j))))=_
    rw [profile_core,←frame_core μ hμ F]
    rfl
  rw [hc,hf]
  simp_rw [source_column_profile]
  change (2*n*μ)*(∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
    sourcePair (bracket (L a) (A μ F) (X i)) (D a (profile i j m ell (X j)))).im=_
  simp_rw [radial_frame_pair μ hμ F]
  simp only [Finset.sum_add_distrib,Complex.add_im,mul_add,radialHalf]
  rfl

private theorem frequency_nonreal (advanced : Bool) (μ : ℝ) (hμ : 0<μ) (w : ℝ) :
    (actualFrequency advanced μ w).im≠0 := by
  cases advanced <;> simpa only [actualFrequency,Bool.false_eq_true,ite_false,ite_true,
    Complex.star_def,Complex.conj_im,line_im,neg_ne_zero] using hμ.ne'
private theorem source_state_return (i : Fin 2) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : sourceState i F z hz g=
      SourceScalarPositiveBulkWard.state F z hz (SourceClockPhiNativeJointPayment.inputSeed g i) := by
  simp only [sourceState,resolventCore,LinearMap.coe_mk,AddHom.coe_mk,coreEquiv.apply_symm_apply]
private theorem source_state_embed (i : Fin 2) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (sourceState i F z hz g)=finiteResolvent F z (SourceClockPhiNativeJointPayment.inputSeed g i:H) := by
  rw [source_state_return]
  unfold SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem finite_star (F:Index) (z:ℂ) : finiteResolvent F (star z)=(finiteResolvent F z).adjoint := by
  unfold finiteResolvent
  change Ring.inverse (GaussGradedCompression.compression F-star z • 1)=(Ring.inverse (GaussGradedCompression.compression F-z • 1)).adjoint
  rw [←ContinuousLinearMap.star_eq_adjoint,←Ring.inverse_star]
  congr 1
  simp only [star_sub,star_smul,star_one,(GaussGradedCompression.compression_selfAdjoint F).star_eq]
private theorem frequency_continuous (advanced:Bool) (μ:ℝ) (hμ:0 < μ) (F:Index) :
    Continuous (fun w:ℝ=>finiteResolvent F (actualFrequency advanced μ w)) := by
  cases advanced
  · exact finite_frequency_continuous μ hμ F
  · have he:(fun w:ℝ=>finiteResolvent F (actualFrequency true μ w))=
        (fun w:ℝ=>(finiteResolvent F (line μ w)).adjoint) := funext (fun w=>finite_star F (line μ w))
    exact he ▸ (ContinuousLinearMap.adjoint.continuous.comp (finite_frequency_continuous μ hμ F))
private theorem error_measurable (m ell : ℕ) (μ : ℝ) (hμ : 0<μ) (advanced : Bool) (F : Index)
    (g : diagonal.domain) :
    Measurable (fun w : ℝ=>ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)) := by
  have h (i : Fin 2) : Measurable (fun w : ℝ=>‖phiTail m ell
      (finiteResolvent F (actualFrequency advanced μ w) (SourceClockPhiNativeJointPayment.inputSeed g i:H))‖^2) :=
    ((phiTail m ell).continuous.comp ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2 |>.measurable
  unfold errorEnergy
  simp_rw [source_state_embed]
  exact (Finset.measurable_sum _ (fun i _=>h i)).ennreal_ofReal
private theorem error_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ε : ℝ,0 < ε → ∃ M : ℕ,∀m : ℕ,M ≤ m → ∀ell : ℕ,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced : Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨M₀,h₀⟩ := SourceClockPhiRadiusResponseNativeBudget.actual_phi_theta_common_tail μ hμ g (ε/2) (by positivity)
  obtain ⟨M₁,h₁⟩ := SourceClockPhiRadiusResponseNativeBudget.actual_phi_theta_common_tail μ hμ (phiRadiusSource g) (ε/2) (by positivity)
  refine ⟨max M₀ M₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hg hh
  intro advanced
  have he (w : ℝ) : errorEnergy m ell F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g=
      ‖embed (phiThetaAction m ell (SourceScalarPositiveBulkWard.state F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g))‖^2+
      ‖embed (phiThetaAction m ell (SourceScalarPositiveBulkWard.state F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) (phiRadiusSource g)))‖^2 := by
    simp only [errorEnergy,Fin.sum_univ_two,phi_tail_core,source_state_return,
      SourceClockPhiNativeJointPayment.inputSeed,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp_rw [he,ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  have hm₀ : Measurable (fun w : ℝ=>ENNReal.ofReal (‖embed (phiThetaAction m ell
      (SourceScalarPositiveBulkWard.state F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g))‖^2)) := by
    have hstate (w : ℝ) : embed (SourceScalarPositiveBulkWard.state F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g)=finiteResolvent F (actualFrequency advanced μ w) (g:H) := by
      unfold SourceScalarPositiveBulkWard.state
      exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
    simp_rw [←phi_tail_core,hstate]
    exact ((phiTail m ell).continuous.comp ((frequency_continuous advanced μ hμ F).clm_apply continuous_const)).norm.pow 2 |>.measurable.ennreal_ofReal
  rw [lintegral_add_left hm₀]
  calc _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal (ε/2) := add_le_add (hg advanced) (hh advanced)
       _ = ENNReal.ofReal ε := by rw [←ENNReal.ofReal_add (by positivity) (by positivity)];congr 1;ring

/-- The original complete native Pi is paid down to its single actual radial Euler
commutator, using only the original pressure debit and the two fixed-source theta tails. -/
theorem actual_native_radial_common_payment (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ∀ε : ℝ,0 < ε → ∃ M : ℕ,∀m : ℕ,M ≤ m → ∀ell : ℕ,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced : Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (|SourceClockAbelNativeCurvature.nativePi m ell μ F
          (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
        radialHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let c : ℝ := 144*n*μ^2/(η/2)
  have hc : 0<c := by dsimp only [c];have hn:=lapse_pos;positivity
  obtain ⟨M₀,h₀⟩ := SourceClockAbelNativeCurvature.actual_native_curvature_common_payment μ hμ g
    (η/2) (by positivity) (ε/2) (by positivity)
  obtain ⟨M₁,h₁⟩ := error_common_tail μ hμ g (ε/(2*c)) (by positivity)
  refine ⟨max M₀ M₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hC hE
  intro advanced
  let price : ℝ → ℝ := fun w=>
    |SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g+
      SourceClockAbelNativeCurvature.curvatureHalf m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|-
      (η/2)*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g
  have hpoint (w : ℝ) :
      ENNReal.ofReal (|SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g+
        radialHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g) ≤
        ENNReal.ofReal c*ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)+ENNReal.ofReal (price w) := by
    have hreturn := actual_native_radial_return μ hμ m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g
    have hframe := frame_point_price m ell μ hμ F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g (η/2) (by positivity)
    have htriangle := abs_sub (SourceClockAbelNativeCurvature.nativePi m ell μ F
      (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
      SourceClockAbelNativeCurvature.curvatureHalf m ell μ F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g)
      (frameHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)
    rw [hreturn] at htriangle
    have he : SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g+
        (radialHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
        frameHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)-
        frameHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g=
      SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g+
        radialHalf m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g := by ring
    rw [he] at htriangle
    calc _ ≤ ENNReal.ofReal (c*errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g+price w) := by
          apply ENNReal.ofReal_le_ofReal
          dsimp only [price,c]
          rw [hreturn]
          linarith only [hframe,htriangle]
         _ ≤ ENNReal.ofReal (c*errorEnergy m ell F (actualFrequency advanced μ w)
              (frequency_nonreal advanced μ hμ w) g)+ENNReal.ofReal (price w) :=
          ENNReal.ofReal_add_le
         _ = _ := by rw [ENNReal.ofReal_mul hc.le]
  calc _ ≤ ∫⁻w:ℝ,ENNReal.ofReal c*ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)+ENNReal.ofReal (price w) := lintegral_mono hpoint
       _ = ENNReal.ofReal c*(∫⁻w:ℝ,ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g))+(∫⁻w:ℝ,ENNReal.ofReal (price w)) := by
          rw [lintegral_add_left ((error_measurable m ell μ hμ advanced F g).const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
       _ ≤ ENNReal.ofReal c*ENNReal.ofReal (ε/(2*c))+ENNReal.ofReal (ε/2) :=
          add_le_add (mul_le_mul le_rfl (hE advanced) zero_le zero_le) (hC advanced)
       _ = ENNReal.ofReal ε := by
          rw [←ENNReal.ofReal_mul hc.le,←ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring

end LowEnergy.SourceClockAbelNativeRadialPayment
