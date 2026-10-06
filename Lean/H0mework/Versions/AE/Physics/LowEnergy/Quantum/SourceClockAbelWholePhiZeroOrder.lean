import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockAbelNativeCurvature
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockAbelNativeRadialPayment
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiZeroOrderProfile
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeJointPayment
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiNativeRadialContraction
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseNativeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockAbelWholePhiZeroOrder
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

private abbrev profile (i j : Fin 2) (m ell : ℕ) : End := SourceClockPhiZeroOrderProfile.radialProfile i j m ell
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


private def errorEnergy (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℝ :=
  ∑j : Fin 2,‖phiTail m ell (embed (sourceState j F z hz g))‖^2

private abbrev radialGenerator : End := SourceClockAbelNativeRadialPayment.radialGenerator
private abbrev zeroProfile (i j : Fin 2) (m ell : ℕ) : End := SourceClockPhiZeroOrderProfile.zeroProfile i j m ell
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


/-- The complete U-weighted radial matrix is retained as one real source word. -/
def zeroWord (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  (n*μ/2)*(∑i:Fin 2,∑j:Fin 2,sourcePair (A μ F (sourceState i F z hz g))
    (U (zeroProfile i j m ell (sourceState j F z hz g)))).re
private def ordinaryWord (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  (4*n*μ)*(∑i:Fin 2,∑j:Fin 2,sourcePair (radialGenerator (sourceState i F z hz g))
    (A μ F (profile i j m ell (sourceState j F z hz g)))).im


private theorem abel_norm (μ : ℝ) (hμ : 0<μ) (F : Index) :
    ‖SourceBoundedClockAbel.abelObservable μ F‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _
    (SourceBoundedClockAbel.actual_bounded_clock_abel_source μ hμ F).2.1).mpr
    (SourceBoundedClockAbel.actual_bounded_clock_abel_source μ hμ F).2.2.1
private theorem two_square {V : Type*} [NormedAddCommGroup V] (x y : V) :
    ‖x+y‖^2 ≤ 2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private def ordinaryInput (a : ScalarIndex) (i : Fin 2) (m ell : ℕ) (μ : ℝ)
    (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : H :=
  phiDirectionOperator (scalarBasis a) (SourceBoundedClockAbel.abelObservable μ F
    (∑j:Fin 2,profileOp i j m ell (embed (sourceState j F z hz g))))
private theorem ordinary_energy (m ell : ℕ) (μ : ℝ) (hμ : 0<μ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑i:Fin 2,∑a:ScalarIndex,‖ordinaryInput a i m ell μ F z hz g‖^2) ≤
      36*errorEnergy m ell F z hz g := by
  let X (i : Fin 2) : H := ∑j:Fin 2,profileOp i j m ell (embed (sourceState j F z hz g))
  have ha (y : H) : ‖SourceBoundedClockAbel.abelObservable μ F y‖ ≤ ‖y‖ :=
    ((SourceBoundedClockAbel.abelObservable μ F).le_opNorm y).trans
      ((mul_le_mul_of_nonneg_right (abel_norm μ hμ F) (norm_nonneg y)).trans_eq (one_mul _))
  have hp (i j : Fin 2) : ‖profileOp i j m ell (embed (sourceState j F z hz g))‖^2 ≤
      36*‖phiTail m ell (embed (sourceState j F z hz g))‖^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) (profile_norm i j m ell (embed (sourceState j F z hz g))) 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using h
  have hx (i : Fin 2) : ‖X i‖^2 ≤ 72*errorEnergy m ell F z hz g := by
    have h := two_square (profileOp i 0 m ell (embed (sourceState 0 F z hz g)))
      (profileOp i 1 m ell (embed (sourceState 1 F z hz g)))
    dsimp only [X]
    rw [Fin.sum_univ_two]
    rw [errorEnergy,Fin.sum_univ_two]
    linarith only [h,hp i 0,hp i 1]
  have hrow (i : Fin 2) : (∑a:ScalarIndex,‖ordinaryInput a i m ell μ F z hz g‖^2) ≤
      18*errorEnergy m ell F z hz g := by
    change (∑a:ScalarIndex,‖phiDirectionOperator (scalarBasis a)
      (SourceBoundedClockAbel.abelObservable μ F (X i))‖^2) ≤ _
    rw [original_phi_gradient_energy]
    have hA := pow_le_pow_left₀ (norm_nonneg _) (ha (X i)) 2
    nlinarith only [hA,hx i,sq_nonneg ‖phiInverseBounded (SourceBoundedClockAbel.abelObservable μ F (X i))‖]
  rw [Fin.sum_univ_two]
  linarith only [hrow 0,hrow 1]
private theorem ordinary_source (m ell : ℕ) (μ : ℝ) (hμ : 0<μ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ordinaryWord m ell μ F z hz g=
      (4*n*μ)*(∑i:Fin 2,∑a:ScalarIndex,
        inner ℂ (nativeInput a i F z hz g) (ordinaryInput a i m ell μ F z hz g)).im := by
  have hr : (∑a:ScalarIndex,D a*L a)=radialGenerator :=
    ClockPhiNativeRadialContraction.original_native_radial_contraction
  unfold ordinaryWord
  rw [←hr]
  simp only [LinearMap.sum_apply,Module.End.mul_apply,sourcePair,map_sum,sum_inner]
  congr 1
  apply congrArg Complex.im
  apply Finset.sum_congr rfl;intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl;intro a _
  unfold ordinaryInput
  simp only [map_sum,inner_sum]
  apply Finset.sum_congr rfl;intro j _
  have hD (p q : QuantumTest) : sourcePair (D a p) q=sourcePair p (D a q) :=
    (multiply_pair _ _ _ _).symm
  change sourcePair (D a (L a (sourceState i F z hz g)))
      (A μ F (profile i j m ell (sourceState j F z hz g)))=_
  rw [hD]
  change inner ℂ (embed (L a (sourceState i F z hz g)))
      (embed (D a (A μ F (profile i j m ell (sourceState j F z hz g)))))=_
  rw [←original_phi_direction_core,BoundedClockNativeCore.abelCore_embed μ hμ F,←profile_core]
  rfl
private theorem young_ordinary (μ η x y : ℝ) (hη : 0<η) :
    (4*sourceTime 0*μ)*(x*y) ≤ η*sourceTime 0*x^2+(4*sourceTime 0*μ^2/η)*y^2 := by
  convert young_native (2*μ) η x y hη using 1 <;> ring
private theorem ordinary_point_price (m ell : ℕ) (μ : ℝ) (hμ : 0<μ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) (η : ℝ) (hη : 0<η) :
    |ordinaryWord m ell μ F z hz g|-η*SourceClockPhiNativeJointPayment.nativePressureDebit F z hz g ≤
      (144*n*μ^2/η)*errorEnergy m ell F z hz g := by
  rw [ordinary_source m ell μ hμ F z hz g]
  have hI : |(∑i:Fin 2,∑a:ScalarIndex,
      inner ℂ (nativeInput a i F z hz g) (ordinaryInput a i m ell μ F z hz g)).im| ≤
      ∑i:Fin 2,∑a:ScalarIndex,‖nativeInput a i F z hz g‖*‖ordinaryInput a i m ell μ F z hz g‖ := by
    apply (Complex.abs_im_le_norm _).trans
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _=>(norm_sum_le _ _).trans
      (Finset.sum_le_sum (fun a _=>norm_inner_le_norm _ _))))
  have h0 : 0 ≤ 4*n*μ := by have hn:=lapse_pos;positivity
  have h1 := mul_le_mul_of_nonneg_left hI h0
  have h2 := Finset.sum_le_sum (s:=Finset.univ) (fun i (_:i∈(Finset.univ:Finset (Fin 2)))=>
    Finset.sum_le_sum (s:=Finset.univ) (fun a (_:a∈(Finset.univ:Finset ScalarIndex))=>
      young_ordinary μ η ‖nativeInput a i F z hz g‖ ‖ordinaryInput a i m ell μ F z hz g‖ hη))
  have h3 := mul_le_mul_of_nonneg_left (native_debit F z hz g) hη.le
  have h4 := mul_le_mul_of_nonneg_left (ordinary_energy m ell μ hμ F z hz g)
    (show 0 ≤ 4*n*μ^2/η by have hn:=lapse_pos;positivity)
  rw [abs_mul,abs_of_nonneg h0]
  simp only [Finset.mul_sum,Finset.sum_add_distrib,←mul_assoc] at h1 h2 h3 h4 ⊢
  dsimp only [n] at h1 h4 ⊢
  have hc : 4*sourceTime 0*μ^2/η*36*errorEnergy m ell F z hz g=
      (144*sourceTime 0*μ^2/η)*errorEnergy m ell F z hz g := by ring
  rw [hc] at h4
  linarith only [h1,h2,h3,h4]

private theorem phi_pair_one : GaussCoframeForm.Paired (1:End) 1 := by intro p q;rfl

private theorem phi_pair_add {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A+B) (A+B) := by
  intro p q
  simp only [LinearMap.add_apply,sourcePair,map_add,inner_add_left,inner_add_right]
  exact congrArg₂ (·+·) (hA p q) (hB p q)

private theorem phi_pair_sub {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) : GaussCoframeForm.Paired (A-B) (A-B) := by
  intro p q
  simp only [LinearMap.sub_apply,sourcePair,map_sub,inner_sub_left,inner_sub_right]
  exact congrArg₂ (·-·) (hA p q) (hB p q)

private theorem phi_pair_real {A : End} (c : ℝ) (hA : GaussCoframeForm.Paired A A) :
    GaussCoframeForm.Paired ((c:ℂ) • A) ((c:ℂ) • A) := by
  intro p q
  simp only [LinearMap.smul_apply,sourcePair,map_smul,inner_smul_left,inner_smul_right,
    Complex.conj_ofReal]
  exact congrArg ((c:ℂ)*·) (hA p q)

private theorem phi_pair_mul {A B : End} (hA : GaussCoframeForm.Paired A A)
    (hB : GaussCoframeForm.Paired B B) (hAB : Commute A B) :
    GaussCoframeForm.Paired (A*B) (A*B) := by
  intro p q
  change sourcePair p (A (B q))=sourcePair (A (B p)) q
  have hc := LinearMap.congr_fun hAB.eq p
  change A (B p)=B (A p) at hc
  rw [hA,hB,←hc]

private theorem phi_pair_pow {A : End} (hA : GaussCoframeForm.Paired A A) (n : ℕ) :
    GaussCoframeForm.Paired (A^n) (A^n) := by
  induction n with
  | zero => simpa only [pow_zero] using phi_pair_one
  | succ n ih =>
    rw [pow_succ]
    exact phi_pair_mul ih hA ((Commute.refl A).pow_left n)

private theorem phi_S_pair : GaussCoframeForm.Paired S S := multiply_pair _ _

private theorem phi_Q_pair : GaussCoframeForm.Paired Q Q := phi_pair_sub phi_pair_one phi_S_pair

private theorem phi_theta_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (phiThetaAction m ell) (phiThetaAction m ell) :=
  phi_pair_sub (phi_pair_pow phi_Q_pair (m+1)) (phi_pair_pow phi_Q_pair (ell+1))

private theorem phi_first_pair (m ell : ℕ) :
    GaussCoframeForm.Paired (B m ell) (B m ell) := by
  unfold B SourceClockPhiRadiusResponseHessian.phiFirstPeak
  change GaussCoframeForm.Paired
    (((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m) : End)
    (((ell+1:ℂ) • Q^ell-(m+1:ℂ) • Q^m) : End)
  have h := phi_pair_sub (phi_pair_real (ell+1:ℝ) (phi_pair_pow phi_Q_pair ell))
    (phi_pair_real (m+1:ℝ) (phi_pair_pow phi_Q_pair m))
  simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one] using h


private theorem first_commute {K : End} (h : Commute S K) (m ell : ℕ) : Commute (B m ell) K :=
  (((((Commute.one_left K).sub_left h).pow_left ell).smul_left _).sub_left
    ((((Commute.one_left K).sub_left h).pow_left m).smul_left _))
private theorem theta_commute {K : End} (h : Commute S K) (m ell : ℕ) : Commute (T m ell) K :=
  (((Commute.one_left K).sub_left h).pow_left (m+1)).sub_left
    (((Commute.one_left K).sub_left h).pow_left (ell+1))
private theorem coefficient_commute {K : End} (h : Commute S K) (i j : Fin 2) (m ell : ℕ) :
    Commute (profileCore m ell i j) K := by
  have hb := first_commute h m ell
  have ht := theta_commute h m ell
  fin_cases i <;> fin_cases j
  · exact ((hb.mul_left h).smul_left (2:ℂ)).sub_left ht
  · exact (h.mul_left (hb.mul_left h)).smul_left (-2:ℂ)
  · exact (h.mul_left (hb.mul_left h)).smul_left (-2:ℂ)
  · exact (h.pow_left 2).mul_left (ht.add_left ((hb.mul_left h).smul_left (2:ℂ)))
private theorem coefficient_pair (i j : Fin 2) (m ell : ℕ) :
    GaussCoframeForm.Paired (profileCore m ell i j) (profileCore m ell i j) := by
  have hs := phi_S_pair
  have hb := phi_first_pair m ell
  have ht := phi_theta_pair m ell
  have hbs := first_commute (Commute.refl S) m ell
  have hst := (theta_commute (Commute.refl S) m ell).symm
  have hbsPair := phi_pair_mul hb hs hbs
  have hSbs : Commute S (B m ell*S) := hbs.symm.mul_right (Commute.refl S)
  fin_cases i <;> fin_cases j
  · exact phi_pair_sub (phi_pair_real 2 hbsPair) ht
  · change GaussCoframeForm.Paired (((-2:ℂ) • (S*(B m ell*S))):End)
      (((-2:ℂ) • (S*(B m ell*S))):End)
    simpa only [Complex.ofReal_neg,Complex.ofReal_ofNat] using
      phi_pair_real (-2:ℝ) (phi_pair_mul (A:=S) (B:=B m ell*S) hs hbsPair hSbs)
  · change GaussCoframeForm.Paired (((-2:ℂ) • (S*(B m ell*S))):End)
      (((-2:ℂ) • (S*(B m ell*S))):End)
    simpa only [Complex.ofReal_neg,Complex.ofReal_ofNat] using
      phi_pair_real (-2:ℝ) (phi_pair_mul (A:=S) (B:=B m ell*S) hs hbsPair hSbs)
  · exact phi_pair_mul (phi_pair_pow hs 2) (phi_pair_add ht (phi_pair_real 2 hbsPair))
      ((hst.pow_left 2).add_right ((hSbs.pow_left 2).smul_right (2:ℂ)))
private theorem profile_pair (i j : Fin 2) (m ell : ℕ) :
    GaussCoframeForm.Paired (profile i j m ell) (profile i j m ell) := by
  have hc := coefficient_commute (theta_commute (Commute.refl S) m ell).symm i j m ell
  exact phi_pair_mul (coefficient_pair i j m ell) (phi_theta_pair m ell) hc
private theorem profile_symmetric (i j : Fin 2) (m ell : ℕ) :
    profile i j m ell=profile j i m ell := by fin_cases i <;> fin_cases j <;> rfl
private theorem U_S_commute : Commute U S := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (SourcePhysicalKineticSquare.reciprocalVolume z:ℂ) (phiReciprocal z:ℂ) (f z)
private theorem profile_US_commute (i j : Fin 2) (m ell : ℕ) : Commute (profile i j m ell) (U*S) := by
  have hs : Commute S (U*S) := U_S_commute.symm.mul_right (Commute.refl S)
  exact (coefficient_commute hs i j m ell).mul_left (theta_commute hs m ell)
private theorem US_pair (p q : QuantumTest) : sourcePair ((U*S) p) q=sourcePair p ((U*S) q) := by
  exact (phi_pair_mul (multiply_pair _ _) (multiply_pair _ _) U_S_commute p q).symm
private abbrev Ephi : End := SourceScalarVirialBulk.phiEulerAction
private theorem euler_U : Commute Ephi U := by
  have h := SourceScalarInverseBulk.inverse_phi
  change Ephi*U-U*Ephi=0 at h
  exact sub_eq_zero.mp h
private theorem inverse_radius : S*phiRadiusAction=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse : phiRadiusAction*S=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiRadius z:ℂ) • ((phiReciprocal z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,mul_inv_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem euler_S : bracket Ephi S=S^3-S := by
  have hr : bracket Ephi phiRadiusAction=phiRadiusAction-S := original_phi_euler_radius
  have hi : bracket Ephi S= -(S*bracket Ephi phiRadiusAction*S) := by
    have h1 : S*Ephi*phiRadiusAction*S=S*Ephi := by
      calc _=S*Ephi*(phiRadiusAction*S) := by noncomm_ring
           _=_ := by rw [radius_inverse,mul_one]
    have h2 : S*phiRadiusAction*Ephi*S=Ephi*S := by rw [inverse_radius,one_mul]
    calc _= -(S*Ephi*phiRadiusAction*S-S*phiRadiusAction*Ephi*S) := by rw [h1,h2];unfold bracket;abel
         _=_ := by unfold bracket;noncomm_ring
  rw [hi,hr]
  calc _= -((S*phiRadiusAction)*S)+S^3 := by noncomm_ring
       _=_ := by rw [inverse_radius,one_mul];abel
private theorem euler_US : bracket Ephi (U*S)=U*(S^3-S) := by
  have hp : bracket Ephi (U*S)=bracket Ephi U*S+U*bracket Ephi S := by unfold bracket;noncomm_ring
  rw [hp,show bracket Ephi U=0 from sub_eq_zero.mpr euler_U.eq,euler_S,zero_mul,zero_add]
private theorem adjoint_profile_operator (i j : Fin 2) (m ell : ℕ) :
    Ephi*(U*S)*profile i j m ell+(61:ℂ) • ((U*S)*profile i j m ell)=
      profile i j m ell*(U*S*Ephi)+U*zeroProfile i j m ell := by
  have hu := euler_US
  have he := (profile_US_commute i j m ell).eq
  change Ephi*(U*S)*profile i j m ell+(61:ℂ) • ((U*S)*profile i j m ell)=
    profile i j m ell*(U*S*Ephi)+U*(S*bracket Ephi (profile i j m ell)+
      ((60:ℂ) • S+S^3)*profile i j m ell)
  unfold bracket at hu ⊢
  linear_combination (norm := (noncomm_ring;module)) hu*profile i j m ell-he*Ephi


private theorem abel_pair (μ : ℝ) (hμ : 0<μ) (F : Index) (p q : QuantumTest) :
    sourcePair (A μ F p) q=sourcePair p (A μ F q) := by
  have h := ((ContinuousLinearMap.nonneg_iff_isPositive _).mp
    (SourceBoundedClockAbel.actual_bounded_clock_abel_source μ hμ F).2.1).isSymmetric
  change inner ℂ (embed (A μ F p)) (embed q)=inner ℂ (embed p) (embed (A μ F q))
  rw [BoundedClockNativeCore.abelCore_embed μ hμ F,BoundedClockNativeCore.abelCore_embed μ hμ F]
  exact h _ _
private theorem radial_adjoint_profile_pair (i j : Fin 2) (m ell : ℕ) (p q : QuantumTest) :
    sourcePair (radialGenerator p) (profile i j m ell q)=
      sourcePair p (profile i j m ell (radialGenerator q))+
        (Complex.I/4:ℂ)*sourcePair p (U (zeroProfile i j m ell q)) := by
  have hr := ClockPhiNativeRadialContraction.original_native_radial_pair (profile i j m ell q) p
  rw [ClockPhiNativeRadialContraction.original_native_radial_contraction] at hr
  change sourcePair (profile i j m ell q) (radialGenerator p)=
    (Complex.I/4:ℂ)*(-sourcePair (Ephi ((U*S) (profile i j m ell q))) p-
      (61:ℂ)*sourcePair ((U*S) (profile i j m ell q)) p) at hr
  have hs := congrArg (starRingEnd ℂ) hr
  simp only [map_mul,map_sub,map_neg,map_div₀,map_ofNat,Complex.conj_I,GaussNativeForm.pair_conjugate] at hs
  have ho := congrArg (sourcePair p) (LinearMap.congr_fun (adjoint_profile_operator i j m ell) q)
  simp only [LinearMap.add_apply,LinearMap.smul_apply,Module.End.mul_apply,sourcePair,
    map_add,map_smul,inner_add_right,inner_smul_right] at ho
  change sourcePair (radialGenerator p) (profile i j m ell q)=
    sourcePair p (profile i j m ell ((Complex.I/4:ℂ) • ((U*S) (Ephi q))))+
      (Complex.I/4:ℂ)*sourcePair p (U (zeroProfile i j m ell q))
  simp only [map_smul,sourcePair,inner_smul_right,Module.End.mul_apply] at hs ⊢
  linear_combination (norm:=ring) hs+(Complex.I/4:ℂ)*ho
private def commWord (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  (2*n*μ)*(∑i:Fin 2,∑j:Fin 2,sourcePair (radialGenerator (sourceState i F z hz g))
    (bracket (profile i j m ell) (A μ F) (sourceState j F z hz g))).im
private def sourceFrameHalf (m ell : ℕ) (μ : ℝ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) : ℝ :=
  (2*n*μ)*(∑i:Fin 2,∑a:ScalarIndex,inner ℂ (nativeInput a i F z hz g)
    (∑j:Fin 2, (phiDirectionOperator (scalarBasis a)*SourceBoundedClockAbel.abelObservable μ F-
      SourceBoundedClockAbel.abelObservable μ F*phiDirectionOperator (scalarBasis a))
      (profileOp i j m ell (embed (sourceState j F z hz g))))).im
private theorem bracket_product (X Y A : End) : bracket (X*Y) A=X*bracket Y A+bracket X A*Y := by
  unfold bracket;noncomm_ring
private theorem frame_embed (μ : ℝ) (hμ : 0<μ) (F : Index) (a : ScalarIndex) (p : QuantumTest) :
    embed (bracket (D a) (A μ F) p)=
      (phiDirectionOperator (scalarBasis a)*SourceBoundedClockAbel.abelObservable μ F-
      SourceBoundedClockAbel.abelObservable μ F*phiDirectionOperator (scalarBasis a)) (embed p) := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  rw [←original_phi_direction_core,BoundedClockNativeCore.abelCore_embed μ hμ F,
    BoundedClockNativeCore.abelCore_embed μ hμ F,←original_phi_direction_core]
  rfl
private theorem column_commutator_embed (μ : ℝ) (hμ : 0<μ) (F : Index) (a : ScalarIndex)
    (i j : Fin 2) (m ell : ℕ) (p : QuantumTest) :
    embed (bracket (E a i j m ell) (A μ F) p)=
      SourceClockPhiNativeJointPayment.nativeColumn a i j m ell
        (SourceBoundedClockAbel.abelObservable μ F (embed p))-
      SourceBoundedClockAbel.abelObservable μ F
        (SourceClockPhiNativeJointPayment.nativeColumn a i j m ell (embed p)) := by
  simp only [bracket,LinearMap.sub_apply,Module.End.mul_apply,map_sub]
  have he (q : QuantumTest) : embed (E a i j m ell q)=
      SourceClockPhiNativeJointPayment.nativeColumn a i j m ell (embed q) :=
    (SourceClockPhiNativeJointPayment.actual_native_column_core a i j m ell q).symm
  rw [he,BoundedClockNativeCore.abelCore_embed μ hμ F,
    BoundedClockNativeCore.abelCore_embed μ hμ F,he]
private theorem native_comm_word (μ : ℝ) (hμ : 0<μ) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    SourceClockAbelNativeCurvature.nativePi m ell μ F z hz g+
      SourceClockAbelNativeRadialPayment.radialHalf m ell μ F z hz g=
      commWord m ell μ F z hz g := by
  have hC := SourceClockAbelNativeCurvature.actual_native_curvature_return μ hμ m ell F z hz g
  have hR := SourceClockAbelNativeRadialPayment.actual_native_radial_return μ hμ m ell F z hz g
  change SourceClockAbelNativeCurvature.curvatureHalf m ell μ F z hz g=
    SourceClockAbelNativeRadialPayment.radialHalf m ell μ F z hz g+sourceFrameHalf m ell μ F z hz g at hR
  have hH : SourceClockPhiNativeJointPayment.nativeHalf m ell μ F z hz g=
      commWord m ell μ F z hz g+sourceFrameHalf m ell μ F z hz g := by
    let X : Fin 2 → QuantumTest := fun i=>sourceState i F z hz g
    have hr : (∑a:ScalarIndex,D a*L a)=radialGenerator :=
      ClockPhiNativeRadialContraction.original_native_radial_contraction
    have hrow (i j : Fin 2) : (∑a:ScalarIndex,sourcePair (L a (X i))
        (bracket (E a i j m ell) (A μ F) (X j)))=
        sourcePair (radialGenerator (X i)) (bracket (profile i j m ell) (A μ F) (X j))+
        ∑a:ScalarIndex,sourcePair (L a (X i))
          (bracket (D a) (A μ F) (profile i j m ell (X j))) := by
      simp_rw [source_column_profile,bracket_product]
      simp only [LinearMap.add_apply,Module.End.mul_apply,sourcePair,map_add,inner_add_right,
        Finset.sum_add_distrib]
      congr 1
      rw [←hr]
      simp only [LinearMap.sum_apply,Module.End.mul_apply,map_sum,sum_inner]
      apply Finset.sum_congr rfl;intro a _
      exact multiply_pair _ _ _ _
    have hswap (Y : Fin 2 → Fin 2 → ScalarIndex → ℂ) :
        (∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,Y i j a)=∑i:Fin 2,∑a:ScalarIndex,∑j:Fin 2,Y i j a := by
      apply Finset.sum_congr rfl;intro i _;exact Finset.sum_comm
    have hm : SourceClockPhiNativeJointPayment.nativeHalf m ell μ F z hz g=
        (2*n*μ)*(∑i:Fin 2,∑j:Fin 2,∑a:ScalarIndex,
          sourcePair (L a (X i)) (bracket (E a i j m ell) (A μ F) (X j))).im := by
      rw [hswap]
      unfold SourceClockPhiNativeJointPayment.nativeHalf
      congr 1
      apply congrArg Complex.im
      apply Finset.sum_congr rfl;intro i _
      apply Finset.sum_congr rfl;intro a _
      simp only [SourceClockPhiNativeJointPayment.columnCommutator,inner_sum]
      apply Finset.sum_congr rfl;intro j _
      change _=inner ℂ (embed (L a (X i))) (embed (bracket (E a i j m ell) (A μ F) (X j)))
      rw [column_commutator_embed μ hμ F]
      simp only [X,source_state_embed]
      rfl
    rw [hm]
    simp_rw [hrow]
    simp only [Finset.sum_add_distrib,Complex.add_im,mul_add]
    congr 1
    unfold sourceFrameHalf
    congr 1
    apply congrArg Complex.im
    rw [hswap]
    apply Finset.sum_congr rfl;intro i _
    apply Finset.sum_congr rfl;intro a _
    simp only [inner_sum]
    apply Finset.sum_congr rfl;intro j _
    change inner ℂ (embed (L a (X i)))
      (embed (bracket (D a) (A μ F) (profile i j m ell (X j))))=_
    rw [frame_embed μ hμ F,←profile_core]
    rfl
  linarith only [hC,hR,hH]


private theorem complex_radial_phase (r y x b : ℂ) (n μ : ℝ)
    (hr : r=starRingEnd ℂ x+(Complex.I/4:ℂ)*b) :
    (2*n*μ)*(r-y).im= -(2*n*μ)*(x-y).im-(4*n*μ)*y.im+(n*μ/2)*b.re := by
  rw [hr]
  simp only [Complex.sub_im,Complex.add_im,Complex.conj_im,Complex.mul_im]
  norm_num
  ring
private theorem radial_zero_reduction (μ : ℝ) (hμ : 0<μ) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    SourceClockAbelNativeRadialPayment.radialHalf m ell μ F z hz g=
      -commWord m ell μ F z hz g-ordinaryWord m ell μ F z hz g+zeroWord m ell μ F z hz g := by
  let X : Fin 2 → QuantumTest := fun i=>sourceState i F z hz g
  let x : ℂ := ∑i:Fin 2,∑j:Fin 2,sourcePair (radialGenerator (X i)) (profile i j m ell (A μ F (X j)))
  let y : ℂ := ∑i:Fin 2,∑j:Fin 2,sourcePair (radialGenerator (X i)) (A μ F (profile i j m ell (X j)))
  let b : ℂ := ∑i:Fin 2,∑j:Fin 2,sourcePair (A μ F (X i)) (U (zeroProfile i j m ell (X j)))
  let r : ℂ := ∑i:Fin 2,∑j:Fin 2,sourcePair (radialGenerator (A μ F (X i))) (profile i j m ell (X j))
  have hr : r=starRingEnd ℂ x+(Complex.I/4:ℂ)*b := by
    calc
      _=(∑i:Fin 2,∑j:Fin 2,sourcePair (A μ F (X i)) (profile i j m ell (radialGenerator (X j))))+
          (Complex.I/4:ℂ)*b := by
        dsimp only [r,b]
        simp_rw [radial_adjoint_profile_pair]
        simp only [Finset.sum_add_distrib,←Finset.mul_sum]
      _=_ := by
        congr 1
        dsimp only [x]
        simp only [map_sum,GaussNativeForm.pair_conjugate]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl;intro i _
        apply Finset.sum_congr rfl;intro j _
        rw [profile_symmetric j i m ell,profile_pair]
  have hrad : SourceClockAbelNativeRadialPayment.radialHalf m ell μ F z hz g=
      (2*n*μ)*(r-y).im := by
    change (2*n*μ)*(∑i:Fin 2,∑j:Fin 2,sourcePair
      ((radialGenerator*(A μ F)-(A μ F)*radialGenerator) (X i)) (profile i j m ell (X j))).im=_
    simp only [LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,inner_sub_left,
      Finset.sum_sub_distrib]
    have hy : (∑i:Fin 2,∑j:Fin 2,sourcePair (A μ F (radialGenerator (X i))) (profile i j m ell (X j)))=y := by
      simp only [abel_pair μ hμ F,y]
    change (2*n*μ)*(r-(∑i:Fin 2,∑j:Fin 2,sourcePair (A μ F (radialGenerator (X i)))
      (profile i j m ell (X j)))).im=_
    rw [hy]
  have hc : commWord m ell μ F z hz g=(2*n*μ)*(x-y).im := by
    simp only [commWord,bracket,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,map_sub,
      inner_sub_right,Finset.sum_sub_distrib]
    rfl
  rw [hrad,hc]
  simpa only [ordinaryWord,zeroWord,y,b,X,neg_mul] using complex_radial_phase r y x b n μ hr

/-- Full native derivative loss is replaced by one actual zero-order U matrix, before estimates. -/
theorem actual_native_zero_source (μ : ℝ) (hμ : 0<μ) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    SourceClockAbelNativeCurvature.nativePi m ell μ F z hz g=
      (4*n*μ)*(∑i:Fin 2,∑j:Fin 2,sourcePair (radialGenerator (sourceState i F z hz g))
        (profile i j m ell (A μ F (sourceState j F z hz g)))).im-zeroWord m ell μ F z hz g := by
  have hC := native_comm_word μ hμ m ell F z hz g
  have hR := radial_zero_reduction μ hμ m ell F z hz g
  have hI : 2*commWord m ell μ F z hz g+ordinaryWord m ell μ F z hz g=
      (4*n*μ)*(∑i:Fin 2,∑j:Fin 2,sourcePair (radialGenerator (sourceState i F z hz g))
        (profile i j m ell (A μ F (sourceState j F z hz g)))).im := by
    simp only [commWord,ordinaryWord,bracket,LinearMap.sub_apply,Module.End.mul_apply,sourcePair,
      map_sub,inner_sub_right,Finset.sum_sub_distrib,Complex.sub_im]
    ring
  linarith only [hC,hR,hI]
private theorem actual_zero_payment_return (μ : ℝ) (hμ : 0<μ) (m ell : ℕ) (F : Index)
    (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    SourceClockAbelNativeCurvature.nativePi m ell μ F z hz g+zeroWord m ell μ F z hz g=
      2*(SourceClockAbelNativeCurvature.nativePi m ell μ F z hz g+
        SourceClockAbelNativeRadialPayment.radialHalf m ell μ F z hz g)+ordinaryWord m ell μ F z hz g := by
  have hC := native_comm_word μ hμ m ell F z hz g
  have hR := radial_zero_reduction μ hμ m ell F z hz g
  linarith only [hC,hR]

/-- The zero-order source is the whole remaining word; both derivative slots are paid
by the original pressure debit and two actual fixed-seed theta tails. -/
theorem actual_native_zero_common_payment (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η : ℝ) (hη : 0<η) :
    ∀ε : ℝ,0 < ε → ∃ M : ℕ,∀m : ℕ,M ≤ m → ∀ell : ℕ,m ≤ ell →
      ∀ᶠ F in (sourceFilter:Filter Index),∀advanced : Bool,
      (∫⁻w:ℝ,ENNReal.ofReal (|SourceClockAbelNativeCurvature.nativePi m ell μ F
          (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
        zeroWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  let c : ℝ := 144*n*μ^2/(η/2)
  have hc : 0<c := by dsimp only [c];have hn:=lapse_pos;positivity
  obtain ⟨M₀,h₀⟩ := SourceClockAbelNativeRadialPayment.actual_native_radial_common_payment μ hμ g
    (η/4) (by positivity) (ε/4) (by positivity)
  obtain ⟨M₁,h₁⟩ := error_common_tail μ hμ g (ε/(2*c)) (by positivity)
  refine ⟨max M₀ M₁,fun m hm ell hml=>?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hC hE
  intro advanced
  let price : ℝ → ℝ := fun w=>
    |SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g+
      SourceClockAbelNativeRadialPayment.radialHalf m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g|-
      (η/4)*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g
  have hpoint (w : ℝ) :
      ENNReal.ofReal (|SourceClockAbelNativeCurvature.nativePi m ell μ F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g+
        zeroWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g|-
        η*SourceClockPhiNativeJointPayment.nativePressureDebit F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g) ≤
        ENNReal.ofReal c*ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)+ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (price w) := by
    have hreturn := actual_zero_payment_return μ hμ m ell F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g
    have hordinary := ordinary_point_price m ell μ hμ F (actualFrequency advanced μ w)
      (frequency_nonreal advanced μ hμ w) g (η/2) (by positivity)
    have htriangle := abs_add_le (2*(SourceClockAbelNativeCurvature.nativePi m ell μ F
      (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g+
      SourceClockAbelNativeRadialPayment.radialHalf m ell μ F (actualFrequency advanced μ w)
        (frequency_nonreal advanced μ hμ w) g))
      (ordinaryWord m ell μ F (actualFrequency advanced μ w) (frequency_nonreal advanced μ hμ w) g)
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at htriangle
    calc _ ≤ ENNReal.ofReal (c*errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g+2*price w) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hreturn]
          dsimp only [price,c]
          linarith only [hordinary,htriangle]
         _ ≤ ENNReal.ofReal (c*errorEnergy m ell F (actualFrequency advanced μ w)
              (frequency_nonreal advanced μ hμ w) g)+ENNReal.ofReal (2*price w) := ENNReal.ofReal_add_le
         _ = _ := by rw [ENNReal.ofReal_mul hc.le,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  calc _ ≤ ∫⁻w:ℝ,ENNReal.ofReal c*ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g)+ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (price w) := lintegral_mono hpoint
       _ = ENNReal.ofReal c*(∫⁻w:ℝ,ENNReal.ofReal (errorEnergy m ell F (actualFrequency advanced μ w)
          (frequency_nonreal advanced μ hμ w) g))+ENNReal.ofReal (2:ℝ)*(∫⁻w:ℝ,ENNReal.ofReal (price w)) := by
          rw [lintegral_add_left ((error_measurable m ell μ hμ advanced F g).const_mul _),
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
       _ ≤ ENNReal.ofReal c*ENNReal.ofReal (ε/(2*c))+ENNReal.ofReal (2:ℝ)*ENNReal.ofReal (ε/4) :=
          add_le_add (mul_le_mul le_rfl (hE advanced) zero_le zero_le)
            (mul_le_mul le_rfl (hC advanced) zero_le zero_le)
       _ = ENNReal.ofReal ε := by
          rw [←ENNReal.ofReal_mul hc.le,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
            ←ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          field_simp
          ring

end LowEnergy.SourceClockAbelWholePhiZeroOrder
