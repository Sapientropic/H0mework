import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockPhiRadiusResponseHessian
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiCombinedScalePressure

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockPhiFixedSourceJets
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential GaussDiagonalHistory
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceClockPhiRadiusSourceCurrent SourceClockRadiusAffineCutoff SourceClockPhiRadiusResponseHessian
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourcePhysicalKineticSquare
open scoped ContDiff InnerProductSpace
abbrev End:=QuantumTest →ₗ[ℂ] QuantumTest
private abbrev H0:End:=diagonalAction
private abbrev S:End:=phiInverseAction
private abbrev r:End:=phiRadiusAction
private abbrev U:End:=inverseVolumeAction
private abbrev W:End:=multiply scalarWeight scalarWeight_smooth
private abbrev P(i:ScalarIndex):End:=covariantMomentum (scalarDirection i)
private abbrev Pa(i:ScalarIndex):End:=GaussMomentumAdjoint.adjoint (scalarDirection i)
private abbrev d(i:ScalarIndex):End:=phiDirectionAction (scalarBasis i)
private abbrev Q:End:=1-S
private abbrev n:ℝ:=sourceTime 0
attribute [local irreducible] diagonalAction sourcePair embed

def inverseCurrent:End:=bracket H0 S
def inverseDoubleCurrent:End:=((n:ℂ)/4) • (U*(S^4-S^6))

private theorem real_commute(c b:SourceCoordinateSlice → ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    Commute (multiply c hc) (multiply b hb) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  exact smul_comm (c z:ℂ) (b z:ℂ) (f z)
private theorem product_bracket(A B C:End):bracket (A*B) C=A*bracket B C+bracket A C*B := by
  unfold bracket
  noncomm_ring
private theorem bracket_product(A B C:End):bracket A (B*C)=bracket A B*C+B*bracket A C := by
  unfold bracket
  noncomm_ring
private theorem bracket_add(A B C:End):bracket (A+B) C=bracket A C+bracket B C := by
  unfold bracket
  noncomm_ring
private theorem bracket_smul(c:ℂ)(A B:End):bracket (c • A) B=c • bracket A B := by
  unfold bracket
  simp only [smul_mul_assoc,mul_smul_comm,smul_sub]
private theorem bracket_sum{ι:Type*}[Fintype ι](v:ι → End)(B:End):
    bracket (∑i,v i) B=∑i,bracket (v i) B := by
  simp only [bracket,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
private theorem inverse_radius:S*r=(1:End) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (phiReciprocal z:ℂ) • ((phiRadius z:ℂ) • f z)=f z
  rw [smul_smul,phiReciprocal,Complex.ofReal_inv,inv_mul_cancel₀,one_smul]
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (by positivity)).ne'
private theorem radius_inverse:r*S=(1:End):=(real_commute _ _ _ _).eq.symm.trans inverse_radius
private theorem inverse_bracket(X:End):bracket X S= -(S*bracket X r*S) := by
  have h1:S*X*r*S=S*X := by rw [mul_assoc,radius_inverse,mul_one]
  have h2:S*r*X*S=X*S := by rw [inverse_radius,one_mul]
  unfold bracket
  linear_combination (norm:=noncomm_ring) h1-h2
private theorem phi_square(z:SourceCoordinateSlice):(phiRadius z)^2=1+‖scalarField z‖^2/4 := by
  exact Real.sq_sqrt (by positivity)
private theorem direction_square(z:SourceCoordinateSlice):
    (∑i:ScalarIndex,(phiDirectionWeight (scalarBasis i) z)^2)=(1-phiReciprocal z^2)/4 := by
  simp only [phiDirectionWeight,div_pow,neg_sq]
  rw [←Finset.sum_div,scalarBasis.sum_sq_inner_left]
  have h:=phi_square z
  have hp:phiRadius z≠0:= (Real.sqrt_pos.2 (by positivity)).ne'
  unfold phiReciprocal
  field_simp [hp]
  nlinarith only [h]
private theorem direction_square_end:(∑i:ScalarIndex,d i*d i)=(1/4:ℂ) • (1-S^2) := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  simp only [LinearMap.sum_apply,Module.End.mul_apply,sum_apply,LinearMap.smul_apply,LinearMap.sub_apply,
    Module.End.one_apply,pow_two]
  change (∑i:ScalarIndex,(phiDirectionWeight (scalarBasis i) z:ℂ) •
      ((phiDirectionWeight (scalarBasis i) z:ℂ) • f z))=
    (1/4:ℂ) • (f z-(phiReciprocal z:ℂ) • ((phiReciprocal z:ℂ) • f z))
  simp only [smul_smul,←pow_two,←Complex.ofReal_pow,←Finset.sum_smul,←Complex.ofReal_sum]
  rw [direction_square]
  have he:(((1-phiReciprocal z^2)/4:ℝ):ℂ)=(1/4:ℂ)-(1/4:ℂ)*(phiReciprocal z:ℂ)^2 := by push_cast;ring
  rw [he]
  module
private theorem scalar_weight:W=(-(n:ℂ)) • U := by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (scalarWeight z:ℂ) • f z=(-(n:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem radius_double:bracket phiRadiusCurrent r=((n:ℂ)/4) • (U*(1-S^2)) := by
  have hrow(i:ScalarIndex):bracket (Pa i*W*d i+d i*W*P i) r=(2*Complex.I:ℂ) • (W*(d i*d i)) := by
    have hp:bracket (P i) r=Complex.I • d i:=(original_phi_radius_native_jet (scalarDirection i)).1
    have ha:bracket (Pa i) r=Complex.I • d i:=(original_phi_radius_native_jet (scalarDirection i)).2
    have hw:bracket W r=0:=sub_eq_zero.mpr (real_commute _ _ _ _).eq
    have hd:bracket (d i) r=0:=sub_eq_zero.mpr (real_commute _ _ _ _).eq
    have hwd:Commute W (d i):=real_commute _ _ _ _
    have he:d i*W*d i=W*(d i*d i) := by rw [hwd.symm.eq,mul_assoc]
    rw [bracket_add]
    simp only [product_bracket,hp,ha,hw,hd,mul_zero,zero_mul,zero_add,add_zero,
      smul_mul_assoc,mul_smul_comm,he]
    module
  change bracket ((Complex.I/2:ℂ) • ∑i:ScalarIndex,(Pa i*W*d i+d i*W*P i)) r=_
  rw [bracket_smul,bracket_sum]
  simp_rw [hrow]
  rw [←Finset.smul_sum,smul_smul]
  have hi:(Complex.I/2)*(2*Complex.I)=(-1:ℂ) := by
    calc _=Complex.I*Complex.I := by ring
         _=_ := Complex.I_mul_I
  rw [hi,←Finset.mul_sum,direction_square_end,scalar_weight]
  simp only [mul_smul_comm,smul_mul_assoc,smul_smul]
  module

/-- The full original H0 generates its actual inverse-radius double current. -/
theorem actual_inverse_double_current:bracket inverseCurrent S=inverseDoubleCurrent := by
  unfold inverseCurrent
  rw [inverse_bracket H0,original_phi_radius_hamiltonian_current]
  have he:bracket (-(S*phiRadiusCurrent*S)) S= -(S*bracket phiRadiusCurrent S*S) := by
    unfold bracket
    noncomm_ring
  rw [he,inverse_bracket phiRadiusCurrent,radius_double]
  have hu:Commute U S:=real_commute _ _ _ _
  have hpoly:S^2*U*(1-S^2)*S^2=U*(S^4-S^6) := by
    rw [(hu.symm.pow_left 2).eq]
    noncomm_ring
  simp only [mul_neg,neg_mul,neg_neg,mul_smul_comm,smul_mul_assoc]
  unfold inverseDoubleCurrent
  congr 1

private theorem double_commutes:Commute inverseDoubleCurrent S := by
  unfold inverseDoubleCurrent
  have hu:Commute U S:=real_commute _ _ _ _
  have hp:Commute (S^4-S^6) S:=((Commute.refl S).pow_left 4).sub_left ((Commute.refl S).pow_left 6)
  exact (hu.mul_left hp).smul_left _
/-- The third S commutator vanishes because the generated double current is a real multiplier. -/
theorem actual_inverse_third_current_zero:bracket inverseDoubleCurrent S=0 :=
  sub_eq_zero.mpr double_commutes.eq

private theorem power_high_formula(X C B:End)(hC:bracket H0 X=C)(hB:bracket C X=B)
    (hBX:Commute B X)(k:ℕ):
    bracket H0 (X^(k+2))=(k+2:ℂ) • (X^(k+1)*C)+
      ((k+1:ℂ)*(k+2:ℂ)/2) • (X^k*B) := by
  have hCX:C*X=X*C+B := by unfold bracket at hB;linear_combination (norm:=noncomm_ring) hB
  have hXC(m:ℕ):X^m*C*X=X^(m+1)*C+X^m*B := by
    rw [mul_assoc,hCX,mul_add,←mul_assoc,←pow_succ]
  have hXB(m:ℕ):X^m*B*X=X^(m+1)*B := by rw [mul_assoc,hBX.eq,←mul_assoc,←pow_succ]
  induction k with
  | zero =>
    rw [show (0+2:ℕ)=1+1 by rfl,pow_succ,bracket_product,hC]
    simp only [pow_one,pow_zero,one_mul]
    rw [hC,hCX]
    norm_num
    module
  | succ k ih =>
    have he:(k+1+2:ℕ)=k+2+1:=by omega
    rw [he,pow_succ,bracket_product,ih,hC]
    simp only [add_mul,smul_mul_assoc,hXC,hXB]
    push_cast
    module

/-- Every inverse-radius power consumes the source-generated double current. -/
theorem actual_inverse_power_hamiltonian_source(k:ℕ):
    bracket H0 (S^(k+1))=(k+1:ℂ) • (S^k*inverseCurrent)+
      ((k:ℂ)*(k+1:ℂ)/2) • (S^(k-1)*inverseDoubleCurrent) := by
  have hC:bracket H0 S=inverseCurrent:=rfl
  cases k with
  | zero => simpa [pow_one,pow_zero] using hC
  | succ k =>
    have h:=power_high_formula S inverseCurrent inverseDoubleCurrent hC
      actual_inverse_double_current double_commutes k
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_assoc,
      show (1:ℂ)+1=2 by norm_num] using h

/-- Full-H0 polynomial cutoff current, including the actual second S derivative. -/
theorem actual_phi_cutoff_power_hamiltonian_source(k:ℕ):
    bracket H0 (Q^(k+1))= -(k+1:ℂ) • (Q^k*inverseCurrent)+
      ((k:ℂ)*(k+1:ℂ)/2) • (Q^(k-1)*inverseDoubleCurrent) := by
  have hC:bracket H0 Q= -inverseCurrent := by unfold inverseCurrent Q bracket;noncomm_ring
  have hB:bracket (-inverseCurrent) Q=inverseDoubleCurrent := by
    have h:=actual_inverse_double_current
    unfold Q bracket at h ⊢
    linear_combination (norm:=noncomm_ring) h
  have hBQ:Commute inverseDoubleCurrent Q:=(Commute.one_right _).sub_right double_commutes
  cases k with
  | zero => simpa [pow_one,pow_zero] using hC
  | succ k =>
    have h:=power_high_formula Q (-inverseCurrent) inverseDoubleCurrent hC hB hBQ k
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,mul_neg,smul_neg,neg_smul,add_assoc,
      show (1:ℂ)+1=2 by norm_num] using h

/-- The actual theta word has precisely its first and second polynomial source jets. -/
theorem actual_phi_theta_hamiltonian_source(m ell:ℕ):
    bracket H0 (phiThetaAction m ell)=phiFirstPeak m ell*inverseCurrent+
      (1/2:ℂ) • (phiSecondPeak m ell*inverseDoubleCurrent) := by
  have hm:=actual_phi_cutoff_power_hamiltonian_source m
  have hl:=actual_phi_cutoff_power_hamiltonian_source ell
  have hs:bracket H0 (Q^(m+1)-Q^(ell+1))=bracket H0 (Q^(m+1))-bracket H0 (Q^(ell+1)) := by
    unfold bracket
    noncomm_ring
  change bracket H0 (Q^(m+1)-Q^(ell+1))=_
  rw [hs,hm,hl]
  unfold phiFirstPeak phiSecondPeak
  simp only [sub_mul,smul_mul_assoc]
  module

end LowEnergy.SourceClockPhiFixedSourceJets
