import H0mework.Versions.AC.Physics.LowEnergy.AlphaSource.CanonicalPreparationActualMixedPhysicalWords

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumActualPreparedMixed
open GaussCoreHilbert GaussComposite CanonicalGradedMixed CanonicalGradedMixedSource
open CanonicalGradedSpatialKernel CanonicalGradedSpatialSource CanonicalPhysicalSpatial
open FullYSourceCutoffVolterra SourceFamilyOperator
open GaussUnitaryHistory (Index HistorySpace sourceFilter reader inclusion)
open GaussComposite.SourceGraph
open MeasureTheory Set Filter
open scoped BigOperators Topology InnerProductSpace Interval
local instance : NormedAlgebra ℝ Op := NormedAlgebra.restrictScalars ℝ ℂ _
local instance : SecondCountableTopologyEither ℝ Op := ⟨Or.inl inferInstance⟩

abbrev ScalarIndex := SourceScalarFock.ScalarIndex

def bandNorm (a : ScalarIndex) (A : NativeCurrent) : ℝ := ∑ i,‖actualBand a A i‖
theorem bandNorm_nonnegative (a : ScalarIndex) (A : NativeCurrent) : 0 ≤ bandNorm a A :=
  Finset.sum_nonneg (fun _ _=>norm_nonneg _)

def timeSize (r s t : ℝ) : ℝ := 1+|r|+|s|+|t|

theorem pathBound_square (cut : ℕ) (a b : ℤ) (ha : -1 ≤ a) (hb : -1 ≤ b) (r s t : ℝ) :
    CanonicalGradedMixedReturn.pathBound cut a b r s t ≤
      27*(timeSize r s t*(1+‖cutoff cut‖))^2 := by
  let Q := timeSize r s t*(1+‖cutoff cut‖)
  have size : 1 ≤ timeSize r s t := by unfold timeSize;linarith [abs_nonneg r,abs_nonneg s,abs_nonneg t]
  have one : 1 ≤ Q := one_le_mul_of_one_le_of_one_le size (by linarith [norm_nonneg (cutoff cut)])
  have rr : |r| *‖cutoff cut‖ ≤ Q := by unfold Q timeSize; nlinarith [abs_nonneg r,abs_nonneg s,abs_nonneg t,norm_nonneg (cutoff cut)]
  have ss : |s| *‖cutoff cut‖ ≤ Q := by unfold Q timeSize; nlinarith [abs_nonneg r,abs_nonneg s,abs_nonneg t,norm_nonneg (cutoff cut)]
  have tt : |t| *‖cutoff cut‖ ≤ Q := by unfold Q timeSize; nlinarith [abs_nonneg r,abs_nonneg s,abs_nonneg t,norm_nonneg (cutoff cut)]
  have bound (i j k : ℕ) :
      (if (i:ℤ)+a+j+b+k=0 then (|r| *‖cutoff cut‖)^i*(|s| *‖cutoff cut‖)^j*(|t| *‖cutoff cut‖)^k else 0) ≤ Q^2 := by
    split_ifs with balance
    · have degree : i+j+k ≤ 2 := by omega
      calc
        _  ≤  Q^i*Q^j*Q^k := by gcongr
        _ = Q^(i+j+k) := by rw [pow_add,pow_add]
        _  ≤  Q^2 := pow_le_pow_right₀ one degree
    · positivity
  unfold CanonicalGradedMixedReturn.pathBound
  calc
    _  ≤  ∑ i∈Finset.range 3,∑ j∈Finset.range 3,∑ k∈Finset.range 3,Q^2 :=
      Finset.sum_le_sum (fun i _=>Finset.sum_le_sum (fun j _=>Finset.sum_le_sum (fun k _=>bound i j k)))
    _ = _ := by norm_num;ring

theorem fullReaderWord_bound (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (out middle input : PhysicalMomentum) (r s t : ℝ) (F : Index) :
    ‖fullWord cut (actualReader a A) (actualReader b B) out middle input r s t F‖ ≤
      27*bandNorm a A*bandNorm b B*(timeSize r s t*(1+‖cutoff cut‖))^2 := by
  rw [actual_reader_paths]
  calc
    _  ≤  ∑ i : Fin 3,∑ j : Fin 3,‖actualBand a A i‖*‖actualBand b B j‖*
        (27*(timeSize r s t*(1+‖cutoff cut‖))^2) := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      exact (selectedWord_bound cut _ _ _ _ out middle input r s t F).trans
        (mul_le_mul_of_nonneg_left (pathBound_square cut _ _ (bandGrade_lower i) (bandGrade_lower j) r s t)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    _ = _ := by
      unfold bandNorm
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

def finiteMixedKernel (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (t s : ℝ) (F : Index) : Op :=
  Complex.I • (fullWord cut (actualReader b B) (actualReader a A)
    (p+k+ell) (p+k) p (-s) (s-t) t F-
    fullWord cut (actualReader a A) (actualReader b B) (p+k+ell) (p+ell) p (-t) (t-s) s F)

theorem finiteMixedKernel_literal (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (t s : ℝ) (F : Index) :
    finiteMixedKernel cut a b A B p k ell t s F=
      gradeZeroProjection*CanonicalGradedBilocal.kernel
        (compression (p+k+ell) F+cutoff cut) (compression p F+cutoff cut)
        (compression (p+ell) F+cutoff cut) (compression (p+k) F+cutoff cut)
        (actualReader a A) (actualReader b B) t s*gradeZeroProjection := by
  simp only [finiteMixedKernel,fullWord,CanonicalGradedBilocal.kernel,CanonicalGradedBilocal.ordered,
    mul_smul_comm,smul_mul_assoc,mul_sub,sub_mul,mul_assoc]

def kernelScale (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent) (age : ℝ) : ℝ :=
  216*bandNorm a A*bandNorm b B*(1+|age|)^2*(1+‖cutoff cut‖)^2

theorem kernelScale_nonnegative (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent) (age : ℝ) :
    0 ≤ kernelScale cut a b A B age := by
  unfold kernelScale
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (bandNorm_nonnegative a A))
    (bandNorm_nonnegative b B)) (sq_nonneg _)) (sq_nonneg _)

theorem timeSize_lag (age lag : ℝ) (hlag : 0 ≤ lag) :
    timeSize (-(age+lag)) (age+lag-age) age ≤ 2*(1+|age|)*(1+lag) ∧
    timeSize (-age) (age-(age+lag)) (age+lag) ≤ 2*(1+|age|)*(1+lag) := by
  have bound:=abs_add_le age lag
  rw [abs_of_nonneg hlag] at bound
  have polynomial : 1+2*|age|+2*lag ≤ 2*(1+|age|)*(1+lag) := by
    nlinarith only [mul_nonneg (abs_nonneg age) hlag]
  constructor
  · change 1+|-(age+lag)|+|age+lag-age|+|age| ≤ _
    rw [abs_neg,add_sub_cancel_left,abs_of_nonneg hlag]
    exact (show 1+|age+lag|+lag+|age| ≤ 1+2*|age|+2*lag by linarith only [bound]).trans polynomial
  · change 1+|-age|+|age-(age+lag)|+|age+lag| ≤ _
    rw [abs_neg,show age-(age+lag) = -lag by ring,abs_neg,abs_of_nonneg hlag]
    exact (show 1+|age|+lag+|age+lag| ≤ 1+2*|age|+2*lag by linarith only [bound]).trans polynomial

theorem finiteMixedKernel_bound (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age lag : ℝ) (hlag : 0 ≤ lag) (F : Index) :
    ‖finiteMixedKernel cut a b A B p k ell (age+lag) age F‖ ≤
      kernelScale cut a b A B age*(1+lag)^2 := by
  have times:=timeSize_lag age lag hlag
  have forward:=fullReaderWord_bound cut a b A B (p+k+ell) (p+ell) p (-(age+lag)) (age+lag-age) age F
  have reverse:=fullReaderWord_bound cut b a B A (p+k+ell) (p+k) p (-age) (age-(age+lag)) (age+lag) F
  have fa : 0 ≤ bandNorm a A := bandNorm_nonnegative a A
  have fb : 0 ≤ bandNorm b B := bandNorm_nonnegative b B
  have one : 0 ≤ 1+‖cutoff cut‖ := by positivity
  have fbound : ‖fullWord cut (actualReader a A) (actualReader b B)
      (p+k+ell) (p+ell) p (-(age+lag)) (age+lag-age) age F‖ ≤
      27*bandNorm a A*bandNorm b B*(2*(1+|age|)*(1+lag)*(1+‖cutoff cut‖))^2 := by
    apply forward.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (by unfold timeSize;positivity) one)
        (mul_le_mul_of_nonneg_right times.1 one) 2)
      (mul_nonneg (mul_nonneg (by norm_num) fa) fb)
  have rbound : ‖fullWord cut (actualReader b B) (actualReader a A)
      (p+k+ell) (p+k) p (-age) (age-(age+lag)) (age+lag) F‖ ≤
      27*bandNorm b B*bandNorm a A*(2*(1+|age|)*(1+lag)*(1+‖cutoff cut‖))^2 := by
    apply reverse.trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (by unfold timeSize;positivity) one)
        (mul_le_mul_of_nonneg_right times.2 one) 2)
      (mul_nonneg (mul_nonneg (by norm_num) fb) fa)
  rw [finiteMixedKernel,norm_smul,Complex.norm_I,one_mul]
  apply (norm_sub_le _ _).trans
  apply (add_le_add rbound fbound).trans_eq
  unfold kernelScale
  ring


open SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace.Response

def dampedSquare (damping t : ℝ) : ℝ := Real.exp (-damping*t)*(1+t)^2

def squareTail (damping T : ℝ) : ℝ :=
  Real.exp (-damping*T)*((1+T)^2/damping+2*(1+T)/damping^2+2/damping^3)

theorem dampedSquare_integrable (damping : ℝ) (positive : 0<damping) :
    IntegrableOn (dampedSquare damping) (Ioi 0) := by
  have same : dampedSquare damping=(fun t=>Real.exp (-damping*t)*t^2+
      (Real.exp (-damping*t)*t^1)*2+Real.exp (-damping*t)*t^0) := by
    funext t;unfold dampedSquare;ring
  rw [same]
  exact ((damping_moment_integrable 2 damping positive).add
    ((damping_moment_integrable 1 damping positive).mul_const 2)).add
    (damping_moment_integrable 0 damping positive)

theorem squareTail_integral (damping T : ℝ) (positive : 0<damping) :
    (∫ t : ℝ in Ioi T,dampedSquare damping t)=squareTail damping T := by
  have shift:=integral_add_right_eq_self (μ:=volume) ((Ioi T).indicator (dampedSquare damping)) T
  rw [integral_indicator measurableSet_Ioi] at shift
  have identity : (fun t=>(Ioi T).indicator (dampedSquare damping) (t+T))=
      (Ioi 0).indicator (fun t=>dampedSquare damping (t+T)) := by
    funext t;simp only [indicator_apply,mem_Ioi,lt_add_iff_pos_left]
  rw [identity,integral_indicator measurableSet_Ioi] at shift
  rw [←shift]
  have polynomial (t : ℝ) : dampedSquare damping (t+T)=Real.exp (-damping*T)*
      (Real.exp (-damping*t)*t^2+Real.exp (-damping*t)*t^1*(2*(1+T))+
        Real.exp (-damping*t)*t^0*(1+T)^2) := by
    unfold dampedSquare
    rw [show -damping*(t+T)=-damping*T+(-damping*t) by ring,Real.exp_add]
    ring
  simp_rw [polynomial]
  have i2 := damping_moment_integrable 2 damping positive
  have i1 := (damping_moment_integrable 1 damping positive).mul_const (2*(1+T))
  have i0 := (damping_moment_integrable 0 damping positive).mul_const ((1+T)^2)
  have i21 : IntegrableOn (fun t=>Real.exp (-damping*t)*t^2+
      Real.exp (-damping*t)*t^1*(2*(1+T))) (Ioi 0) := i2.add i1
  rw [integral_const_mul,integral_add i21 i0,integral_add i2 i1,
    integral_mul_const,integral_mul_const,
    damping_moment_integral 2 damping positive,damping_moment_integral 1 damping positive,
    damping_moment_integral 0 damping positive]
  norm_num [squareTail,Nat.factorial,div_eq_mul_inv]
  ring

theorem squareTail_nonnegative (damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) :
    0 ≤ squareTail damping T := by unfold squareTail;positivity

@[fun_prop] theorem source_time_continuous (C : Op) : Continuous (SourceFiniteUnitary.time C) :=
  continuous_iff_continuousAt.mpr (fun t=>
    (hasDerivAt_exp_smul_const ((-Complex.I) • C) t).continuousAt)

theorem finiteMixedKernel_continuous (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age : ℝ) (F : Index) :
    Continuous (fun lag=>finiteMixedKernel cut a b A B p k ell (age+lag) age F) := by
  unfold finiteMixedKernel fullWord
  fun_prop

def mixedIntegrand (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping lag : ℝ) (F : Index) : Op :=
  CanonicalGradedFrequency.weight frequency damping lag •
    finiteMixedKernel cut a b A B p k ell (age+lag) age F

theorem mixedIntegrand_bound (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping lag : ℝ) (hlag : 0 ≤ lag) (F : Index) :
    ‖mixedIntegrand cut a b A B p k ell age frequency damping lag F‖ ≤
      dampedSquare damping lag*kernelScale cut a b A B age := by
  rw [mixedIntegrand,norm_smul,CanonicalGradedFrequency.weight_norm]
  exact (mul_le_mul_of_nonneg_left (finiteMixedKernel_bound cut a b A B p k ell age lag hlag F)
    (Real.exp_pos _).le).trans_eq (by unfold dampedSquare;ring)

theorem mixedIntegrand_integrable (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    IntegrableOn (fun lag=>mixedIntegrand cut a b A B p k ell age frequency damping lag F) (Ioi 0) := by
  apply ((dampedSquare_integrable damping positive).mul_const (kernelScale cut a b A B age)).mono'
    ((CanonicalGradedFrequency.weight_continuous frequency damping).smul
      (finiteMixedKernel_continuous cut a b A B p k ell age F)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
  exact mixedIntegrand_bound cut a b A B p k ell age frequency damping lag (le_of_lt hlag) F

def finiteMixedResponse (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (F : Index) : Op :=
  ∫ lag in Ioi 0,mixedIntegrand cut a b A B p k ell age frequency damping lag F

def finiteMixedTruncation (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (F : Index) : Op :=
  ∫ lag in (0:ℝ)..T,mixedIntegrand cut a b A B p k ell age frequency damping lag F

theorem finiteMixedResponse_bound (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) (F : Index) :
    ‖finiteMixedResponse cut a b A B p k ell age frequency damping F‖ ≤
      squareTail damping 0*kernelScale cut a b A B age := by
  have h:=norm_integral_le_of_norm_le
    ((dampedSquare_integrable damping positive).mul_const (kernelScale cut a b A B age))
    (show ∀ᵐ lag ∂volume.restrict (Ioi 0),
      ‖mixedIntegrand cut a b A B p k ell age frequency damping lag F‖ ≤
        dampedSquare damping lag*kernelScale cut a b A B age from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
      exact mixedIntegrand_bound cut a b A B p k ell age frequency damping lag (le_of_lt hlag) F)
  rw [integral_mul_const,squareTail_integral damping 0 positive] at h
  exact h

theorem finiteMixedResponse_tail (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ)
    (positive : 0<damping) (future : 0 ≤ T) (F : Index) :
    ‖finiteMixedResponse cut a b A B p k ell age frequency damping F-
        finiteMixedTruncation cut a b A B p k ell age frequency damping T F‖ ≤
      squareTail damping T*kernelScale cut a b A B age := by
  have integrable:=mixedIntegrand_integrable cut a b A B p k ell age frequency damping positive F
  have split:=intervalIntegral.integral_interval_add_Ioi integrable (integrable.mono_set (Ioi_subset_Ioi future))
  change ‖(∫ lag in Ioi 0,mixedIntegrand cut a b A B p k ell age frequency damping lag F)-
    (∫ lag in (0:ℝ)..T,mixedIntegrand cut a b A B p k ell age frequency damping lag F)‖ ≤ _
  rw [←split,add_sub_cancel_left]
  have h:=norm_integral_le_of_norm_le
    (((dampedSquare_integrable damping positive).mono_set (Ioi_subset_Ioi future)).mul_const (kernelScale cut a b A B age))
    (show ∀ᵐ lag ∂volume.restrict (Ioi T),
      ‖mixedIntegrand cut a b A B p k ell age frequency damping lag F‖ ≤
        dampedSquare damping lag*kernelScale cut a b A B age from by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with lag hlag
      exact mixedIntegrand_bound cut a b A B p k ell age frequency damping lag (future.trans hlag.le) F)
  rw [integral_mul_const,squareTail_integral damping T positive] at h
  exact h


def responseFamily (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) :
    SourceFamilyOperator.Operator Index H where
  component F:=finiteMixedResponse cut a b A B p k ell age frequency damping F
  bounded:=⟨squareTail damping 0*kernelScale cut a b A B age,
    mul_nonneg (squareTail_nonnegative damping 0 positive le_rfl) (kernelScale_nonnegative cut a b A B age),
    fun F x=>((finiteMixedResponse cut a b A B p k ell age frequency damping F).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (finiteMixedResponse_bound cut a b A B p k ell age frequency damping positive F) (norm_nonneg x))⟩

def truncationFamily (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) :
    SourceFamilyOperator.Operator Index H where
  component F:=finiteMixedTruncation cut a b A B p k ell age frequency damping T F
  bounded:=⟨(squareTail damping 0+squareTail damping T)*kernelScale cut a b A B age,
    mul_nonneg (add_nonneg (squareTail_nonnegative damping 0 positive le_rfl)
      (squareTail_nonnegative damping T positive future)) (kernelScale_nonnegative cut a b A B age),fun F x=>by
    have normBound : ‖finiteMixedTruncation cut a b A B p k ell age frequency damping T F‖ ≤
        (squareTail damping 0+squareTail damping T)*kernelScale cut a b A B age := by
      calc
        _ = ‖finiteMixedResponse cut a b A B p k ell age frequency damping F-
            (finiteMixedResponse cut a b A B p k ell age frequency damping F-
              finiteMixedTruncation cut a b A B p k ell age frequency damping T F)‖ := by rw [sub_sub_cancel]
        _  ≤  _ := (norm_sub_le _ _).trans ((add_le_add
          (finiteMixedResponse_bound cut a b A B p k ell age frequency damping positive F)
          (finiteMixedResponse_tail cut a b A B p k ell age frequency damping T positive future F)).trans_eq (by ring))
    exact ((finiteMixedTruncation cut a b A B p k ell age frequency damping T F).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right normBound (norm_nonneg x))⟩

def tailFamily (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) :
    SourceFamilyOperator.Operator Index H where
  component F:=finiteMixedResponse cut a b A B p k ell age frequency damping F-
    finiteMixedTruncation cut a b A B p k ell age frequency damping T F
  bounded:=⟨squareTail damping T*kernelScale cut a b A B age,
    mul_nonneg (squareTail_nonnegative damping T positive future) (kernelScale_nonnegative cut a b A B age),
    fun F x=>((finiteMixedResponse cut a b A B p k ell age frequency damping F-
      finiteMixedTruncation cut a b A B p k ell age frequency damping T F).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (finiteMixedResponse_tail cut a b A B p k ell age frequency damping T positive future F) (norm_nonneg x))⟩

def mixedResponse (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (responseFamily cut a b A B p k ell age frequency damping positive)

def mixedTruncation (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) : HistorySpace →L[ℂ] HistorySpace :=
  lift sourceFilter (truncationFamily cut a b A B p k ell age frequency damping T positive future)

theorem mixedResponse_tail (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T) :
    ‖mixedResponse cut a b A B p k ell age frequency damping positive-
      mixedTruncation cut a b A B p k ell age frequency damping T positive future‖ ≤
      squareTail damping T*kernelScale cut a b A B age := by
  have same:=lift_congr sourceFilter
    (add (tailFamily cut a b A B p k ell age frequency damping T positive future)
      (truncationFamily cut a b A B p k ell age frequency damping T positive future))
    (responseFamily cut a b A B p k ell age frequency damping positive)
    (fun F=>by simp only [add,tailFamily,truncationFamily,responseFamily,sub_add_cancel])
  rw [lift_add] at same
  change _=mixedResponse cut a b A B p k ell age frequency damping positive at same
  rw [←same,mixedTruncation,add_sub_cancel_right]
  exact CanonicalGradedVariation.lift_bound sourceFilter _ _
    (mul_nonneg (squareTail_nonnegative damping T positive future) (kernelScale_nonnegative cut a b A B age))
    (finiteMixedResponse_tail cut a b A B p k ell age frequency damping T positive future)

def mixedKernelFamily (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age lag : ℝ) (future : 0 ≤ lag) : SourceFamilyOperator.Operator Index H where
  component F:=finiteMixedKernel cut a b A B p k ell (age+lag) age F
  bounded:=⟨kernelScale cut a b A B age*(1+lag)^2,
    mul_nonneg (kernelScale_nonnegative cut a b A B age) (sq_nonneg _),fun F x=>
      ((finiteMixedKernel cut a b A B p k ell (age+lag) age F).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (finiteMixedKernel_bound cut a b A B p k ell age lag future F) (norm_nonneg x))⟩

def preparedTwoTime (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age lag : ℝ) (future : 0 ≤ lag)
    (left right : Bool) (lc ls rc rs : Fin 2) (f g : Profile) : ℂ :=
  SourceGraph.response (lift sourceFilter (mixedKernelFamily cut a b A B p k ell age lag future))
    left right lc ls rc rs f g

def preparedResponse (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping : ℝ) (positive : 0<damping)
    (left right : Bool) (lc ls rc rs : Fin 2) (f g : Profile) : ℂ :=
  SourceGraph.response (mixedResponse cut a b A B p k ell age frequency damping positive)
    left right lc ls rc rs f g

theorem preparedResponse_tail (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T)
    (left right : Bool) (lc ls rc rs : Fin 2) (f g : Profile) :
    ‖preparedResponse cut a b A B p k ell age frequency damping positive left right lc ls rc rs f g-
      SourceGraph.response (mixedTruncation cut a b A B p k ell age frequency damping T positive future)
        left right lc ls rc rs f g‖ ≤
      legBound^2*(squareTail damping T*kernelScale cut a b A B age)*‖f‖*‖g‖ := by
  have same : preparedResponse cut a b A B p k ell age frequency damping positive left right lc ls rc rs f g-
      SourceGraph.response (mixedTruncation cut a b A B p k ell age frequency damping T positive future)
        left right lc ls rc rs f g=
      SourceGraph.response (mixedResponse cut a b A B p k ell age frequency damping positive-
        mixedTruncation cut a b A B p k ell age frequency damping T positive future) left right lc ls rc rs f g := by
    simp only [preparedResponse,SourceGraph.response,sub_apply,inner_sub_right]
  rw [same]
  apply (SourceGraph.response_bound _ left right lc ls rc rs f g).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (mixedResponse_tail cut a b A B p k ell age frequency damping T positive future) (sq_nonneg _))
      (norm_nonneg f)) (norm_nonneg g)

-- Equal-time commutator contact is read from the same two ordered words.
-- Density seagulls from varying geometry are separate source insertions.
theorem finiteMixedKernel_equalTime (cut : ℕ) (a b : ScalarIndex) (A B : NativeCurrent)
    (p k ell : PhysicalMomentum) (age : ℝ) (F : Index) :
    finiteMixedKernel cut a b A B p k ell age age F=
      Complex.I • (gradeZeroProjection*SourceFiniteUnitary.time (compression (p+k+ell) F+cutoff cut) (-age)*
        (actualReader b B*actualReader a A-actualReader a A*actualReader b B)*
        SourceFiniteUnitary.time (compression p F+cutoff cut) age*gradeZeroProjection) := by
  simp only [finiteMixedKernel,fullWord,sub_self,SourceFiniteUnitary.time_zero,mul_one,
    mul_sub,sub_mul,mul_assoc]

open PreparationVacuumPreparedTail PreparationVacuumTailOperator PreparationVacuumNativeClosure
open CanonicalPreparationCore.Completed CanonicalPreparationCreation
open PreparationChartGuard PreparationScalarCoordinates CanonicalScalarPreparation
open SaturationMonoid.Quantum.Forms

theorem actual_prepared_mixed_return (B0 : ℕ→Fin 5→(ℕ→ℝ))
    (nonnegative : ∀ k i n,0 ≤ B0 k i n) (inputs : PreparationVacuumTailSupport.UnitEnergyInputs B0 102)
    (epsilon : ℝ) (precision : 0<epsilon) :
    ∃ x : (BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
      (completeNativeRemainder B0 nonnegative inputs)).domain,
      let f:=zeroLocalizedProfile actualNativeLocalizer x.val
      ‖prepared f‖=1 ∧
      prepared f=sourceCreated (GaussHalfDensity.halfDensityEquiv 0 x.val.val) ∧
      ‖BoundedRemainder.operator sourceClosedFactor sourceClosedFactor_closed sourceClosedFactor_dense
          (completeNativeRemainder B0 nonnegative inputs) x-
        (BoundedRemainder.energy sourceClosedFactor sourceClosedFactor_closed
          (completeNativeRemainder B0 nonnegative inputs):ℂ) • x.val‖<epsilon ∧
      (∀ (addition : Bool) (c s : Fin 2),
        reader gradeZeroProjection (inclusion (completedLeg addition c s f))=inclusion (completedLeg addition c s f)) ∧
      ∀ (cut : ℕ) (a b : ScalarIndex) (mu nu : Fin 4) (v w : Fin 12)
        (p k ell : PhysicalMomentum) (age frequency damping T : ℝ) (positive : 0<damping) (future : 0 ≤ T)
        (left right : Bool) (lc ls rc rs : Fin 2),
        ‖preparedResponse cut a b (gauge48 actualNativeLocalizer mu v) (gauge48 actualNativeLocalizer nu w)
          p k ell age frequency damping positive left right lc ls rc rs f f-
          SourceGraph.response (mixedTruncation cut a b (gauge48 actualNativeLocalizer mu v)
            (gauge48 actualNativeLocalizer nu w) p k ell age frequency damping T positive future)
            left right lc ls rc rs f f‖ ≤
          legBound^2*(squareTail damping T*kernelScale cut a b (gauge48 actualNativeLocalizer mu v)
            (gauge48 actualNativeLocalizer nu w) age)*‖f‖*‖f‖ := by
  obtain ⟨x,hx⟩:=actual_full_tail_preparation B0 nonnegative inputs epsilon precision
  refine ⟨x,hx.1,hx.2.2.1,hx.2.1,?_,?_⟩
  · exact fun addition c s=>completedLeg_gradeZero addition c s _
  · intro cut a b mu nu v w p k ell age frequency damping T positive future left right lc ls rc rs
    exact preparedResponse_tail cut a b _ _ p k ell age frequency damping T positive future left right lc ls rc rs _ _

end LowEnergy.PreparationVacuumActualPreparedMixed
