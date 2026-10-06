import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceCutoffSharpCore
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.SourceResolventGraphSplice

/-! The original cutoff's own radius and the signed finite-resolvent mass balance. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.SourceSignedRadiusBalance
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory
open GaussUnitaryHistory (Index)
open FullYSourceCutoffVolterra FullYSourceResolventGraphSplice
open scoped Topology InnerProductSpace BigOperators

theorem geometric_derivative_nonnegative (s : ℝ) (_hs : 0 ≤ s) (hs1 : s ≤ 1)
    (m : ℕ) : 0 ≤ 1-(1-s)^m*(1+(m : ℝ)*s) := by
  suffices h : (1-s)^m*(1+(m : ℝ)*s) ≤ 1 by linarith
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : 0 ≤ (1-s)^m := pow_nonneg (sub_nonneg.mpr hs1) _
    have hd : (1-s)*(1+((m+1 : ℕ) : ℝ)*s) ≤ 1+(m : ℝ)*s := by
      simp only [Nat.cast_add, Nat.cast_one]
      have hn : 0 ≤ (m : ℝ)+1 := by positivity
      nlinarith [mul_nonneg hn (sq_nonneg s)]
    calc
      _ = (1-s)^m*((1-s)*(1+((m+1 : ℕ) : ℝ)*s)) := by rw [pow_succ]; ring
      _ ≤ (1-s)^m*(1+(m : ℝ)*s) := mul_le_mul_of_nonneg_left hd hp
      _ ≤ 1 := ih

theorem geometric_derivative_le_one (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (m : ℕ) : 1-(1-s)^m*(1+(m : ℝ)*s) ≤ 1 := by
  have hp : 0 ≤ (1-s)^m := pow_nonneg (sub_nonneg.mpr hs1) _
  have hn : 0 ≤ 1+(m : ℝ)*s := by positivity
  linarith [mul_nonneg hp hn]

def radiusCutoff (m : ℕ) : H →L[ℂ] H :=
  ∑ j ∈ Finset.range (m+1), (1-GaussRadialDomain.inverseRadius)^j

theorem radius_recursion (m : ℕ) :
    radiusCutoff (m+1)=1+(1-GaussRadialDomain.inverseRadius)*radiusCutoff m := by
  unfold radiusCutoff
  rw [geom_sum_succ]
  exact add_comm _ _

private theorem radiusPolynomial_selfAdjoint {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (S : E →L[ℂ] E)
    (hs : IsSelfAdjoint S) (m : ℕ) :
    IsSelfAdjoint (∑ j ∈ Finset.range (m+1), (1-S)^j) := by
  have hq : IsSelfAdjoint (1-S) := (IsSelfAdjoint.one (E →L[ℂ] E)).sub hs
  exact isSelfAdjoint_sum _ (fun j _ => hq.pow j)

theorem radius_selfAdjoint (m : ℕ) : IsSelfAdjoint (radiusCutoff m) := by
  have hs : IsSelfAdjoint GaussRadialDomain.inverseRadius :=
    (show GaussRadialDomain.inverseRadius.toLinearMap.IsSymmetric from
      fun x y => GaussRadialDomain.inverse_pair x y).isSelfAdjoint
  exact radiusPolynomial_selfAdjoint _ hs m

theorem bounded_inverse_commute :
    Commute GaussYukawaOperator.bounded GaussRadialDomain.inverseRadius := by
  apply ContinuousLinearMap.ext
  intro x
  refine GaussBoundedMultiplier.core_dense.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩ := coreEquiv.surjective a
  change GaussYukawaOperator.bounded (GaussRadialDomain.inverseRadius (embed f))=
    GaussRadialDomain.inverseRadius (GaussYukawaOperator.bounded (embed f))
  rw [GaussRadialDomain.inverse_core,GaussYukawaOperator.bounded_core,
    GaussYukawaOperator.bounded_core,GaussRadialDomain.inverse_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change GaussYukawaCoefficient.normalized z
      ((GaussRadialDomain.reciprocal z : ℂ) • f z)=
    (GaussRadialDomain.reciprocal z : ℂ) • GaussYukawaCoefficient.normalized z (f z)
  exact map_smul _ _ _

theorem radius_bounded_commute (m : ℕ) :
    Commute (radiusCutoff m) GaussYukawaOperator.bounded := by
  have hq : Commute (1-GaussRadialDomain.inverseRadius) GaussYukawaOperator.bounded := by
    exact (Commute.one_left _).sub_left bounded_inverse_commute.symm
  exact Commute.sum_left _ _ _ (fun j _ => hq.pow_left j)

theorem cutoff_radius_factor (m : ℕ) :
    cutoff m=GaussYukawaOperator.bounded*radiusCutoff m := by
  have hl : cutoff m=radiusCutoff m*GaussYukawaOperator.bounded := by
    induction m with
    | zero => simp [cutoff,radiusCutoff]
    | succ m ih =>
      rw [cutoff,ih,radius_recursion]
      simp only [add_mul,one_mul,mul_assoc]
  exact hl.trans (radius_bounded_commute m).eq

theorem sharp_radius_factor (m : ℕ) :
    (cutoff m).adjoint=GaussYukawaOperator.bounded.adjoint*radiusCutoff m := by
  have hl := (cutoff_radius_factor m).trans (radius_bounded_commute m).eq.symm
  change star (cutoff m)=star GaussYukawaOperator.bounded*radiusCutoff m
  rw [hl,star_mul,(radius_selfAdjoint m).star_eq]

theorem native_radius_bound (m : ℕ) (x : H) :
    ‖cutoff m x‖≤‖GaussYukawaOperator.bounded‖*‖radiusCutoff m x‖ := by
  rw [cutoff_radius_factor,mul_apply_eq_comp]
  exact ContinuousLinearMap.le_opNorm _ _

theorem sharp_radius_bound (m : ℕ) (x : H) :
    ‖(cutoff m).adjoint x‖≤‖GaussYukawaOperator.bounded‖*‖radiusCutoff m x‖ := by
  rw [sharp_radius_factor,mul_apply_eq_comp]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using
    ContinuousLinearMap.le_opNorm GaussYukawaOperator.bounded.adjoint (radiusCutoff m x)

def signedFiniteCurrent (F : Index) (m : ℕ) (q : H) : ℝ :=
  2*(inner ℂ (radiusCutoff m q)
    (radiusCutoff m (GaussGradedCompression.compression F q))).im

theorem finite_resolvent_balance (F : Index) (m : ℕ) (z : ℂ) (hz : z.im≠0) (g : H) :
    2*z.im*‖radiusCutoff m (finiteResolvent F z g)‖^2=
      signedFiniteCurrent F m (finiteResolvent F z g)-
      2*(inner ℂ (radiusCutoff m (finiteResolvent F z g)) (radiusCutoff m g)).im := by
  let q := finiteResolvent F z g
  have hq : GaussGradedCompression.compression F q=z • q+g := by
    have hh := congrArg (fun A : H →L[ℂ] H => A g)
      (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
    change GaussGradedCompression.compression F q-z • q=g at hh
    exact (sub_eq_iff_eq_add.mp hh).trans (add_comm _ _)
  have he : inner ℂ (radiusCutoff m q) (radiusCutoff m q)=(‖radiusCutoff m q‖^2 : ℝ) := by
    simp only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow]
    rfl
  change 2*z.im*‖radiusCutoff m q‖^2=
    2*(inner ℂ (radiusCutoff m q)
      (radiusCutoff m (GaussGradedCompression.compression F q))).im-
    2*(inner ℂ (radiusCutoff m q) (radiusCutoff m g)).im
  rw [hq,map_add,map_smul,inner_add_right,inner_smul_right,he]
  simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_im,Complex.ofReal_re]
  ring

theorem finite_resolvent_signed_bound (F : Index) (m : ℕ) (z : ℂ)
    (hz : 0<z.im) (g : H) :
    z.im*‖radiusCutoff m (finiteResolvent F z g)‖^2≤
      signedFiniteCurrent F m (finiteResolvent F z g)+
      z.im⁻¹*‖radiusCutoff m g‖^2 := by
  let x := radiusCutoff m (finiteResolvent F z g)
  let y := radiusCutoff m g
  have hi : |(inner ℂ x y).im|≤‖x‖*‖y‖ :=
    (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  have hy : 2*‖x‖*‖y‖≤z.im*‖x‖^2+z.im⁻¹*‖y‖^2 := by
    apply (mul_le_mul_iff_right₀ hz).mp
    calc
      z.im*(2*‖x‖*‖y‖)≤z.im^2*‖x‖^2+‖y‖^2 := by
        nlinarith [sq_nonneg (z.im*‖x‖-‖y‖)]
      _ = z.im*(z.im*‖x‖^2+z.im⁻¹*‖y‖^2) := by
        rw [mul_add,←mul_assoc z.im z.im⁻¹,mul_inv_cancel₀ hz.ne']
        ring
  have he := finite_resolvent_balance F m z hz.ne' g
  change 2*z.im*‖x‖^2 = signedFiniteCurrent F m (finiteResolvent F z g)-
    2*(inner ℂ x y).im at he
  have hn := (abs_le.mp hi).1
  change z.im*‖x‖^2 ≤ signedFiniteCurrent F m (finiteResolvent F z g)+z.im⁻¹*‖y‖^2
  nlinarith

theorem original_projection_current (F : Index) (W : H →L[ℂ] H)
    (p q : diagonal.domain) :
    inner ℂ (GaussGradedCompression.compression F (p : H)) (W (q : H))-
      inner ℂ (p : H) (W (GaussGradedCompression.compression F (q : H)))=
    inner ℂ (diagonal p) (W (q : H))-inner ℂ (p : H) (W (diagonal q))-
      inner ℂ (diagonal p-GaussGradedCompression.compression F (p : H)) (W (q : H))+
      inner ℂ (p : H) (W (diagonal q-GaussGradedCompression.compression F (q : H))) := by
  simp only [map_sub,inner_sub_left,inner_sub_right]
  abel

#print axioms cutoff_radius_factor
#print axioms sharp_radius_factor
#print axioms finite_resolvent_balance
#print axioms finite_resolvent_signed_bound
#print axioms original_projection_current
end LowEnergy.SourceSignedRadiusBalance
