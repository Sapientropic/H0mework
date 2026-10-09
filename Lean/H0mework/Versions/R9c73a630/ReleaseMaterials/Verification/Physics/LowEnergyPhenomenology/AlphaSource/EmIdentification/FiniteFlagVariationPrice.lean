import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUpperCurrent

set_option autoImplicit false
set_option maxRecDepth 16384
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedGradedPrice
open FullYSourceCutoffVolterra MeasureTheory
open scoped Topology Interval
section Generic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
local instance : NormedAlgebra ℝ (E→L[ℂ]E) := NormedAlgebra.restrictScalars ℝ ℂ _

private theorem time_continuous (G : E→L[ℂ]E) : Continuous (SourceFiniteUnitary.time G) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (hasDerivAt_exp_smul_const ((-Complex.I) • G) t).continuousAt)

private theorem variation_apply (G B : E→L[ℂ]E) (t : ℝ) (v : E) :
    CanonicalGradedVariation.variation G B t v=∫s in (0:ℝ)..t,
      SourceFiniteUnitary.time G s ((-Complex.I) • (B (SourceFiniteUnitary.time G (t-s) v))) := by
  have ct:=time_continuous G
  have hi : IntervalIntegrable (fun s : ℝ => SourceFiniteUnitary.time G s * ((-Complex.I) • B) *
      SourceFiniteUnitary.time G (t-s)) volume 0 t :=
    ((ct.mul continuous_const).mul (ct.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 t
  simpa only [CanonicalGradedVariation.variation,CanonicalGradedVariation.variationBetween,
    zero_smul,add_zero,mul_apply_eq_comp,smul_apply] using ContinuousLinearMap.intervalIntegral_apply hi v

private theorem interval_times (t s : ℝ) (hs : s ∈ Ι (0:ℝ) t) : |s| ≤ |t| ∧ |t-s| ≤ |t| := by
  by_cases ht : 0 ≤ t
  · rw [Set.uIoc_of_le ht] at hs
    rw [abs_of_pos hs.1,abs_of_nonneg ht,abs_of_nonneg (sub_nonneg.mpr hs.2)]
    constructor
    · exact hs.2
    · linarith [hs.1]
  · have ht' : t ≤ 0:=le_of_not_ge ht
    rw [Set.uIoc_of_ge ht'] at hs
    rw [abs_of_nonpos hs.2,abs_of_nonpos ht',abs_of_nonpos (sub_nonpos.mpr (le_of_lt hs.1))]
    constructor <;> linarith [hs.1,hs.2]

omit [CompleteSpace E] in
private theorem range_apply (P Q B : E→L[ℂ]E) (range : Q*B*P=B*P)
    (v : E) (sector : P v=v) : Q (B v)=B v := by
  simpa only [mul_apply_eq_comp,sector] using congrArg (fun A : E→L[ℂ]E=>A v) range

private theorem time_opNorm (C : E→L[ℂ]E) (selfadj : IsSelfAdjoint C) (t : ℝ) :
    ‖SourceFiniteUnitary.time C t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simp only [SourceFiniteUnitary.time_norm C selfadj,one_mul]
  exact le_rfl

theorem finite_flag_variation_price (G C A J P Q R : E→L[ℂ]E)
    (selfadj : IsSelfAdjoint C) (comm : Commute P C)
    (ret : ∀s x,P x=x→SourceFiniteUnitary.time G s x=partialEvolution C A 2 s x)
    (first : ∀s,Q*finitePrefix C A 1 s*P=finitePrefix C A 1 s*P)
    (second : ∀s,R*finitePrefix C A 2 s*P=finitePrefix C A 2 s*P)
    (jp : P*J*P=J*P) (jq : Q*J*Q=J*Q) (jr : R*J*R=J*R)
    (t : ℝ)
    (price0 : ∀s,|s| ≤|t|→∀x,P x=x→‖SourceFiniteUnitary.time G s x‖≤
      (1+|t| *‖A‖+(|t| *‖A‖)^2)*‖x‖)
    (price1 : ∀s,|s| ≤|t|→∀x,Q x=x→‖SourceFiniteUnitary.time G s x‖≤(1+|t| *‖A‖)*‖x‖)
    (price2 : ∀s,|s| ≤|t|→∀x,R x=x→‖SourceFiniteUnitary.time G s x‖≤‖x‖)
    (v : E) (sector : P v=v) :
    ‖CanonicalGradedVariation.variation G J t v‖ ≤
      |t| *‖J‖*(1+2*(|t| *‖A‖)+3*(|t| *‖A‖)^2)*‖v‖ := by
  let x := |t| *‖A‖
  have hx : 0≤x := mul_nonneg (abs_nonneg t) (norm_nonneg A)
  have bound (s : ℝ) (hs : s ∈ Ι (0:ℝ) t) :
      ‖SourceFiniteUnitary.time G s ((-Complex.I) • (J (SourceFiniteUnitary.time G (t-s) v)))‖ ≤
        ‖J‖*(1+2*x+3*x^2)*‖v‖ := by
    have st:=interval_times t s hs
    let u := SourceFiniteUnitary.time C (t-s) v
    let w := finitePrefix C A 1 (t-s) v
    let z := finitePrefix C A 2 (t-s) v
    have pu : P u=u := by
      have h:=(SourceFiniteUnitary.time_commutes C P comm (t-s)).eq
      simpa only [mul_apply_eq_comp,sector] using congrArg (fun B : E→L[ℂ]E=>B v) h
    have qw : Q w=w := range_apply _ _ _ (first (t-s)) v sector
    have rz : R z=z := range_apply _ _ _ (second (t-s)) v sector
    have un : ‖u‖≤‖v‖ := by simpa only [u,SourceFiniteUnitary.time_norm C selfadj] using le_rfl (a:=‖v‖)
    have wn : ‖w‖≤x*‖v‖ := by
      refine ((finitePrefix C A 1 (t-s)).le_opNorm v).trans ?_
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      exact (finitePrefix_bound C A selfadj 1 (t-s)).trans (by
        simpa only [pow_one] using mul_le_mul_of_nonneg_right st.2 (norm_nonneg A))
    have zn : ‖z‖≤x^2*‖v‖ := by
      refine ((finitePrefix C A 2 (t-s)).le_opNorm v).trans ?_
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      exact (finitePrefix_bound C A selfadj 2 (t-s)).trans
        (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right st.2 (norm_nonneg A)) 2)
    have split : SourceFiniteUnitary.time G (t-s) v=u+w+z := by
      simpa only [partialEvolution,add_apply,u,w,z] using ret (t-s) v sector
    have bu:=range_apply _ _ _ jp u pu
    have bw:=range_apply _ _ _ jq w qw
    have bz:=range_apply _ _ _ jr z rz
    have b0 := price0 s st.1 ((-Complex.I) • J u) (by rw [map_smul,bu])
    have b1 := price1 s st.1 ((-Complex.I) • J w) (by rw [map_smul,bw])
    have b2 := price2 s st.1 ((-Complex.I) • J z) (by rw [map_smul,bz])
    simp only [norm_smul,norm_neg,Complex.norm_I,one_mul] at b0 b1 b2
    have n0 : ‖SourceFiniteUnitary.time G s ((-Complex.I) • J u)‖≤(1+x+x^2)*‖J‖*‖v‖ :=
      b0.trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          ((J.le_opNorm u).trans (mul_le_mul_of_nonneg_left un (norm_nonneg J))) (by positivity : 0≤1+x+x^2))
    have n1 : ‖SourceFiniteUnitary.time G s ((-Complex.I) • J w)‖≤(1+x)*‖J‖*(x*‖v‖) :=
      b1.trans (by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
          ((J.le_opNorm w).trans (mul_le_mul_of_nonneg_left wn (norm_nonneg J))) (by positivity : 0≤1+x))
    have n2 : ‖SourceFiniteUnitary.time G s ((-Complex.I) • J z)‖≤‖J‖*(x^2*‖v‖) :=
      b2.trans ((J.le_opNorm z).trans (mul_le_mul_of_nonneg_left zn (norm_nonneg J)))
    rw [split,map_add,map_add,smul_add,smul_add,map_add,map_add]
    exact ((norm_add_le _ _).trans (add_le_add
      ((norm_add_le _ _).trans (add_le_add n0 n1)) n2)).trans_eq (by ring)
  have estimate:=intervalIntegral.norm_integral_le_of_norm_le_const bound
  rw [variation_apply]
  exact estimate.trans_eq (by rw [sub_zero]; dsimp [x]; ring)
end Generic
end LowEnergy.GaussComposite.ActualDressedGradedPrice
