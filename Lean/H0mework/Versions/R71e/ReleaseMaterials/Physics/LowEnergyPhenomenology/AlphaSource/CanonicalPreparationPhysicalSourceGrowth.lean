import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationPhysicalTimePolynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumPhysicalHalfAxis
open GaussCoreHilbert CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldPerturbation PreparationVacuumActionFieldLift
open PreparationVacuumOriginalGreenFeedback
open Filter Set
open scoped Topology BigOperators InnerProductSpace Matrix Interval
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
local instance : NormedAlgebra ℚ Op:=NormedAlgebra.restrictScalars ℚ ℂ _
attribute [local irreducible] actualA actualC actualGrowth jointGenerator jointCurrent physicalTime timeSlope

def SourceSubexp {E : Type*} [Norm E] (f : ℝ→E) : Prop:=
  ∀d : ℝ,0<d→Tendsto (fun r=>Real.exp (-d*r)*‖f r‖) atTop (𝓝 0)

theorem subexp_const {E : Type*} [Norm E] (v : E) : SourceSubexp (fun _=>v) :=by
  intro d hd
  have h : Tendsto (fun r : ℝ=>Real.exp (-d*r)) atTop (𝓝 0):=by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 d hd
  simpa using h.mul_const ‖v‖

theorem subexp_add {E : Type*} [SeminormedAddCommGroup E] {f g : ℝ→E}
    (hf : SourceSubexp f) (hg : SourceSubexp g) : SourceSubexp (fun r=>f r+g r) :=by
  intro d hd
  refine squeeze_zero (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun r=>?_) (by simpa using (hf d hd).add (hg d hd))
  exact (mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le).trans_eq (by simp only [neg_mul];ring)

theorem subexp_neg {E : Type*} [SeminormedAddCommGroup E] {f : ℝ→E}
    (hf : SourceSubexp f) : SourceSubexp (fun r=> -f r) :=by
  simpa only [SourceSubexp,norm_neg] using hf

theorem subexp_mul {E : Type*} [NormedRing E] {f g : ℝ→E}
    (hf : SourceSubexp f) (hg : SourceSubexp g) : SourceSubexp (fun r=>f r*g r) :=by
  intro d hd
  have half : 0<d/2:=by positivity
  refine squeeze_zero (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun r=>?_) (by simpa using (hf (d/2) half).mul (hg (d/2) half))
  have w : Real.exp (-d*r)=Real.exp (-(d/2)*r)*Real.exp (-(d/2)*r):=by
    rw [←Real.exp_add];congr 1;ring
  calc
    _≤Real.exp (-d*r)*(‖f r‖*‖g r‖):=mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Real.exp_pos _).le
    _=_:=by rw [w];simp only [neg_mul];ring

theorem subexp_smul {𝕜 E : Type*} [NormedField 𝕜] [SeminormedAddCommGroup E]
    [NormedSpace 𝕜 E] (c : 𝕜) {f : ℝ→E} (hf : SourceSubexp f) : SourceSubexp (fun r=>c • f r) :=by
  intro d hd
  convert (hf d hd).const_mul ‖c‖ using 1
  · ext r;simp only [norm_smul,neg_mul];ring
  · simp

theorem subexp_map {E G : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup G]
    [NormedSpace ℂ E] [NormedSpace ℂ G] (L : E→L[ℂ] G) {f : ℝ→E}
    (hf : SourceSubexp f) : SourceSubexp (fun r=>L (f r)) :=by
  intro d hd
  refine squeeze_zero (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))
    (fun r=>?_) (by simpa using (hf d hd).const_mul ‖L‖)
  exact (mul_le_mul_of_nonneg_left (L.le_opNorm _) (Real.exp_pos _).le).trans_eq (by simp only [neg_mul];ring)

theorem actualGrowth_polynomial (p : PhysicalMomentum) (F : Index) (t Q : ℝ)
    (one : 1≤Q) (dominates : t*‖actualA p F‖≤Q) (positive : 0≤t) :
    actualGrowth p F t≤57*Q^56 :=by
  unfold actualGrowth
  calc
    _≤∑n∈Finset.range 57,Q^56:=by
      apply Finset.sum_le_sum
      intro n hn
      exact (pow_le_pow_left₀ (mul_nonneg positive (norm_nonneg _)) dominates n).trans
        (pow_le_pow_right₀ one (by have := Finset.mem_range.mp hn;omega))
    _=_:=by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_ofNat]

private theorem affine_argument_bound (a b r : ℝ) (hr : 1≤r) : |a*r+b|≤(|a|+|b|)*r :=by
  have h:=abs_add_le (a*r) b
  rw [abs_mul,abs_of_nonneg (by linarith : 0≤r)] at h
  calc
    _≤|a| *r+|b|:=h
    _≤|a| *r+|b| *r:=add_le_add le_rfl (le_mul_of_one_le_right (abs_nonneg b) hr)
    _=_:=by ring

theorem actual_time_subexp (p : PhysicalMomentum) (F : Index) (a b : ℝ) :
    SourceSubexp (fun r=>physicalTime p F (a*r+b) 0) :=by
  intro d hd
  let Q : ℝ:=1+(|a|+|b|)*‖actualA p F‖
  have hQ : 1≤Q:=by
    dsimp [Q]
    have h:=mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) (norm_nonneg (actualA p F))
    linarith
  have lim : Tendsto (fun r : ℝ=>Real.exp (-d*r)*(57*Q^56*r^56)) atTop (𝓝 0):=by
    have h:=tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (56:ℕ) d hd
    simp only [Real.rpow_natCast] at h
    convert h.const_mul (57*Q^56) using 1
    · ext r;ac_rfl
    · simp
  refine squeeze_zero' (Filter.Eventually.of_forall (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))) ?_ lim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have harg : |a*r+b| *‖actualA p F‖≤Q*r:=by
    have z:=(mul_le_mul_of_nonneg_right (affine_argument_bound a b r hr) (norm_nonneg (actualA p F)))
    calc
      _≤((|a|+|b|)*r)*‖actualA p F‖:=z
      _=((|a|+|b|)*‖actualA p F‖)*r:=by ring
      _≤Q*r:=mul_le_mul_of_nonneg_right (by dsimp [Q];linarith) (by linarith)
  have hp:=actualGrowth_polynomial p F |a*r+b| (Q*r) (by nlinarith) harg (abs_nonneg _)
  have bound : ‖physicalTime p F (a*r+b) 0‖≤57*Q^56*r^56:=
    (actual_time_bound p F (a*r+b)).trans (by simpa only [mul_pow,mul_assoc] using hp)
  exact mul_le_mul_of_nonneg_left bound (Real.exp_pos _).le

def actualVariationBound (p : PhysicalMomentum) (F : Index) (B : Op) (t : ℝ) : ℝ:=
  |t| *(actualGrowth p F |t|)^2*‖B‖

theorem actual_variation_bound (p : PhysicalMomentum) (F : Index) (B : Op) (t : ℝ) :
    ‖CanonicalGradedVariation.variation (jointGenerator p F 0 0) B t‖≤actualVariationBound p F B t :=by
  have bound (s : ℝ) (inside : |s|≤|t|) :
      ‖SourceFiniteUnitary.time (jointGenerator p F 0 0) s‖≤actualGrowth p F |t|:=
    by simpa only [physicalTime] using actual_time_window p F |t| s inside
  have h:=variationBetween_window (jointGenerator p F 0 0) B 0 |t|
    (actualGrowth p F |t|) (actualGrowth p F |t|) t
    (actualGrowth_nonnegative p F _ (abs_nonneg t)) (actualGrowth_nonnegative p F _ (abs_nonneg t)) le_rfl
    bound (by simpa only [zero_smul,add_zero] using bound)
  exact h.trans_eq (by unfold actualVariationBound;ring)

theorem actual_variation_subexp (p : PhysicalMomentum) (F : Index) (B : Op) (a b : ℝ) :
    SourceSubexp (fun r=>CanonicalGradedVariation.variation (jointGenerator p F 0 0) B (a*r+b)) :=by
  intro d hd
  let Q : ℝ:=1+(|a|+|b|)*‖actualA p F‖
  let C : ℝ:=(|a|+|b|)*(57*Q^56)^2*‖B‖
  have hQ : 1≤Q:=by
    dsimp [Q]
    have h:=mul_nonneg (add_nonneg (abs_nonneg a) (abs_nonneg b)) (norm_nonneg (actualA p F))
    linarith
  have lim : Tendsto (fun r : ℝ=>Real.exp (-d*r)*(C*r^113)) atTop (𝓝 0):=by
    have h:=tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (113:ℕ) d hd
    simp only [Real.rpow_natCast] at h
    convert h.const_mul C using 1
    · ext r;ac_rfl
    · simp
  refine squeeze_zero' (Filter.Eventually.of_forall (fun r=>mul_nonneg (Real.exp_pos _).le (norm_nonneg _))) ?_ lim
  filter_upwards [eventually_ge_atTop (1:ℝ)] with r hr
  have normarg:=affine_argument_bound a b r hr
  have harg : |a*r+b| *‖actualA p F‖≤Q*r:=by
    have z:=(mul_le_mul_of_nonneg_right normarg (norm_nonneg (actualA p F)))
    calc
      _≤((|a|+|b|)*r)*‖actualA p F‖:=z
      _=((|a|+|b|)*‖actualA p F‖)*r:=by ring
      _≤Q*r:=mul_le_mul_of_nonneg_right (by dsimp [Q];linarith) (by linarith)
  have hp : actualGrowth p F |a*r+b|≤57*Q^56*r^56:=by
    have h:=actualGrowth_polynomial p F |a*r+b| (Q*r) (by nlinarith) harg (abs_nonneg _)
    simpa only [mul_pow,mul_assoc] using h
  have vbound : ‖CanonicalGradedVariation.variation (jointGenerator p F 0 0) B (a*r+b)‖≤C*r^113:=by
    refine (actual_variation_bound p F B (a*r+b)).trans ?_
    unfold actualVariationBound
    calc
      _≤((|a|+|b|)*r)*(57*Q^56*r^56)^2*‖B‖:=by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact mul_le_mul normarg (pow_le_pow_left₀ (actualGrowth_nonnegative p F _ (abs_nonneg _)) hp 2)
          (sq_nonneg _) (by positivity)
      _=_:=by
        dsimp only [C]
        rw [mul_pow,←pow_mul]
        norm_num only [show (56:ℕ)*2=112 by decide]
        rw [show r^113=r*r^112 from pow_succ' r 112]
        ac_rfl
  exact mul_le_mul_of_nonneg_left vbound (Real.exp_pos _).le

def SubexpJets {E : Type*} [Norm E] (j : ℝ→SourceJet E) : Prop:=
  SourceSubexp (fun r=>(j r).value) ∧ SourceSubexp (fun r=>(j r).first) ∧ SourceSubexp (fun r=>(j r).second)

theorem constantJets_subexp (A : Op) : SubexpJets (fun _=>jetConst A):=
  ⟨subexp_const _,subexp_const _,subexp_const _⟩

theorem productJets_subexp (a b : ℝ→SourceJet Op) (ha : SubexpJets a) (hb : SubexpJets b) :
    SubexpJets (fun r=>jetMul (a r) (b r)):=
  ⟨subexp_mul ha.1 hb.1,subexp_add (subexp_mul ha.2.1 hb.1) (subexp_mul ha.1 hb.2.1),
    subexp_add (subexp_add (subexp_mul ha.2.2 hb.1) (subexp_mul ha.2.1 hb.2.1))
      (subexp_add (subexp_mul ha.2.1 hb.2.1) (subexp_mul ha.1 hb.2.2))⟩

theorem sumJets_subexp (a b : ℝ→SourceJet Op) (ha : SubexpJets a) (hb : SubexpJets b) :
    SubexpJets (fun r=>addJet (a r) (b r)):=
  ⟨subexp_add ha.1 hb.1,subexp_add ha.2.1 hb.2.1,subexp_add ha.2.2 hb.2.2⟩

private theorem timeJets_subexp_generic (C : Op) (rate shift : ℝ)
    (ht : SourceSubexp (fun r=>SourceFiniteUnitary.time C (rate*r+shift))) :
    SubexpJets (timeJet C rate shift) :=by
  have first : SourceSubexp (fun r=>rate •
      (SourceFiniteUnitary.time C (rate*r+shift)*((-Complex.I) • C))):=
    subexp_smul (𝕜:=ℝ) (E:=Op) rate (subexp_mul (E:=Op) ht (subexp_const ((-Complex.I) • C)))
  exact ⟨ht,first,subexp_smul (𝕜:=ℝ) (E:=Op) rate (subexp_mul (E:=Op) first (subexp_const ((-Complex.I) • C)))⟩

theorem physicalTimeJets_subexp (p : PhysicalMomentum) (F : Index) (rate shift : ℝ) :
    SubexpJets (physicalTimeJet p F 0 rate shift) :=by
  exact timeJets_subexp_generic (jointGenerator p F 0 0) rate shift
    (by simpa only [physicalTime] using actual_time_subexp p F rate shift)

private theorem variationJets_subexp_generic (C B : Op) (rate shift : ℝ)
    (hv : SourceSubexp (fun r=>CanonicalGradedVariation.variation C B (rate*r+shift)))
    (ht : SubexpJets (timeJet C rate shift)) : SubexpJets (variationJet C B rate shift) :=by
  have first : SourceSubexp (fun r=>rate •
      (CanonicalGradedVariation.variation C B (rate*r+shift)*((-Complex.I) • C)+
        SourceFiniteUnitary.time C (rate*r+shift)*((-Complex.I) • B))):=
    subexp_smul (𝕜:=ℝ) (E:=Op) rate (subexp_add (E:=Op)
      (subexp_mul (E:=Op) hv (subexp_const ((-Complex.I) • C)))
      (subexp_mul (E:=Op) ht.1 (subexp_const ((-Complex.I) • B))))
  exact ⟨hv,first,subexp_smul (𝕜:=ℝ) (E:=Op) rate (subexp_add (E:=Op)
    (subexp_mul (E:=Op) first (subexp_const ((-Complex.I) • C)))
    (subexp_mul (E:=Op) ht.2.1 (subexp_const ((-Complex.I) • B))))⟩

theorem physicalSlopeJets_subexp (force : Field289) (p : PhysicalMomentum) (F : Index) (rate shift : ℝ) :
    SubexpJets (physicalSlopeJet force p F rate shift) :=by
  exact variationJets_subexp_generic (jointGenerator p F 0 0) (jointCurrent p F 0 0 force) rate shift
    (actual_variation_subexp p F (jointCurrent p F 0 0 force) rate shift)
    (physicalTimeJets_subexp p F rate shift)

theorem rawKernelJets_subexp (reader : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) :
    SubexpJets (PreparationVacuumPhysicalFeedback.rawKernelJet reader p k F z w 0) :=by
  unfold PreparationVacuumPhysicalFeedback.rawKernelJet
  exact productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _
    (physicalTimeJets_subexp _ _ _ _) (constantJets_subexp _)) (constantJets_subexp _))
      (constantJets_subexp _)) (physicalTimeJets_subexp _ _ _ _)

theorem slopeKernelJets_subexp (reader force : Field289) (p k : PhysicalMomentum) (F : Index) (z w : ℂ) :
    SubexpJets (slopeKernelJet reader force p k F z w) :=by
  unfold slopeKernelJet
  apply sumJets_subexp
  · apply sumJets_subexp
    · apply sumJets_subexp
      · apply sumJets_subexp
        · exact productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _
            (physicalSlopeJets_subexp _ _ _ _ _) (constantJets_subexp _)) (constantJets_subexp _))
              (constantJets_subexp _)) (physicalTimeJets_subexp _ _ _ _)
        · exact productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _
            (physicalTimeJets_subexp _ _ _ _) (constantJets_subexp _)) (constantJets_subexp _))
              (constantJets_subexp _)) (physicalTimeJets_subexp _ _ _ _)
      · exact productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _
          (physicalTimeJets_subexp _ _ _ _) (constantJets_subexp _)) (constantJets_subexp _))
            (constantJets_subexp _)) (physicalTimeJets_subexp _ _ _ _)
    · exact productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _
        (physicalTimeJets_subexp _ _ _ _) (constantJets_subexp _)) (constantJets_subexp _))
          (constantJets_subexp _)) (physicalTimeJets_subexp _ _ _ _)
  · exact productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _ (productJets_subexp _ _
      (physicalTimeJets_subexp _ _ _ _) (constantJets_subexp _)) (constantJets_subexp _))
        (constantJets_subexp _)) (physicalSlopeJets_subexp _ _ _ _ _)

private theorem pairJets_subexp_generic (x y : H) (j : ℝ→SourceJet Op) (hj : SubexpJets j) :
    SubexpJets (fun r=>negativeJet (pairJet x y (j r))) :=by
  let L : Op→L[ℂ] ℂ:=(innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H y)
  have h0 : SourceSubexp (fun r=>L (j r).value):=
    subexp_map (E:=Op) (G:=ℂ) (f:=fun r=>(j r).value) L hj.1
  have h1 : SourceSubexp (fun r=>L (j r).first):=
    subexp_map (E:=Op) (G:=ℂ) (f:=fun r=>(j r).first) L hj.2.1
  have h2 : SourceSubexp (fun r=>L (j r).second):=
    subexp_map (E:=Op) (G:=ℂ) (f:=fun r=>(j r).second) L hj.2.2
  refine ⟨?_,?_,?_⟩
  · change SourceSubexp (fun r=> -L (j r).value)
    exact subexp_neg (E:=ℂ) h0
  · change SourceSubexp (fun r=> -L (j r).first)
    exact subexp_neg (E:=ℂ) h1
  · change SourceSubexp (fun r=> -L (j r).second)
    exact subexp_neg (E:=ℂ) h2

theorem sourceJets_subexp (q : PhysicalResponsePoint) (i : Fin 289) :
    SubexpJets (fun r=>sourceJet q 0 r i) :=by
  exact pairJets_subexp_generic (responseLeft q) (responseRight q) _
    (rawKernelJets_subexp (fieldUnit i) q.p q.k q.F q.z q.w)

theorem sourceSlopeJets_subexp (q : PhysicalResponsePoint) (force : Field289) (i : Fin 289) :
    SubexpJets (fun r=>sourceSlopeJet q force r i) :=by
  exact pairJets_subexp_generic (responseLeft q) (responseRight q) _
    (slopeKernelJets_subexp (fieldUnit i) force q.p q.k q.F q.z q.w)

theorem fullSourceJets_subexp (q : PhysicalResponsePoint) (force : Field289) (response : Bool) (i : Fin 289) :
    SubexpJets (fun r=>fullSourceJet q force response r i) :=by
  cases response
  · exact sourceJets_subexp _ _
  · exact sourceSlopeJets_subexp _ _ _

theorem laplace_norm (lambda : ℂ) (r : ℝ) : ‖laplaceWeight lambda r‖=Real.exp (-lambda.re*r):=by
  simp only [laplaceWeight,Complex.norm_exp,Complex.mul_re,Complex.neg_re,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,neg_mul]

theorem weighted_decay (f : ℝ→ℂ) (hf : SourceSubexp f) (lambda : ℂ) (positive : 0<lambda.re) :
    Tendsto (fun r=>laplaceWeight lambda r*f r) atTop (𝓝 0) :=by
  have point (r : ℝ) : Real.exp (-lambda.re*r)*‖f r‖=‖laplaceWeight lambda r*f r‖:=by
    rw [norm_mul,laplace_norm]
  have h:=Filter.Tendsto.congr (f₁:=fun r=>Real.exp (-lambda.re*r)*‖f r‖)
    (f₂:=fun r=>‖laplaceWeight lambda r*f r‖) point (hf lambda.re positive)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr h

theorem fullJetEntry_subexp (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (i : Fin 289) (n : Fin 3) : SourceSubexp (fun r=>jetEntry (fullSourceJet q force response r i) n) :=by
  have h:=fullSourceJets_subexp q force response i
  fin_cases n
  · exact h.1
  · exact h.2.1
  · exact h.2.2

theorem fullInitialCoSource_decay (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (lambda : ℂ) (positive : 0<lambda.re) (i : Fin 289) (n : Fin 3) :
    Tendsto (fun r=>laplaceWeight lambda r*initialCoSource lambda (fullSourceJet q force response r i) n) atTop (𝓝 0) :=by
  have hf : SourceSubexp (fun r=>initialCoSource lambda (fullSourceJet q force response r i) n):=by
    have h:=fullSourceJets_subexp q force response i
    fin_cases n
    · exact subexp_const 0
    · exact h.1
    · exact subexp_add (subexp_mul (subexp_const lambda) h.1) h.2.1
  exact weighted_decay _ hf lambda positive

private theorem tendstoListSumZero {ι : Type*} (ts : List ι) (f : ι→ℝ→ℂ)
    (h : ∀a∈ts,Tendsto (f a) atTop (𝓝 0)) : Tendsto (fun r=>(ts.map (fun a=>f a r)).sum) atTop (𝓝 0) :=by
  induction ts with
  | nil=>exact tendsto_const_nhds
  | cons a rest ih=>
    simpa only [List.map_cons,List.sum_cons,zero_add] using
      (h a (by simp)).add (ih (fun b hb=>h b (by simp [hb])))

theorem fullBoundary_decay (q : PhysicalResponsePoint) (force : Field289) (response : Bool)
    (spatial : Fin 3→ℂ) (lambda : ℂ) (positive : 0<lambda.re) (row : Fin 289) :
    Tendsto (fun T=>fullBoundary q force response spatial lambda T row) atTop (𝓝 0) :=by
  unfold fullBoundary
  apply tendstoListSumZero
  intro a _
  by_cases same : row=a.val.row
  · simp only [if_pos same]
    simpa only [mul_zero] using (fullInitialCoSource_decay q force response lambda positive a.val.column (nativeTimeOrder a)).const_mul
      (termSpatial spatial a.val)
  · simp only [if_neg same]
    exact tendsto_const_nhds

end LowEnergy.PreparationVacuumPhysicalHalfAxis
