import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceScalarVirialCurrent
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceNativeCutoffContact

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceScalarVirialIMS
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeEnergy
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeForm
open SourceCoframeVolumeCurrent SourceScalarFlatJoint SourceScalarVirialCurrent SourceScalarRetardedGram
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceResolventGraphSplice SourceResolventBandLimit Filter MeasureTheory
open scoped InnerProductSpace
abbrev End := SourceScalarGaugeScale.End
abbrev I := SourceScalarFlatJoint.SliceIndex

def thetaAction (m ell : ℕ) : End := SourceNativeCutoffContact.thetaAction m ell
def contact (i : I) (m ell : ℕ) : End :=
  SourceNativeCutoffContact.contactAction ((scalarFrame i : Scalar),0) m ell

private theorem theta_pair (m ell : ℕ) (f g : QuantumTest) :
    sourcePair f (thetaAction m ell g)=sourcePair (thetaAction m ell f) g :=
  multiply_pair (SourceNativeCutoffContact.theta m ell)
    (fun _ => (SourceNativeCutoffContact.theta_smooth m ell).contDiffAt) f g

private theorem flat_contact (i : I) (m ell : ℕ) (f : QuantumTest) :
    flatMomentum (scalarFrame i) (thetaAction m ell f)=
      thetaAction m ell (flatMomentum (scalarFrame i) f)+contact i m ell f := by
  simpa only [←actual_flat_momentum] using!
    SourceNativeCutoffContact.native_core_contact ((scalarFrame i : Scalar),0) m ell f

private theorem contact_theta (i : I) (m ell : ℕ) : Commute (contact i m ell) (thetaAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative ((scalarFrame i : Scalar),0) m ell z : ℂ)) •
      ((SourceNativeCutoffContact.theta m ell z : ℂ) • f z)=
    (SourceNativeCutoffContact.theta m ell z : ℂ) •
      (((-Complex.I)*(SourceNativeCutoffContact.thetaDerivative ((scalarFrame i : Scalar),0) m ell z : ℂ)) • f z)
  exact smul_comm _ _ _

private theorem position_theta (i : I) (m ell : ℕ) : Commute (positionAction i) (thetaAction m ell) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (positionCoefficient i z : ℂ) • ((SourceNativeCutoffContact.theta m ell z : ℂ) • f z)=
    (SourceNativeCutoffContact.theta m ell z : ℂ) • ((positionCoefficient i z : ℂ) • f z)
  exact smul_comm _ _ _

private theorem core_ims (P T C : End)
    (hP : ∀ f g,sourcePair f (P g)=sourcePair (P f) g)
    (hT : ∀ f g,sourcePair f (T g)=sourcePair (T f) g)
    (hC : ∀ f,P (T f)=T (P f)+C f) (hCT : Commute C T) (f : QuantumTest) :
    ‖embed (P (T f))‖^2=(sourcePair (T (T f)) (P (P f))).re+‖embed (C f)‖^2 := by
  have hTT : P (T (T f))=T (T (P f))+T (C f)+T (C f) := by
    rw [hC,hC,map_add,show C (T f)=T (C f) from LinearMap.congr_fun hCT.eq f]
  have hb : sourcePair (T (T f)) (P (P f))=
      sourcePair (T (P f)) (T (P f))+sourcePair (C f) (T (P f))+sourcePair (C f) (T (P f)) := by
    rw [hP,hTT]
    change inner ℂ (embed (T (T (P f))+T (C f)+T (C f))) (embed (P f))=_
    rw [map_add,map_add,inner_add_left,inner_add_left]
    change sourcePair (T (T (P f))) (P f)+sourcePair (T (C f)) (P f)+sourcePair (T (C f)) (P f)=_
    rw [←hT,←hT,←hT]
  have hnadd (x y : H) : ‖x+y‖^2=‖x‖^2+2*(inner ℂ x y).re+‖y‖^2 := by
    simpa only using! norm_add_sq (𝕜 := ℂ) x y
  rw [hC,map_add,hnadd,hb,Complex.add_re,Complex.add_re]
  have hn : (sourcePair (T (P f)) (T (P f))).re=‖embed (T (P f))‖^2 := by
    simpa only [sourcePair] using! inner_self_eq_norm_sq (𝕜 := ℂ) (embed (T (P f)))
  have hs : (sourcePair (C f) (T (P f))).re=(inner ℂ (embed (T (P f))) (embed (C f))).re := by
    simpa only [sourcePair] using! inner_re_symm (𝕜 := ℂ) (embed (C f)) (embed (T (P f)))
  rw [hn,hs]
  ring

theorem original_flat_ims (i : I) (m ell : ℕ) (f : QuantumTest) :
    ‖embed (flatMomentum (scalarFrame i) (thetaAction m ell f))‖^2=
      (sourcePair (thetaAction m ell (thetaAction m ell f))
        (flatMomentum (scalarFrame i) (flatMomentum (scalarFrame i) f))).re+‖embed (contact i m ell f)‖^2 :=
  core_ims _ _ _ (flat_momentum_pair (scalarFrame i)) (theta_pair m ell)
    (flat_contact i m ell) (contact_theta i m ell) f

private theorem original_position_ims (i : I) (m ell : ℕ) (f : QuantumTest) :
    ‖embed (positionAction i (thetaAction m ell f))‖^2=
      (sourcePair (thetaAction m ell (thetaAction m ell f)) (positionAction i (positionAction i f))).re := by
  have h := core_ims (positionAction i) (thetaAction m ell) 0
    (fun x y => multiply_pair _ _ x y) (theta_pair m ell)
    (fun x => by simpa only [LinearMap.zero_apply,add_zero,Module.End.mul_apply] using! LinearMap.congr_fun (position_theta i m ell).eq x)
    (Commute.zero_left _) f
  simpa only [LinearMap.zero_apply,map_zero,norm_zero,zero_pow (by decide : 2≠0),add_zero] using! h

def contactCost (m ell : ℕ) (f : QuantumTest) : ℝ :=
  sourceTime 0*∑ i : I,‖embed (contact i m ell f)‖^2

/-- IMS applies to the same positive scalar virial; its entire localization error is a bounded native contact sum. -/
theorem original_virial_ims (m ell : ℕ) (f : QuantumTest) :
    (sourcePair (thetaAction m ell f) (positiveVirial (thetaAction m ell f))).re=
      (sourcePair (thetaAction m ell (thetaAction m ell f)) (positiveVirial f)).re+contactCost m ell f := by
  rw [original_positive_virial_square]
  simp_rw [original_flat_ims,original_position_ims]
  simp only [Finset.sum_add_distrib,contactCost,positiveVirial,flatKinetic,radiusSquare,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply,
    sourcePair,map_add,map_smul,map_sum,inner_add_right,inner_smul_right,inner_sum,Complex.add_re]
  have hc (x : ℂ) : ((sourceTime 0 : ℂ)*x).re=sourceTime 0*x.re := by
    rw [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hc2 (x : ℂ) : ((2*(sourceTime 0 : ℂ))*x).re=(2*sourceTime 0)*x.re := by
    have h : (2*(sourceTime 0 : ℂ))=((2*sourceTime 0 : ℝ) : ℂ) := by push_cast; rfl
    rw [h,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [hc,hc2]
  simp only [Complex.re_sum]
  ring

/-- Arbitrary actual p/q mixing is localized before the IMS square, preserving all cross terms. -/
theorem actual_joint_virial_ims (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g k : diagonal.domain) (a b : ℂ) :
    (sourcePair (thetaAction m ell (jointState F z hz g k a b))
      (positiveVirial (thetaAction m ell (jointState F z hz g k a b)))).re=
      (sourcePair (thetaAction m ell (thetaAction m ell (jointState F z hz g k a b)))
        (positiveVirial (jointState F z hz g k a b))).re+
      sourceTime 0*(∑ i : I,‖a • embed (contact i m ell (leftState F z hz k))+
        b • embed (contact i m ell (rightState F z hz g))‖^2) := by
  rw [original_virial_ims]
  simp only [contactCost,jointState,map_add,map_smul]

def boundedContactCost (m ell : ℕ) (hell : m ≤ ell) (x : H) : ℝ :=
  sourceTime 0*∑ i : I,‖SourceNativeCutoffContact.boundedContact ((scalarFrame i : Scalar),0) m ell hell x‖^2

theorem actual_contact_cost_core (m ell : ℕ) (hell : m ≤ ell) (f : QuantumTest) :
    boundedContactCost m ell hell (embed f)=contactCost m ell f := by
  simp only [boundedContactCost,contactCost,SourceNativeCutoffContact.bounded_contact_core,contact]

private theorem lapse_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

private theorem contact_cost_bound (m ell : ℕ) (hell : m ≤ ell) (x : H) :
    boundedContactCost m ell hell x ≤ (244*sourceTime 0/(m+2 : ℝ)^2)*‖x‖^2 := by
  have hb (i : I) :
      ‖SourceNativeCutoffContact.boundedContact ((scalarFrame i : Scalar),0) m ell hell x‖^2 ≤
        (2/(m+2 : ℝ))^2*‖x‖^2 := by
    have h := SourceNativeCutoffContact.bounded_contact_bound ((scalarFrame i : Scalar),0) m ell hell x
    have hi : ‖(scalarFrame i : Scalar)‖=1 := by
      simpa only [Submodule.norm_coe] using (scalarFrame.orthonormal.norm_eq_one i)
    simp only [hi,mul_one] at h
    exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans_eq (mul_pow _ _ _)
  have hsum := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset I)) => hb i)
  have hcard : Fintype.card I=61 := by
    simp only [I,SourceScalarFlatJoint.SliceIndex,Fintype.card_fin,SourceQuantumScalarOrbitDimensions.scalarSlice_finrank]
  have h := mul_le_mul_of_nonneg_left hsum lapse_pos.le
  simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul] at h
  exact h.trans_eq (by
    have hd : (m+2 : ℝ)≠0 := by positivity
    field_simp [hd]
    ring)

/-- The complete scalar61 IMS error has an explicit uniform-in-F/ell full-frequency budget. -/
theorem actual_ims_contact_energy (m ell : ℕ) (hell : m ≤ ell) (F : Index)
    (μ : ℝ) (hμ : 0<μ) (g : H) :
    (∫⁻ w : ℝ,ENNReal.ofReal (boundedContactCost m ell hell (finiteResolvent F (line μ w) g))) ≤
      ENNReal.ofReal ((244*sourceTime 0/(m+2 : ℝ)^2)*(Real.pi/μ)*‖g‖^2) := by
  let C := 244*sourceTime 0/(m+2 : ℝ)^2
  have hC : 0 ≤ C := by
    exact div_nonneg (mul_nonneg (by norm_num) lapse_pos.le) (sq_nonneg _)
  have he : (∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2))=
      ENNReal.ofReal ((Real.pi/μ)*‖g‖^2) := by
    simpa only [line,mul_comm (μ : ℂ) Complex.I] using! SourceActualResolventEnergy.actual_square_lintegral F μ hμ g
  calc
    _  ≤  ∫⁻ w : ℝ,ENNReal.ofReal C*ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_mul hC]
      exact ENNReal.ofReal_le_ofReal (contact_cost_bound m ell hell _)
    _=ENNReal.ofReal C*∫⁻ w : ℝ,ENNReal.ofReal (‖finiteResolvent F (line μ w) g‖^2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _=_ := by rw [he,←ENNReal.ofReal_mul hC]; congr 1; dsimp [C]; ring

/-- No cofinal projection or state-moment hypothesis is needed for the actual localization error. -/
theorem actual_ims_contact_tail (μ : ℝ) (hμ : 0<μ) (g : H) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, ∀ hell : m ≤ ell, ∀ F : Index,
      (∫⁻ w : ℝ,ENNReal.ofReal (boundedContactCost m ell hell (finiteResolvent F (line μ w) g))) ≤
        ENNReal.ofReal ε := by
  intro ε hε
  let C := 244*sourceTime 0*(Real.pi/μ)*‖g‖^2
  obtain ⟨N,hN⟩ := exists_nat_gt (C/ε)
  refine ⟨N,fun m hm ell hell F => (actual_ims_contact_energy m ell hell F μ hμ g).trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hmR : (N : ℝ) ≤ m := Nat.cast_le.mpr hm
  have hd : 0<(m+2 : ℝ) := by positivity
  have hdiv : C/ε<(m+2 : ℝ) := by linarith
  have hc : C<ε*(m+2 : ℝ) := by
    have h := (div_lt_iff₀ hε).mp hdiv
    nlinarith
  have hs : (m+2 : ℝ) ≤ (m+2 : ℝ)^2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hb : C/(m+2 : ℝ)^2 ≤ ε := (div_le_iff₀ (sq_pos_of_pos hd)).mpr
    (hc.le.trans (mul_le_mul_of_nonneg_left hs hε.le))
  convert hb using 1
  dsimp [C]
  ring

end LowEnergy.SourceScalarVirialIMS
