import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourcePrimitiveJetTail
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCurrentEndpointEnergy
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceMixedCurrentJets
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceFixedJetBudget
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceJointResidualEnergy
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeCompressionCovariance
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.SourceMovingJetFlux
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussDiagonalHistory GaussUnitaryHistory
open SourceCoframeStrongJet SourceCoframeScaleTransport SourceCoframeVolumeCurrent
open SourceRetardedIncrement SourceActualResolventEnergy SourceJointResidualEnergy
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open InnerProductSpace
open scoped InnerProductSpace Topology

abbrev Op := H →L[ℂ] H

def frameJet (n : ℕ) (f : QuantumTest) (s : ℝ) : H :=
  ((3/2 : ℝ)^n) • strongJet n f ((3/2 : ℝ)*s)

theorem frame_jet_derivative (n : ℕ) (f : QuantumTest) (s : ℝ) :
    HasDerivAt (frameJet n f) (frameJet (n+1) f s) s := by
  have ht : HasDerivAt (fun t : ℝ => (3/2 : ℝ)*t) (3/2 : ℝ) s := by
    simpa only [id_eq,mul_one] using! (hasDerivAt_id s).const_mul (3/2 : ℝ)
  have h := ((strong_jet_derivative n f ((3/2 : ℝ)*s)).scomp s ht).const_smul ((3/2 : ℝ)^n)
  simpa only [frameJet,one_mul,pow_succ,smul_smul] using! h

private theorem rank_bilinear :
    IsBoundedBilinearMap ℝ (fun p : H×H => rankOne ℂ p.1 p.2) where
  add_left x y z := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,add_apply,smul_add]
  smul_left c x y := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,smul_apply]; exact smul_comm _ _ _
  add_right x y z := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,add_apply,inner_add_left,add_smul]
  smul_right c x y := by apply ContinuousLinearMap.ext; intro w; simp only [rankOne_apply,smul_apply]; rw [←algebraMap_smul ℂ c y,inner_smul_real_left,smul_assoc]
  bound := ⟨1,by norm_num,by intro x y; simp⟩

private theorem rank_derivative {f g : ℝ → H} {f' g' : H} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => rankOne ℂ (f t) (g t))
      (rankOne ℂ f' (g s)+rankOne ℂ (f s) g') s := by
  simpa only [IsBoundedBilinearMap.toContinuousLinearMap_apply,add_comm] using!
    (rank_bilinear.toContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => hf) (fun _ => hg))

def rankJet : ℕ → ℕ → ℕ → QuantumTest → QuantumTest → ℝ → Op
  | 0,r,s,f,g,t => rankOne ℂ (frameJet r f t) (frameJet s g t)
  | n+1,r,s,f,g,t => rankJet n (r+1) s f g t+rankJet n r (s+1) f g t

theorem rank_jet_derivative (n r s : ℕ) (f g : QuantumTest) (t : ℝ) :
    HasDerivAt (rankJet n r s f g) (rankJet (n+1) r s f g t) t := by
  induction n generalizing r s with
  | zero => exact rank_derivative (frame_jet_derivative r f t) (frame_jet_derivative s g t)
  | succ n ih => exact (ih (r+1) s).add (ih r (s+1))

def eigenTest (F : Index) (i : SpectralIndex F) : QuantumTest :=
  coreEquiv.symm ⟨(sourceBasis F i : H),
    FiniteCoreEvolution.coreSpan_le diagonal (supportSet F) (sourceBasis F i).property⟩

@[simp] theorem eigen_test_embed (F : Index) (i : SpectralIndex F) :
    embed (eigenTest F i)=(sourceBasis F i : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

@[simp] theorem frame_zero (f : QuantumTest) (t : ℝ) :
    frameJet 0 f t=hilbertFlow ((3/2 : ℝ)*t) (embed f) := by
  simp [frameJet,strong_jet_zero,hilbertFlow_on_core]

private theorem conjugate_rank (U : H ≃ₗᵢ[ℂ] H) (x y : H) :
    U.conjStarAlgEquiv (rankOne ℂ x y)=rankOne ℂ (U x) (U y) := by
  apply ContinuousLinearMap.ext
  intro z
  change U (inner ℂ y (U.symm z) • x)=inner ℂ (U y) z • U x
  rw [map_smul,←U.inner_map_map y (U.symm z),U.apply_symm_apply]

def projectionJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpectralIndex F, rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

def compressionOrbitJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpectralIndex F, (channelValue F (some i) : ℂ) •
    rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

/-- The static identity term retains the entire escape space, including zero eigenvalue collisions. -/
def resolventOrbitJet (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  (if n=0 then -z⁻¹ • (1 : Op) else 0)+
  ∑ i : SpectralIndex F, (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
    rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

theorem moving_projection_derivative (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (projectionJet F n) (projectionJet F (n+1) t) t := by
  unfold projectionJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ => rank_jet_derivative n 0 0 (eigenTest F i) (eigenTest F i) t) using 1
  funext s
  simp only [Finset.sum_apply]

theorem moving_compression_derivative (F : Index) (n : ℕ) (t : ℝ) :
    HasDerivAt (compressionOrbitJet F n) (compressionOrbitJet F (n+1) t) t := by
  unfold compressionOrbitJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (rank_jet_derivative n 0 0 (eigenTest F i) (eigenTest F i) t).const_smul
        (channelValue F (some i) : ℂ)) using 1
  funext s
  simp only [Finset.sum_apply,Pi.smul_apply]

theorem moving_resolvent_derivative (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (resolventOrbitJet F z n) (resolventOrbitJet F z (n+1) t) t := by
  have h := (hasDerivAt_const t (if n=0 then -z⁻¹ • (1 : Op) else 0)).add
    (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (rank_jet_derivative n 0 0 (eigenTest F i) (eigenTest F i) t).const_smul
        (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹)))
  unfold resolventOrbitJet
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,zero_add]
  simp only [zero_add] at h
  convert! h using 1
  funext s
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply]

theorem actual_moving_projection (F : Index) (t : ℝ) :
    projectionJet F 0 t=
      (hilbertFlow ((3/2 : ℝ)*t)).conjStarAlgEquiv (supportProjection F) := by
  classical
  rw [supportProjection,(sourceBasis F).starProjection_eq_sum_rankOne,map_sum]
  simp only [projectionJet,rankJet,frame_zero,eigen_test_embed,conjugate_rank]



private theorem basis_coefficient (F : Index) (i : SpectralIndex F) (x : H) :
    (sourceBasis F).repr ((supportSpan F).orthogonalProjectionOnto x) i=
      inner ℂ (sourceBasis F i : H) x := by
  rw [OrthonormalBasis.repr_apply_apply]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (sourceBasis F i) x

private theorem actual_compression_spectral (F : Index) :
    GaussGradedCompression.compression F=
      ∑ i : SpectralIndex F, (channelValue F (some i) : ℂ) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  let y := (supportSpan F).orthogonalProjectionOnto x
  have hs := congrArg (supportSpan F).subtypeL ((sourceBasis F).sum_repr (supportAction F y))
  simp only [map_sum,map_smul] at hs
  have hc (i : SpectralIndex F) :
      (sourceBasis F).repr (supportAction F y) i=
        (channelValue F (some i) : ℂ)*(sourceBasis F).repr y i :=
    SourceFiniteResolventEnergy.coordinate_action (supportAction F) (support_action_selfAdjoint F) y i
  simp_rw [hc,mul_smul] at hs
  have he := compression_escape_zero F x
  change GaussGradedCompression.compression F (x-supportProjection F x)=0 at he
  rw [map_sub,sub_eq_zero] at he
  change (∑ i, (channelValue F (some i) : ℂ) •
    (sourceBasis F).repr y i • (sourceBasis F i : H))=
      GaussGradedCompression.compression F (supportProjection F x) at hs
  trans GaussGradedCompression.compression F (supportProjection F x)
  · exact he
  trans ∑ i, (channelValue F (some i) : ℂ) • (sourceBasis F).repr y i • (sourceBasis F i : H)
  · exact hs.symm
  simp only [sum_apply,smul_apply,rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (sourceBasis F).repr y i=inner ℂ (sourceBasis F i : H) x from basis_coefficient F i x]

private theorem rank_join {E : Type*} [AddCommGroup E] [Module ℂ E]
    {ι : Type*} [Fintype ι] (x p : E) (z : ℂ) (c : ι → ℂ) (v : ι → E)
    (hp : p=∑ i,v i) :
    (∑ i,c i • v i)-z • (x-p)= -z • x+∑ i,(c i+z) • v i := by
  rw [hp]
  simp only [add_smul,Finset.sum_add_distrib,Finset.smul_sum,smul_sub,neg_smul]
  abel

private theorem actual_resolvent_rank (F : Index) (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z= -z⁻¹ • (1 : Op)+
      ∑ i : SpectralIndex F, (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  let y := (supportSpan F).orthogonalProjectionOnto x
  let r := FullYSourceResolventGraphSplice.resolvent (supportAction F) z y
  have hs := congrArg (supportSpan F).subtypeL ((sourceBasis F).sum_repr r)
  simp only [map_sum,map_smul] at hs
  have hc (i : SpectralIndex F) :
      (sourceBasis F).repr r i=
        ((channelValue F (some i) : ℂ)-z)⁻¹*(sourceBasis F).repr y i :=
    SourceFiniteResolventEnergy.coordinate_resolvent (supportAction F) (support_action_selfAdjoint F) z hz y i
  simp_rw [hc,mul_smul] at hs
  have hp : supportProjection F x=
      ∑ i : SpectralIndex F, inner ℂ (sourceBasis F i : H) x • (sourceBasis F i : H) := by
    have h := congrArg (fun A : Op => A x) ((sourceBasis F).starProjection_eq_sum_rankOne)
    simpa only [supportProjection,sum_apply,rankOne_apply] using! h
  have hr : finiteResolvent F z (supportProjection F x)=(r : H) :=
    (support_resolvent F z hz y).symm
  change (∑ i, (((channelValue F (some i) : ℂ)-z)⁻¹) •
    (sourceBasis F).repr y i • (sourceBasis F i : H))=(r : H) at hs
  trans finiteResolvent F z (supportProjection F x)-z⁻¹ • escapeProjection F x
  · simpa only [neg_smul,sub_eq_add_neg] using! resolvent_split F z hz x
  trans (r : H)-z⁻¹ • escapeProjection F x
  · exact congrArg (fun q : H => q-z⁻¹ • escapeProjection F x) hr
  trans (∑ i, (((channelValue F (some i) : ℂ)-z)⁻¹) •
    (sourceBasis F).repr y i • (sourceBasis F i : H))-z⁻¹ • escapeProjection F x
  · exact congrArg (fun q : H => q-z⁻¹ • escapeProjection F x) hs.symm
  simp only [y,basis_coefficient,escapeProjection,sub_apply,one_apply_eq_self,
    sum_apply,add_apply,smul_apply,rankOne_apply]
  exact rank_join x (supportProjection F x) z⁻¹
    (fun i : SpectralIndex F => ((channelValue F (some i) : ℂ)-z)⁻¹)
    (fun i => inner ℂ (sourceBasis F i : H) x • (sourceBasis F i : H)) hp

theorem actual_moving_compression (F : Index) (t : ℝ) :
    compressionOrbitJet F 0 t=
      (hilbertFlow ((3/2 : ℝ)*t)).conjStarAlgEquiv (GaussGradedCompression.compression F) := by
  classical
  let U := hilbertFlow ((3/2 : ℝ)*t)
  apply ContinuousLinearMap.ext
  intro x
  change _=U (GaussGradedCompression.compression F (U.symm x))
  rw [actual_compression_spectral]
  simp only [compressionOrbitJet,rankJet,frame_zero,eigen_test_embed,sum_apply,smul_apply,
    map_sum,map_smul,rankOne_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [←U.inner_map_map (sourceBasis F i : H) (U.symm x),U.apply_symm_apply]

theorem actual_moving_resolvent (F : Index) (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    resolventOrbitJet F z 0 t=
      (hilbertFlow ((3/2 : ℝ)*t)).conjStarAlgEquiv (finiteResolvent F z) := by
  classical
  let U := hilbertFlow ((3/2 : ℝ)*t)
  apply ContinuousLinearMap.ext
  intro x
  change _=U (finiteResolvent F z (U.symm x))
  rw [actual_resolvent_rank F z hz]
  simp only [resolventOrbitJet,rankJet,frame_zero,eigen_test_embed,sum_apply,smul_apply,
    add_apply,one_apply_eq_self,if_true,map_add,map_sum,map_smul,U.apply_symm_apply,rankOne_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [←U.inner_map_map (sourceBasis F i : H) (U.symm x),U.apply_symm_apply]



open SourceFixedJetBudget SourceCoframeCompressionCovariance SourceCoframeScaleAction
open SourceJointScaleBudget

/-- Original coframe covariance identifies the moving finite family; the index is never discarded. -/
theorem moving_compression_source (F : Index) (s : ℝ) :
    compressionOrbitJet F 0 s=
      sourceCompression (mapFinsetFlow ((3/2 : ℝ)*s) F)
        (conjugation ((3/2 : ℝ)*s) diagonalAction) := by
  rw [source_compression_conjugation,actual_moving_compression]
  have he : sourceCompression F diagonalAction=GaussGradedCompression.compression F := by
    simpa only [scaledCompression,source_scale_one] using! actual_compression_return F
  exact congrArg (hilbertFlow ((3/2 : ℝ)*s)).conjStarAlgEquiv he.symm

@[simp] theorem resolvent_orbit_zero (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventOrbitJet F z 0 0=finiteResolvent F z := by
  rw [actual_moving_resolvent F z hz]
  apply ContinuousLinearMap.ext
  intro x
  change hilbertFlow ((3/2 : ℝ)*0)
    (finiteResolvent F z ((hilbertFlow ((3/2 : ℝ)*0)).symm x))=finiteResolvent F z x
  have he : (hilbertFlow 0).symm x=x := by
    apply (hilbertFlow 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hilbertFlow_zero]
  rw [mul_zero,he,hilbertFlow_zero]

def pairJet (F : Index) (z : ℂ) (n : ℕ) (k g : QuantumTest) (t : ℝ) : ℂ :=
  inner ℂ (embed k) (resolventOrbitJet F z n t (embed g))

private theorem pair_jet_derivative (F : Index) (z : ℂ) (n : ℕ)
    (k g : QuantumTest) (t : ℝ) :
    HasDerivAt (pairJet F z n k g) (pairJet F z (n+1) k g t) t := by
  exact (((innerSL ℂ (embed k)).comp (ContinuousLinearMap.apply ℂ H (embed g))).restrictScalars ℝ).hasFDerivAt
    |>.comp_hasDerivAt t (moving_resolvent_derivative F z n t)

private theorem fixed_profile_chain (F : Index) (z : ℂ) (n : ℕ)
    (k g : QuantumTest) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ((-3/2 : ℝ)^n) • profileJet n 0 0 F z k g ((-3/2 : ℝ)*s))
      (((-3/2 : ℝ)^(n+1)) • profileJet (n+1) 0 0 F z k g ((-3/2 : ℝ)*t)) t := by
  have ht : HasDerivAt (fun s : ℝ => (-3/2 : ℝ)*s) (-3/2 : ℝ) t := by
    simpa only [id_eq,mul_one] using! (hasDerivAt_id t).const_mul (-3/2 : ℝ)
  have h := ((profile_jet_derivative n 0 0 F z k g ((-3/2 : ℝ)*t)).scomp t ht).const_smul
    ((-3/2 : ℝ)^n)
  simpa only [pow_succ,smul_smul] using! h

/-- Every operator jet is read against fixed source jets, with the exact scale-time factor. -/
theorem actual_moving_pair_jet (F : Index) (z : ℂ) (hz : z.im≠0) (n : ℕ)
    (k g : QuantumTest) (t : ℝ) :
    pairJet F z n k g t=
      ((-3/2 : ℝ)^n) • profileJet n 0 0 F z k g ((-3/2 : ℝ)*t) := by
  induction n generalizing t with
  | zero =>
    unfold pairJet
    rw [actual_moving_resolvent F z hz,moving_resolvent_pair]
    simp only [pow_zero,one_smul,profileJet,neg_mul,neg_div]
  | succ n ih =>
    have he : pairJet F z n k g=
        fun s : ℝ => ((-3/2 : ℝ)^n) • profileJet n 0 0 F z k g ((-3/2 : ℝ)*s) := funext ih
    have h := pair_jet_derivative F z n k g t
    rw [he] at h
    exact h.unique (fixed_profile_chain F z n k g t)

theorem rank_jet_three (f g : QuantumTest) (t : ℝ) :
    rankJet 3 0 0 f g t=
      rankOne ℂ (frameJet 3 f t) (frameJet 0 g t)+
      3*rankOne ℂ (frameJet 2 f t) (frameJet 1 g t)+
      3*rankOne ℂ (frameJet 1 f t) (frameJet 2 g t)+
      rankOne ℂ (frameJet 0 f t) (frameJet 3 g t) := by
  simp only [rankJet]
  noncomm_ring



open SourceMixedNativeReturn

private def productJet {R : Type*} [Ring R] : ℕ → ℕ → ℕ → (ℕ → ℝ → R) → (ℕ → ℝ → R) → ℝ → R
  | 0,r,s,a,b,t => a r t*b s t
  | n+1,r,s,a,b,t => productJet n (r+1) s a b t+productJet n r (s+1) a b t

private theorem product_jet_derivative (a b : ℕ → ℝ → Op)
    (ha : ∀ n t, HasDerivAt (a n) (a (n+1) t) t)
    (hb : ∀ n t, HasDerivAt (b n) (b (n+1) t) t) (n r s : ℕ) (t : ℝ) :
    HasDerivAt (productJet n r s a b) (productJet (n+1) r s a b t) t := by
  induction n generalizing r s with
  | zero => exact (ha r t).mul (hb s t)
  | succ n ih => exact (ih (r+1) s).add (ih r (s+1))

private def shiftedJet (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  compressionOrbitJet F n t-(if n=0 then z • (1 : Op) else 0)

private theorem shifted_jet_derivative (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) :
    HasDerivAt (shiftedJet F z n) (shiftedJet F z (n+1) t) t := by
  have h := (moving_compression_derivative F n t).sub
    (hasDerivAt_const t (if n=0 then z • (1 : Op) else 0))
  simpa only [shiftedJet,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,sub_zero] using! h

private theorem actual_inverse_product (F : Index) (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    shiftedJet F z 0 t*resolventOrbitJet F z 0 t=1 := by
  let U := (hilbertFlow ((3/2 : ℝ)*t)).conjStarAlgEquiv
  have h := congrArg U (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change U ((GaussGradedCompression.compression F-z • (1 : Op))*finiteResolvent F z)=U 1 at h
  have hu : U (GaussGradedCompression.compression F-z • (1 : Op))=
      U (GaussGradedCompression.compression F)-z • (1 : Op) := by
    apply ContinuousLinearMap.ext
    intro x
    change hilbertFlow ((3/2 : ℝ)*t)
      ((GaussGradedCompression.compression F-z • (1 : Op))
        ((hilbertFlow ((3/2 : ℝ)*t)).symm x))=_
    simp only [sub_apply,smul_apply,one_apply_eq_self,map_sub,map_smul,
      LinearIsometryEquiv.apply_symm_apply]
    rfl
  rw [map_mul,hu,map_one] at h
  simpa only [shiftedJet,if_true,actual_moving_compression,actual_moving_resolvent F z hz] using! h

private theorem inverse_product_jet (F : Index) (z : ℂ) (hz : z.im≠0) (n : ℕ) (t : ℝ) :
    productJet n 0 0 (shiftedJet F z) (resolventOrbitJet F z) t=
      if n=0 then 1 else 0 := by
  induction n generalizing t with
  | zero => exact actual_inverse_product F z hz t
  | succ n ih =>
    have he : productJet n 0 0 (shiftedJet F z) (resolventOrbitJet F z)=
        fun _ : ℝ => if n=0 then 1 else 0 := funext ih
    have h := product_jet_derivative (shiftedJet F z) (resolventOrbitJet F z)
      (shifted_jet_derivative F z) (moving_resolvent_derivative F z) n 0 0 t
    rw [he] at h
    simpa only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false] using!
      h.unique (hasDerivAt_const t (if n=0 then (1 : Op) else 0))

/-- B is generated from the original finite eigenframe and the actual source commutator jet. -/
def compressionCorrection (F : Index) (n : ℕ) : Op :=
  compressionOrbitJet F n 0-compressionJet F n

theorem compression_correction_explicit (F : Index) :
    compressionCorrection F 3=
      (∑ i : SpectralIndex F, (channelValue F (some i) : ℂ) • (
        rankOne ℂ (frameJet 3 (eigenTest F i) 0) (frameJet 0 (eigenTest F i) 0)+
        3*rankOne ℂ (frameJet 2 (eigenTest F i) 0) (frameJet 1 (eigenTest F i) 0)+
        3*rankOne ℂ (frameJet 1 (eigenTest F i) 0) (frameJet 2 (eigenTest F i) 0)+
        rankOne ℂ (frameJet 0 (eigenTest F i) 0) (frameJet 3 (eigenTest F i) 0)))-
      sourceCompression F (jet 3 diagonalAction) := by
  simp only [compressionCorrection,compressionOrbitJet,rank_jet_three,compressionJet]



private theorem product_jet_two {R : Type*} [Ring R] (a b : ℕ → ℝ → R) (t : ℝ) :
    productJet 2 0 0 a b t=a 2 t*b 0 t+2*a 1 t*b 1 t+a 0 t*b 2 t := by
  simp only [productJet]
  noncomm_ring

private theorem product_jet_three {R : Type*} [Ring R] (a b : ℕ → ℝ → R) (t : ℝ) :
    productJet 3 0 0 a b t=a 3 t*b 0 t+3*a 2 t*b 1 t+3*a 1 t*b 2 t+a 0 t*b 3 t := by
  simp only [productJet]
  noncomm_ring

private theorem recover_inverse_jets {R : Type*} [Ring R] (l r a b c u v w : R)
    (hr : r*l=1) (h1 : a*r+l*u=0) (h2 : b*r+2*a*u+l*v=0)
    (h3 : c*r+3*b*u+3*a*v+l*w=0) :
    u=inverseJet1 r a ∧ v=inverseJet2 r a b ∧ w=inverseJet3 r a b c := by
  have hrx (x : R) : r*(l*x)=x := by rw [←mul_assoc,hr,one_mul]
  have hu : u=inverseJet1 r a := by
    calc
      u=r*(l*u) := (hrx u).symm
      _ = r*(-(a*r)) := congrArg (fun x => r*x) (eq_neg_of_add_eq_zero_right h1)
      _ = _ := by unfold inverseJet1; noncomm_ring
  have hv : v=inverseJet2 r a b := by
    calc
      v=r*(l*v) := (hrx v).symm
      _ = r*(-(b*r+2*a*u)) := congrArg (fun x => r*x) (eq_neg_of_add_eq_zero_right h2)
      _ = _ := by rw [hu]; unfold inverseJet1 inverseJet2; noncomm_ring
  refine ⟨hu,hv,?_⟩
  calc
    w=r*(l*w) := (hrx w).symm
    _ = r*(-(c*r+3*b*u+3*a*v)) := congrArg (fun x => r*x) (eq_neg_of_add_eq_zero_right h3)
    _ = _ := by rw [hu,hv]; unfold inverseJet1 inverseJet2 inverseJet3; noncomm_ring

@[simp] theorem compression_orbit_zero (F : Index) :
    compressionOrbitJet F 0 0=GaussGradedCompression.compression F := by
  rw [actual_moving_compression]
  apply ContinuousLinearMap.ext
  intro x
  change hilbertFlow ((3/2 : ℝ)*0)
    (GaussGradedCompression.compression F ((hilbertFlow ((3/2 : ℝ)*0)).symm x))=_
  have he : (hilbertFlow 0).symm x=x := by
    apply (hilbertFlow 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hilbertFlow_zero]
  rw [mul_zero,he,hilbertFlow_zero]

/-- Differentiating the actual finite inverse identity pays all four inverse-jet monomials. -/
theorem actual_moving_inverse_jets (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventOrbitJet F z 1 0=inverseJet1 (finiteResolvent F z) (compressionOrbitJet F 1 0) ∧
    resolventOrbitJet F z 2 0=inverseJet2 (finiteResolvent F z)
      (compressionOrbitJet F 1 0) (compressionOrbitJet F 2 0) ∧
    resolventOrbitJet F z 3 0=inverseJet3 (finiteResolvent F z)
      (compressionOrbitJet F 1 0) (compressionOrbitJet F 2 0) (compressionOrbitJet F 3 0) := by
  have h1 := inverse_product_jet F z hz 1 0
  have h2 := inverse_product_jet F z hz 2 0
  have h3 := inverse_product_jet F z hz 3 0
  rw [product_jet_two] at h2
  rw [product_jet_three] at h3
  simp only [productJet,shiftedJet,show (0 : ℕ)+1=1 from rfl,
    show (1 : ℕ)≠0 from by omega,show (2 : ℕ)≠0 from by omega,show (3 : ℕ)≠0 from by omega,
    if_true,if_false,sub_zero,compression_orbit_zero,resolvent_orbit_zero F z hz] at h1 h2 h3
  exact recover_inverse_jets _ _ _ _ _ _ _ _
    (resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz) h1 h2 h3



open MeasureTheory

theorem actual_moving_pair_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (n : ℕ)
    (k g : QuantumTest) (t : ℝ) :
    (∫ ω : ℝ, ‖pairJet F (line μ ω) n k g t‖^2) ≤
      ‖(-3/2 : ℝ)^n‖^2*((Real.pi/μ)*profileJetBudget n 0 0 k g) := by
  have he (ω : ℝ) : ‖pairJet F (line μ ω) n k g t‖^2=
      ‖(-3/2 : ℝ)^n‖^2*‖profileJet n 0 0 F (line μ ω) k g ((-3/2 : ℝ)*t)‖^2 := by
    rw [actual_moving_pair_jet F (line μ ω) (by simpa only [line_im] using hμ.ne')]
    rw [norm_smul,mul_pow]
  simp_rw [he]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (actual_profile_jet_energy n 0 0 F μ hμ k g _)
    (sq_nonneg _)

section CorrectionAlgebra
variable {R : Type*} [Ring R]

def inverseFlux1 (r p : R) : R := r*p*r

def inverseFlux2 (r a p q : R) : R :=
  -2*r*p*r*a*r-2*r*a*r*p*r-2*r*p*r*p*r+r*q*r

def inverseFlux3 (r a b p q w : R) : R :=
  6*(r*p*r*a*r*a*r+r*a*r*p*r*a*r+r*a*r*a*r*p*r+
    r*p*r*p*r*a*r+r*p*r*a*r*p*r+r*a*r*p*r*p*r+r*p*r*p*r*p*r)-
  3*(r*q*r*a*r+r*b*r*p*r+r*q*r*p*r+r*p*r*b*r+r*a*r*q*r+r*p*r*q*r)+r*w*r

private theorem inverse_flux_algebra (r a b c p q w : R) :
    inverseJet1 r a-inverseJet1 r (a+p)=inverseFlux1 r p ∧
    inverseJet2 r a b-inverseJet2 r (a+p) (b+q)=inverseFlux2 r a p q ∧
    inverseJet3 r a b c-inverseJet3 r (a+p) (b+q) (c+w)=inverseFlux3 r a b p q w := by
  constructor
  · unfold inverseJet1 inverseFlux1
    noncomm_ring
  constructor
  · unfold inverseJet2 inverseFlux2
    noncomm_ring
  · unfold inverseJet3 inverseFlux3
    noncomm_ring
end CorrectionAlgebra


def inverseCorrection (F : Index) (z : ℂ) (j : Fin 4) : Op :=
  inverseJet F z j-resolventOrbitJet F z j 0

theorem generated_inverse_corrections (F : Index) (z : ℂ) (hz : z.im≠0) :
    inverseCorrection F z 0=0 ∧
    inverseCorrection F z 1=inverseFlux1 (finiteResolvent F z) (compressionCorrection F 1) ∧
    inverseCorrection F z 2=inverseFlux2 (finiteResolvent F z) (compressionJet F 1)
      (compressionCorrection F 1) (compressionCorrection F 2) ∧
    inverseCorrection F z 3=inverseFlux3 (finiteResolvent F z)
      (compressionJet F 1) (compressionJet F 2)
      (compressionCorrection F 1) (compressionCorrection F 2) (compressionCorrection F 3) := by
  have hc (j : ℕ) : compressionOrbitJet F j 0=compressionJet F j+compressionCorrection F j := by
    dsimp only [compressionCorrection]
    abel
  have hj := actual_moving_inverse_jets F z hz
  have ha := inverse_flux_algebra (finiteResolvent F z)
    (compressionJet F 1) (compressionJet F 2) (compressionJet F 3)
    (compressionCorrection F 1) (compressionCorrection F 2) (compressionCorrection F 3)
  constructor
  · change finiteResolvent F z-resolventOrbitJet F z 0 0=0
    rw [resolvent_orbit_zero F z hz,sub_self]
  change (inverseJet1 (finiteResolvent F z) (compressionJet F 1)-resolventOrbitJet F z 1 0=
    inverseFlux1 (finiteResolvent F z) (compressionCorrection F 1)) ∧
    (inverseJet2 (finiteResolvent F z) (compressionJet F 1) (compressionJet F 2)-
      resolventOrbitJet F z 2 0=inverseFlux2 (finiteResolvent F z) (compressionJet F 1)
      (compressionCorrection F 1) (compressionCorrection F 2)) ∧
    (inverseJet3 (finiteResolvent F z) (compressionJet F 1) (compressionJet F 2)
      (compressionJet F 3)-resolventOrbitJet F z 3 0=
      inverseFlux3 (finiteResolvent F z) (compressionJet F 1) (compressionJet F 2)
        (compressionCorrection F 1) (compressionCorrection F 2) (compressionCorrection F 3))
  simpa only [hj.1,hj.2.1,hj.2.2,hc] using! ha




def jetWord {R : Type*} [Ring R] (r : Fin 4 → R) : R := r 3+3*r 2-r 1-3*r 0

private theorem endpoint_word_algebra {R : Type*} [Ring R] (r : Fin 4 → R) (t : R) :
    endpointJet3 (r 0) (r 1) (r 2) (r 3) t (-3*t) (9*t) (-27*t)+
      12*endpointJet2 (r 0) (r 1) (r 2) t (-3*t) (9*t)+
      44*endpointJet1 (r 0) (r 1) t (-3*t)+48*endpointJet0 (r 0) t=
        t*jetWord r-jetWord r*t := by
  unfold endpointJet0 endpointJet1 endpointJet2 endpointJet3 jetWord
  noncomm_ring

private theorem nat_smul_operator (n : ℕ) (A : Op) : (n : ℂ) • A=(n : Op)*A :=
  (Nat.cast_smul_eq_nsmul ℂ n A).trans (nsmul_eq_mul n A)

def orbitWord (F : Index) (z : ℂ) : Op := jetWord (fun j => resolventOrbitJet F z j 0)
def correctionWord (F : Index) (z : ℂ) : Op := jetWord (inverseCorrection F z)

theorem original_endpoint_word (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) :
    endpointPolynomial sharp m ell F g z=
      Complex.I • (sourceRead F g (primitive sharp m ell)*jetWord (inverseJet F z)-
        jetWord (inverseJet F z)*sourceRead F g (primitive sharp m ell)) := by
  let T := sourceRead F g (primitive sharp m ell)
  have h0 : primitiveJet sharp m ell F g 0=T := by simp only [primitiveJet,pow_zero,one_smul,T]
  have h1 : primitiveJet sharp m ell F g 1= -3*T := by
    change ((-3 : ℂ)^1) • T=_
    norm_num only [pow_one]
    calc
      (-3 : ℂ) • T= -((3 : ℂ) • T) := by simpa only using! neg_smul (3 : ℂ) T
      _ = -(3*T) := congrArg Neg.neg (nat_smul_operator 3 T)
      _ = _ := by simpa only using! (neg_mul (3 : Op) T).symm
  have h2 : primitiveJet sharp m ell F g 2=9*T := by
    change ((-3 : ℂ)^2) • T=_
    norm_num only [neg_pow,even_two,Even.neg_pow]
    exact nat_smul_operator 9 T
  have h3 : primitiveJet sharp m ell F g 3= -27*T := by
    change ((-3 : ℂ)^3) • T=_
    norm_num
    calc
      (-27 : ℂ) • T= -((27 : ℂ) • T) := by simpa only using! neg_smul (27 : ℂ) T
      _ = -(27*T) := congrArg Neg.neg (nat_smul_operator 27 T)
      _ = _ := by simpa only using! (neg_mul (27 : Op) T).symm
  simpa only [endpointPolynomial,h0,h1,h2,h3] using!
    congrArg (fun A : Op => Complex.I • A) (endpoint_word_algebra (inverseJet F z) T)

private theorem jet_word_sub {R : Type*} [Ring R] (r s : Fin 4 → R) :
    jetWord (fun j => r j-s j)=jetWord r-jetWord s := by
  unfold jetWord
  noncomm_ring

private theorem commutator_add {R : Type*} [Ring R] (t a b : R) :
    t*(a+b)-(a+b)*t=(t*a-a*t)+(t*b-b*t) := by noncomm_ring

private theorem endpoint_partition {R : Type*} [Ring R] [Module ℂ R]
    (r s : Fin 4 → R) (t : R) :
    Complex.I • (t*jetWord r-jetWord r*t)=
      Complex.I • (t*jetWord s-jetWord s*t)+
      Complex.I • (t*jetWord (fun j => r j-s j)-jetWord (fun j => r j-s j)*t) := by
  have hw : jetWord r=jetWord s+jetWord (fun j => r j-s j) := by rw [jet_word_sub]; abel
  conv_lhs => rw [hw]
  rw [commutator_add,smul_add]

theorem original_endpoint_moving_return (sharp : Bool) (m ell : ℕ) (F : Index)
    (g : diagonal.domain) (z : ℂ) :
    endpointPolynomial sharp m ell F g z=
      Complex.I • (sourceRead F g (primitive sharp m ell)*orbitWord F z-
        orbitWord F z*sourceRead F g (primitive sharp m ell))+
      Complex.I • (sourceRead F g (primitive sharp m ell)*correctionWord F z-
        correctionWord F z*sourceRead F g (primitive sharp m ell)) := by
  exact (original_endpoint_word sharp m ell F g z).trans
    (endpoint_partition (inverseJet F z) (fun j => resolventOrbitJet F z j 0)
      (sourceRead F g (primitive sharp m ell)))


open GaussNativeForm SourceCurrentEndpointEnergy

private theorem operator_word_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r : Fin 4 → E →L[ℂ] E) (x y : E) :
    inner ℂ x (jetWord r y)=jetWord (fun j => inner ℂ x (r j y)) := by
  have h3 (A : E →L[ℂ] E) : (3 : E →L[ℂ] E)*A=(3 : ℂ) • A :=
    ((Nat.cast_smul_eq_nsmul ℂ 3 A).trans (nsmul_eq_mul 3 A)).symm
  simp only [jetWord,h3,sub_apply,add_apply,smul_apply,inner_sub_right,inner_add_right,inner_smul_right]

def fixedProfileWord (F : Index) (z : ℂ) (k g : QuantumTest) : ℂ :=
  jetWord (fun j : Fin 4 => ((-3/2 : ℝ)^(j : ℕ)) • profileJet j 0 0 F z k g 0)

theorem actual_orbit_word_pair (F : Index) (z : ℂ) (hz : z.im≠0) (k g : QuantumTest) :
    inner ℂ (embed k) (orbitWord F z (embed g))=fixedProfileWord F z k g := by
  trans jetWord (fun j : Fin 4 => pairJet F z j k g 0)
  · exact operator_word_pair _ _ _
  apply congrArg jetWord
  funext j
  simpa only [mul_zero] using! actual_moving_pair_jet F z hz j k g 0

private theorem core_embed (g : diagonal.domain) : embed (coreEquiv.symm g)=(g : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply g)

private theorem source_read_pair_projection (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (x : H) :
    inner ℂ (k : H) (sourceRead F g (primitive sharp m ell) x)=
      inner ℂ (embed (primitiveAdjoint sharp m ell (coreEquiv.symm k)))
        ((inputSpan F g).starProjection x) := by
  let q : diagonal.domain :=
    Submodule.inclusion (input_span_core F g) ((inputSpan F g).orthogonalProjectionOnto x)
  have h := primitive_pair sharp m ell (coreEquiv.symm k) (coreEquiv.symm q)
  change inner ℂ (embed (coreEquiv.symm k))
    (embed (primitive sharp m ell (coreEquiv.symm q)))=
      inner ℂ (embed (primitiveAdjoint sharp m ell (coreEquiv.symm k))) (embed (coreEquiv.symm q)) at h
  simpa only [core_embed] using! h

def fixedEndpointProfile (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) : ℂ :=
  fixedProfileWord F z (primitiveAdjoint sharp m ell (coreEquiv.symm k)) (coreEquiv.symm g)-
    fixedProfileWord F z (coreEquiv.symm k) (primitive sharp m ell (coreEquiv.symm g))

def movingProjectionShadow (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) : ℂ :=
  inner ℂ ((inputSpan F g).starProjection
      (embed (primitiveAdjoint sharp m ell (coreEquiv.symm k)))-
      embed (primitiveAdjoint sharp m ell (coreEquiv.symm k)))
    (orbitWord F z (g : H))

/-- Every moving-projector term is retained with its original sign, including the primitive input read. -/
def generatedEndpointFlux (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) : ℂ :=
  movingProjectionShadow sharp m ell F g k z+
    inner ℂ (k : H) ((sourceRead F g (primitive sharp m ell)*correctionWord F z-
      correctionWord F z*sourceRead F g (primitive sharp m ell)) (g : H))

private theorem moving_endpoint_pair (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    inner ℂ (k : H) ((sourceRead F g (primitive sharp m ell)*orbitWord F z-
      orbitWord F z*sourceRead F g (primitive sharp m ell)) (g : H))=
    fixedEndpointProfile sharp m ell F g k z+movingProjectionShadow sharp m ell F g k z := by
  let a := embed (primitiveAdjoint sharp m ell (coreEquiv.symm k))
  have hl := source_read_pair_projection sharp m ell F g k (orbitWord F z (g : H))
  have hp := (inputSpan F g).inner_starProjection_left_eq_right a (orbitWord F z (g : H))
  change inner ℂ (k : H) (sourceRead F g (primitive sharp m ell) (orbitWord F z (g : H)))=
    inner ℂ a ((inputSpan F g).starProjection (orbitWord F z (g : H))) at hl
  have hl' : inner ℂ (k : H) (sourceRead F g (primitive sharp m ell) (orbitWord F z (g : H)))=
      inner ℂ a (orbitWord F z (g : H))+movingProjectionShadow sharp m ell F g k z := by
    rw [hl,←hp]
    unfold movingProjectionShadow
    change inner ℂ ((inputSpan F g).starProjection a) (orbitWord F z (g : H))=
      inner ℂ a (orbitWord F z (g : H))+
        inner ℂ ((inputSpan F g).starProjection a-a) (orbitWord F z (g : H))
    rw [inner_sub_left]
    ring
  change inner ℂ (k : H) (sourceRead F g (primitive sharp m ell) (orbitWord F z (g : H))-
    orbitWord F z (sourceRead F g (primitive sharp m ell) (g : H)))=_
  rw [inner_sub_right,hl',source_read_input]
  have hleft := actual_orbit_word_pair F z hz
    (primitiveAdjoint sharp m ell (coreEquiv.symm k)) (coreEquiv.symm g)
  have hright := actual_orbit_word_pair F z hz
    (coreEquiv.symm k) (primitive sharp m ell (coreEquiv.symm g))
  simp only [core_embed] at hleft hright
  change inner ℂ a (orbitWord F z (g : H))=_ at hleft
  rw [hleft,hright]
  unfold fixedEndpointProfile
  ring

/-- The original fixed-F endpoint is the paid fixed-source profile plus the generated full flux. -/
theorem actual_endpoint_fixed_profiles (sharp : Bool) (m ell : ℕ) (F : Index)
    (g k : diagonal.domain) (z : ℂ) (hz : z.im≠0) :
    inner ℂ (k : H) (endpointPolynomial sharp m ell F g z (g : H))=
      Complex.I*(fixedEndpointProfile sharp m ell F g k z+
        generatedEndpointFlux sharp m ell F g k z) := by
  have h := congrArg (fun A : Op => inner ℂ (k : H) (A (g : H)))
    (original_endpoint_moving_return sharp m ell F g z)
  simp only [add_apply,smul_apply,inner_add_right,inner_smul_right] at h
  rw [moving_endpoint_pair sharp m ell F g k z hz] at h
  exact h.trans (by unfold generatedEndpointFlux; ring)



/-- The original source filter contains this fixed cutoff-dependent adjoint source cofinally. -/
theorem projection_shadow_eventually_zero (sharp : Bool) (m ell : ℕ)
    (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ,
      movingProjectionShadow sharp m ell F g k z=0 := by
  let a : diagonal.domain := coreEquiv (primitiveAdjoint sharp m ell (coreEquiv.symm k))
  filter_upwards [source_eventually_mem_support a] with F hF
  intro z
  have hp : (inputSpan F g).starProjection (a : H)=(a : H) :=
    Submodule.starProjection_eq_self_iff.mpr (Submodule.mem_sup_left hF)
  change inner ℂ ((inputSpan F g).starProjection (a : H)-(a : H)) (orbitWord F z (g : H))=0
  rw [hp,sub_self,inner_zero_left]

theorem actual_endpoint_cofinal_return (sharp : Bool) (m ell : ℕ) (g k : diagonal.domain) :
    ∀ᶠ F in (sourceFilter : Filter Index), ∀ z : ℂ, ∀ _hz : z.im≠0,
      inner ℂ (k : H) (endpointPolynomial sharp m ell F g z (g : H))=
        Complex.I*(fixedEndpointProfile sharp m ell F g k z+
          inner ℂ (k : H) ((sourceRead F g (primitive sharp m ell)*correctionWord F z-
            correctionWord F z*sourceRead F g (primitive sharp m ell)) (g : H))) := by
  filter_upwards [projection_shadow_eventually_zero sharp m ell g k] with F hF
  intro z hz
  simpa only [generatedEndpointFlux,hF z,zero_add] using!
    actual_endpoint_fixed_profiles sharp m ell F g k z hz



theorem fixed_profile_word_expansion (F : Index) (z : ℂ) (k g : QuantumTest) :
    fixedProfileWord F z k g=
      (-27/8 : ℂ)*profileJet 3 0 0 F z k g 0+
      (27/4 : ℂ)*profileJet 2 0 0 F z k g 0+
      (3/2 : ℂ)*profileJet 1 0 0 F z k g 0-
      3*profileJet 0 0 0 F z k g 0 := by
  change ((-3/2 : ℝ)^3) • profileJet 3 0 0 F z k g 0+
    3*(((-3/2 : ℝ)^2) • profileJet 2 0 0 F z k g 0)-
    ((-3/2 : ℝ)^1) • profileJet 1 0 0 F z k g 0-
    3*(((-3/2 : ℝ)^0) • profileJet 0 0 0 F z k g 0)=_
  norm_num [Complex.real_smul]
  ring

theorem compression_correction_first_second (F : Index) :
    compressionCorrection F 1=
      (∑ i : SpectralIndex F, (channelValue F (some i) : ℂ) • (
        rankOne ℂ (frameJet 1 (eigenTest F i) 0) (frameJet 0 (eigenTest F i) 0)+
        rankOne ℂ (frameJet 0 (eigenTest F i) 0) (frameJet 1 (eigenTest F i) 0)))-
      sourceCompression F (jet 1 diagonalAction) ∧
    compressionCorrection F 2=
      (∑ i : SpectralIndex F, (channelValue F (some i) : ℂ) • (
        rankOne ℂ (frameJet 2 (eigenTest F i) 0) (frameJet 0 (eigenTest F i) 0)+
        2*rankOne ℂ (frameJet 1 (eigenTest F i) 0) (frameJet 1 (eigenTest F i) 0)+
        rankOne ℂ (frameJet 0 (eigenTest F i) 0) (frameJet 2 (eigenTest F i) 0)))-
      sourceCompression F (jet 2 diagonalAction) := by
  constructor
  · rfl
  · unfold compressionCorrection compressionOrbitJet compressionJet
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    simp only [rankJet]
    noncomm_ring



private def EnergyTail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
    (∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2)) ≤ ENNReal.ofReal ε

private theorem energy_tail_smul (f : ℕ → ℕ → Index → ℝ → ℂ) (c : ℂ)
    (hf : EnergyTail f) : EnergyTail (fun m ell F w => c*f m ell F w) := by
  intro ε hε
  have hc : 0<‖c‖^2+1 := by positivity
  have hδ : 0<ε/(‖c‖^2+1) := div_pos hε hc
  obtain ⟨N,hN⟩ := hf (ε/(‖c‖^2+1)) hδ
  refine ⟨N,fun m hm ell hell F => ?_⟩
  simp only [norm_mul,mul_pow,ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hb := hN m hm ell hell F
  apply le_trans (show ENNReal.ofReal (‖c‖^2)*(∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2)) ≤
    ENNReal.ofReal (‖c‖^2)*ENNReal.ofReal (ε/(‖c‖^2+1)) by gcongr)
  rw [←ENNReal.ofReal_mul (sq_nonneg ‖c‖)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (‖c‖^2+1)*(ε/(‖c‖^2+1)) :=
      mul_le_mul_of_nonneg_right (by linarith) hδ.le
    _ = ε := mul_div_cancel₀ ε hc.ne'

private theorem energy_tail_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hc : ∀ m ell F, Continuous (f m ell F))
    (hf : EnergyTail f) (hg : EnergyTail g) : EnergyTail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell F => ?_⟩
  have hl := h₁ m (le_trans (Nat.le_max_left _ _) hm) ell hell F
  have hr := h₂ m (le_trans (Nat.le_max_right _ _) hm) ell hell F
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact ENNReal.ofReal_le_ofReal (hp _ _)
    _ = ENNReal.ofReal 2*((∫⁻ w : ℝ, ENNReal.ofReal (‖f m ell F w‖^2))+
        (∫⁻ w : ℝ, ENNReal.ofReal (‖g m ell F w‖^2))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (‖f m ell F w‖^2)) := by
        simpa only [Pi.pow_apply] using! ((hc m ell F).norm.pow 2).measurable.ennreal_ofReal
      exact congrArg (fun x : ENNReal => ENNReal.ofReal 2*x) (lintegral_add_left hmeas _)
    _ ≤ ENNReal.ofReal 2*(ENNReal.ofReal (ε/4)+ENNReal.ofReal (ε/4)) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_add (by positivity : 0 ≤ ε/4) (by positivity : 0 ≤ ε/4),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring

private theorem fixed_word_continuous (F : Index) (μ : ℝ) (hμ : 0<μ) (k g : QuantumTest) :
    Continuous (fun w => fixedProfileWord F (line μ w) k g) := by
  simp_rw [fixed_profile_word_expansion]
  exact ((((profile_jet_frequency_continuous 3 0 0 F μ hμ k g 0).const_mul (-27/8)).add
    ((profile_jet_frequency_continuous 2 0 0 F μ hμ k g 0).const_mul (27/4))).add
    ((profile_jet_frequency_continuous 1 0 0 F μ hμ k g 0).const_mul (3/2))).sub
    ((profile_jet_frequency_continuous 0 0 0 F μ hμ k g 0).const_mul 3)

private theorem fixed_word_tail (μ : ℝ) (hμ : 0<μ) (a b : ℕ → ℕ → QuantumTest)
    (h : ∀ n : ℕ, EnergyTail (fun m ell F w => profileJet n 0 0 F (line μ w) (a m ell) (b m ell) 0)) :
    EnergyTail (fun m ell F w => fixedProfileWord F (line μ w) (a m ell) (b m ell)) := by
  let f (n : ℕ) (m ell : ℕ) (F : Index) (w : ℝ) := profileJet n 0 0 F (line μ w) (a m ell) (b m ell) 0
  have hc (n m ell : ℕ) (F : Index) : Continuous (f n m ell F) :=
    profile_jet_frequency_continuous n 0 0 F μ hμ (a m ell) (b m ell) 0
  have h3 := energy_tail_smul (f 3) (-27/8) (h 3)
  have h2 := energy_tail_smul (f 2) (27/4) (h 2)
  have h1 := energy_tail_smul (f 1) (3/2) (h 1)
  have h0 := energy_tail_smul (f 0) (-3) (h 0)
  have h32 := energy_tail_add _ _ (fun m ell F => (hc 3 m ell F).const_mul (-27/8)) h3 h2
  have h321 := energy_tail_add _ _ (fun m ell F =>
    ((hc 3 m ell F).const_mul (-27/8)).add ((hc 2 m ell F).const_mul (27/4))) h32 h1
  have h3210 := energy_tail_add _ _ (fun m ell F =>
    (((hc 3 m ell F).const_mul (-27/8)).add ((hc 2 m ell F).const_mul (27/4))).add
      ((hc 1 m ell F).const_mul (3/2))) h321 h0
  simpa only [EnergyTail,fixed_profile_word_expansion,sub_eq_add_neg,neg_mul,f] using! h3210

/-- The complete fixed-source part of the original third endpoint has a uniform all-frequency tail. -/
theorem actual_fixed_endpoint_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell → ∀ F : Index,
      (∫⁻ w : ℝ, ENNReal.ofReal (‖fixedEndpointProfile sharp m ell F g k (line μ w)‖^2)) ≤
        ENNReal.ofReal ε := by
  have hl : EnergyTail (fun m ell F w => fixedProfileWord F (line μ w)
      (primitiveAdjoint sharp m ell (coreEquiv.symm k)) (coreEquiv.symm g)) := by
    apply fixed_word_tail μ hμ
    intro n ε hε
    obtain ⟨N,hN⟩ := SourcePrimitiveJetTail.actual_left_primitive_profile_tail sharp n 0 0 μ hμ
      (coreEquiv.symm k) (coreEquiv.symm g) ε hε
    exact ⟨N,fun m hm ell hell F => hN m hm ell hell F 0⟩
  have hr : EnergyTail (fun m ell F w => fixedProfileWord F (line μ w)
      (coreEquiv.symm k) (primitive sharp m ell (coreEquiv.symm g))) := by
    apply fixed_word_tail μ hμ
    intro n ε hε
    obtain ⟨N,hN⟩ := SourcePrimitiveJetTail.actual_right_primitive_profile_tail sharp n 0 0 μ hμ
      (coreEquiv.symm k) (coreEquiv.symm g) ε hε
    exact ⟨N,fun m hm ell hell F => hN m hm ell hell F 0⟩
  have hn := energy_tail_smul _ (-1) hr
  have hsum := energy_tail_add _ _ (fun m ell F => fixed_word_continuous F μ hμ
    (primitiveAdjoint sharp m ell (coreEquiv.symm k)) (coreEquiv.symm g)) hl hn
  simpa only [EnergyTail,fixedEndpointProfile,neg_one_mul,sub_eq_add_neg] using! hsum



/-- Original endpoint consumer: after the explicitly generated inverse flux, its cofinal tail is paid. -/
theorem actual_endpoint_corrected_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) :
    ∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ, ENNReal.ofReal (‖
          inner ℂ (k : H) (endpointPolynomial sharp m ell F g (line μ w) (g : H))-
          Complex.I*inner ℂ (k : H)
            ((sourceRead F g (primitive sharp m ell)*correctionWord F (line μ w)-
              correctionWord F (line μ w)*sourceRead F g (primitive sharp m ell)) (g : H))‖^2)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_fixed_endpoint_tail sharp μ hμ g k ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [actual_endpoint_cofinal_return sharp m ell g k] with F hF
  have he (w : ℝ) := hF (line μ w) (by simpa only [line_im] using hμ.ne')
  simp_rw [he,mul_add,add_sub_cancel_right,norm_mul,Complex.norm_I,one_mul]
  exact hN m hm ell hell F

end LowEnergy.SourceMovingJetFlux
