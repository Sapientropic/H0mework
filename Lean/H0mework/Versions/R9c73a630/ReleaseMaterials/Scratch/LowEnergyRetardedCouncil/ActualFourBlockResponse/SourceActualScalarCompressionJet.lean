import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceScalarAffineScaleTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
noncomputable section
namespace LowEnergy.ActualScalarCompressionJet
open GaussCoreHilbert GaussCoreDifferential GaussDiagonalHistory GaussUnitaryHistory
open SourceActualResolventEnergy SourceJointResidualEnergy
open FullYSourceResolventGraphSplice SourceRetardedIncrement SourceResolventBandLimit
open SourceScalarAffineScaleTransport InnerProductSpace
open scoped InnerProductSpace Topology BigOperators

abbrev Op := H →L[ℂ] H

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
  | 0,r,s,f,g,t => rankOne ℂ (strongJet r f t) (strongJet s g t)
  | n+1,r,s,f,g,t => rankJet n (r+1) s f g t+rankJet n r (s+1) f g t

private theorem rank_jet_derivative (n r s : ℕ) (f g : QuantumTest) (t : ℝ) :
    HasDerivAt (rankJet n r s f g) (rankJet (n+1) r s f g t) t := by
  induction n generalizing r s with
  | zero => exact rank_derivative (strong_jet_derivative r f t) (strong_jet_derivative s g t)
  | succ n ih => exact (ih (r+1) s).add (ih r (s+1))

open SourceMovingJetFlux (eigenTest eigen_test_embed)

private theorem jet_zero_flow (f : QuantumTest) (t : ℝ) :
    strongJet 0 f t=hilbertFlow t (embed f) := by rw [strong_jet_zero,hilbertFlow_on_core]

private theorem conjugate_rank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    U.conjStarAlgEquiv (rankOne ℂ x y)=rankOne ℂ (U x) (U y) := by
  apply ContinuousLinearMap.ext
  intro z
  change U (inner ℂ y (U.symm z) • x)=inner ℂ (U y) z • U x
  rw [map_smul,←U.inner_map_map y (U.symm z),U.apply_symm_apply]

def projectionJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpectralIndex F,rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

def compressionOrbitJet (F : Index) (n : ℕ) (t : ℝ) : Op :=
  ∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
    rankJet n 0 0 (eigenTest F i) (eigenTest F i) t

/-- The static identity is the entire escape-space resolvent, retained before taking derivatives. -/
def resolventOrbitJet (F : Index) (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  (if n=0 then -z⁻¹ • (1 : Op) else 0)+
  ∑ i : SpectralIndex F,(((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
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
    projectionJet F 0 t=(hilbertFlow t).conjStarAlgEquiv (supportProjection F) := by
  classical
  rw [supportProjection,(sourceBasis F).starProjection_eq_sum_rankOne,map_sum]
  simp only [projectionJet,rankJet,jet_zero_flow,eigen_test_embed,conjugate_rank]

private theorem compression_spectral (F : Index) :
    GaussGradedCompression.compression F=
      ∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  simpa only [SourceMovingJetFlux.compressionOrbitJet,SourceMovingJetFlux.rankJet,
    SourceMovingJetFlux.frame_zero,mul_zero,SourceCoframeScaleTransport.hilbertFlow_zero,eigen_test_embed] using!
    (SourceMovingJetFlux.compression_orbit_zero F).symm

private theorem resolvent_spectral (F : Index) (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z= -z⁻¹ • (1 : Op)+
      ∑ i : SpectralIndex F,(((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  simpa only [SourceMovingJetFlux.resolventOrbitJet,SourceMovingJetFlux.rankJet,
    SourceMovingJetFlux.frame_zero,mul_zero,SourceCoframeScaleTransport.hilbertFlow_zero,eigen_test_embed,if_true] using!
    (SourceMovingJetFlux.resolvent_orbit_zero F z hz).symm

private theorem conjugate_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (U : E ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) (c : ι → ℂ) (v : ι → E)
    (hA : A=∑ i,c i • rankOne ℂ (v i) (v i)) :
    (∑ i,c i • rankOne ℂ (U (v i)) (U (v i)))=U.conjStarAlgEquiv A := by
  rw [hA,map_sum]
  simp only [map_smul,conjugate_rank]

private theorem conjugate_affine_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (U : E ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) (a : ℂ) (c : ι → ℂ) (v : ι → E)
    (hA : A=a • (1 : E →L[ℂ] E)+∑ i,c i • rankOne ℂ (v i) (v i)) :
    a • (1 : E →L[ℂ] E)+(∑ i,c i • rankOne ℂ (U (v i)) (U (v i)))=U.conjStarAlgEquiv A := by
  rw [hA,map_add,map_smul,map_one,map_sum]
  simp only [map_smul,conjugate_rank]

theorem actual_moving_compression (F : Index) (t : ℝ) :
    compressionOrbitJet F 0 t=(hilbertFlow t).conjStarAlgEquiv (GaussGradedCompression.compression F) := by
  simpa only [compressionOrbitJet,rankJet,jet_zero_flow,eigen_test_embed] using!
    conjugate_spectral (E := H) (hilbertFlow t) (GaussGradedCompression.compression F)
      (fun i : SpectralIndex F => (channelValue F (some i) : ℂ))
      (fun i => (sourceBasis F i : H)) (compression_spectral F)

theorem actual_moving_resolvent (F : Index) (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    resolventOrbitJet F z 0 t=(hilbertFlow t).conjStarAlgEquiv (finiteResolvent F z) := by
  simpa only [resolventOrbitJet,rankJet,jet_zero_flow,eigen_test_embed,if_true] using!
    conjugate_affine_spectral (E := H) (hilbertFlow t) (finiteResolvent F z) (-z⁻¹)
      (fun i : SpectralIndex F => (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹))
      (fun i => (sourceBasis F i : H)) (resolvent_spectral F z hz)

private theorem conjugate_zero (A : Op) : (hilbertFlow 0).conjStarAlgEquiv A=A := by
  apply ContinuousLinearMap.ext
  intro x
  change hilbertFlow 0 (A ((hilbertFlow 0).symm x))=A x
  have he : (hilbertFlow 0).symm x=x := by
    apply (hilbertFlow 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hilbertFlow_zero]
  rw [he,hilbertFlow_zero]

private theorem compression_zero (F : Index) : compressionOrbitJet F 0 0=GaussGradedCompression.compression F :=
  (actual_moving_compression F 0).trans (conjugate_zero _)

private theorem resolvent_zero (F : Index) (z : ℂ) (hz : z.im≠0) : resolventOrbitJet F z 0 0=finiteResolvent F z :=
  (actual_moving_resolvent F z hz 0).trans (conjugate_zero _)

/-- The complete first projection discrepancy is generated from the actual moving eigenframe. -/
def compressionCorrection (F : Index) : Op := compressionOrbitJet F 1 0-
  SourceJointScaleBudget.sourceCompression F
    (SourceScalarVirialBulk.deltaPhi GaussDiagonalHistory.diagonalAction)

theorem compression_correction_explicit (F : Index) :
    compressionCorrection F=
      (∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
        (rankOne ℂ (embed (generator (eigenTest F i))) (sourceBasis F i : H)+
          rankOne ℂ (sourceBasis F i : H) (embed (generator (eigenTest F i)))))-
      SourceJointScaleBudget.sourceCompression F
        (SourceScalarVirialBulk.deltaPhi GaussDiagonalHistory.diagonalAction) := by
  simp only [compressionCorrection,compressionOrbitJet,rankJet,strongJet,Nat.zero_add,pow_one,pow_zero,
    Module.End.one_apply,coreFlow_zero,eigen_test_embed]

private theorem map_inverse_product {R S : Type*} [Ring R] [Ring S]
    [Module ℂ R] [Module ℂ S] [Star R] [Star S]
    (e : R ≃⋆ₐ[ℂ] S) (A B : R) (z : ℂ) (h : (A-z • (1 : R))*B=1) :
    (e A-z • (1 : S))*e B=1 := by
  simpa only [map_mul,map_sub,map_smul,map_one] using congrArg e h

private theorem inverse_product (F : Index) (z : ℂ) (hz : z.im≠0) (t : ℝ) :
    (compressionOrbitJet F 0 t-z • (1 : Op))*resolventOrbitJet F z 0 t=1 := by
  have h := map_inverse_product (R := Op) (S := Op) (hilbertFlow t).conjStarAlgEquiv
    (GaussGradedCompression.compression F) (finiteResolvent F z) z
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  simpa only [actual_moving_compression,actual_moving_resolvent F z hz] using! h

private theorem solve_inverse_derivative {R : Type*} [Ring R] (r l a u : R)
    (hr : r*l=1) (hd : a*r+l*u=0) : u= -r*a*r := by
  have h := congrArg (fun x : R => r*x) hd
  rw [mul_add,←mul_assoc r l u,hr,one_mul,mul_zero] at h
  exact (eq_neg_of_add_eq_zero_right h).trans (by noncomm_ring)

private theorem inverse_curve_source_flux {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℝ → R) (a b l r d : R)
    (hA : HasDerivAt A a 0) (hB : HasDerivAt B b 0)
    (hA0 : A 0=l) (hB0 : B 0=r) (hr : r*l=1) (hp : ∀ t,A t*B t=1) :
    b= -r*d*r-r*(a-d)*r := by
  have hd := hA.mul hB
  have he : (fun t => A t*B t)=fun _ : ℝ => (1 : R) := funext hp
  change HasDerivAt (fun t => A t*B t) _ 0 at hd
  rw [he] at hd
  have hh := hd.unique (hasDerivAt_const (0 : ℝ) (1 : R))
  rw [hA0,hB0] at hh
  rw [solve_inverse_derivative r l a b hr hh]
  noncomm_ring

/-- True bounded resolvent derivative, with the source derivative and every moving-projection term retained. -/
theorem actual_resolvent_source_flux (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventOrbitJet F z 1 0=
      -(finiteResolvent F z)*SourceJointScaleBudget.sourceCompression F
        (SourceScalarVirialBulk.deltaPhi GaussDiagonalHistory.diagonalAction)*finiteResolvent F z-
      finiteResolvent F z*compressionCorrection F*finiteResolvent F z := by
  have hc : HasDerivAt (fun t : ℝ => compressionOrbitJet F 0 t-z • (1 : Op))
      (compressionOrbitJet F 1 0) 0 := by
    simpa only [Nat.zero_add] using! (moving_compression_derivative F 0 0).sub_const (z • (1 : Op))
  have h0 : compressionOrbitJet F 0 0-z • (1 : Op)=GaussGradedCompression.compression F-z • (1 : Op) :=
    congrArg (fun A : Op => A-z • (1 : Op)) (compression_zero F)
  have hr : finiteResolvent F z*(GaussGradedCompression.compression F-z • (1 : Op))=1 :=
    resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz
  simpa only [compressionCorrection] using! inverse_curve_source_flux (R := Op)
    (fun t => compressionOrbitJet F 0 t-z • (1 : Op)) (resolventOrbitJet F z 0)
    (compressionOrbitJet F 1 0) (resolventOrbitJet F z 1 0)
    (GaussGradedCompression.compression F-z • (1 : Op)) (finiteResolvent F z)
    (SourceJointScaleBudget.sourceCompression F (SourceScalarVirialBulk.deltaPhi diagonalAction))
    hc (moving_resolvent_derivative F z 0 0) h0 (resolvent_zero F z hz) hr (inverse_product F z hz)


end LowEnergy.ActualScalarCompressionJet
