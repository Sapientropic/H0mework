import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceGaugeScaleTransport
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceMovingJetFlux

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceGaugeCoframeJets
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolumeCurrent GaussDiagonalHistory GaussUnitaryHistory
open MeasureTheory Filter Set Function InnerProductSpace
open scoped ContDiff Topology InnerProductSpace ENNReal
private local instance scalarTestBoundedSMul : IsBoundedSMul ℂ ℂ := NormedSpace.toIsBoundedSMul
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
abbrev G := SourceGaugeScaleTransport.generator

def K : End := (3*Complex.I/2 : ℂ) • dilation

def coframeFlow (s : ℝ) : End := SourceCoframeScaleTransport.coreFlow ((3/2 : ℝ)*s)
def coframeHilbert (s : ℝ) : H ≃ₗᵢ[ℂ] H := SourceCoframeScaleTransport.hilbertFlow ((3/2 : ℝ)*s)

theorem core_flows_commute (s t : ℝ) (f : QuantumTest) :
    SourceGaugeScaleTransport.coreFlow t (coframeFlow s f)=
      coframeFlow s (SourceGaugeScaleTransport.coreFlow t f) := by
  ext z word
  simp only [coframeFlow,SourceGaugeScaleTransport.coreFlow_apply,SourceCoframeScaleTransport.coreFlow_apply,
    SourceGaugeRadialCurrent.gaugeScale,SourceCoframeVolume.scale]
  ring

theorem hilbert_flows_commute (s t : ℝ) (x : H) :
    SourceGaugeScaleTransport.hilbertFlow t (coframeHilbert s x)=
      coframeHilbert s (SourceGaugeScaleTransport.hilbertFlow t x) := by
  refine SourceCoframeScaleTransport.embed_dense.induction_on x
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro f
  simp only [coframeHilbert,SourceCoframeScaleTransport.hilbertFlow_on_core,
    SourceGaugeScaleTransport.hilbertFlow_on_core]
  exact congrArg embed (core_flows_commute s t f)

private theorem coframe_zero (f : QuantumTest) : coframeFlow 0 f=f := by
  rw [coframeFlow,mul_zero,SourceCoframeScaleTransport.coreFlow_zero]

private theorem coframe_jet_one (f : QuantumTest) (s : ℝ) :
    SourceMovingJetFlux.frameJet 1 f s=embed (coframeFlow s (K f)) := by
  simp only [SourceMovingJetFlux.frameJet,SourceCoframeStrongJet.strongJet,pow_one]
  change (3/2 : ℝ) • (Complex.I • embed (coframeFlow s (dilation f)))=
    embed (coframeFlow s ((3*Complex.I/2 : ℂ) • dilation f))
  rw [map_smul,map_smul,←smul_assoc]
  congr 1
  rw [Complex.real_smul]
  push_cast
  ring

private theorem coframe_derivative (f : QuantumTest) (s : ℝ) :
    HasDerivAt (fun r => embed (coframeFlow r f)) (embed (coframeFlow s (K f))) s := by
  have h := SourceMovingJetFlux.frame_jet_derivative 0 f s
  have h0 : SourceMovingJetFlux.frameJet 0 f=(fun r => embed (coframeFlow r f)) := by
    funext r
    simp only [SourceMovingJetFlux.frameJet,pow_zero,one_smul,SourceCoframeStrongJet.strong_jet_zero,coframeFlow]
  rw [h0,Nat.zero_add,coframe_jet_one] at h
  exact h

private theorem bounded_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] E) {f : ℝ → E} {v : E} {t : ℝ} (h : HasDerivAt f v t) :
    HasDerivAt (fun s => A (f s)) (A v) t :=
  (A.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem K_gauge_flow (t : ℝ) (f : QuantumTest) :
    K (SourceGaugeScaleTransport.coreFlow t f)=SourceGaugeScaleTransport.coreFlow t (K f) := by
  apply embed_injective
  have hl := coframe_derivative (SourceGaugeScaleTransport.coreFlow t f) 0
  have hr := bounded_derivative
    (SourceGaugeScaleTransport.hilbertFlow t).toContinuousLinearEquiv.toContinuousLinearMap
    (coframe_derivative f 0)
  have he : (fun s => embed (coframeFlow s (SourceGaugeScaleTransport.coreFlow t f)))=
      fun s => SourceGaugeScaleTransport.hilbertFlow t (embed (coframeFlow s f)) := by
    funext s
    rw [SourceGaugeScaleTransport.hilbertFlow_on_core,core_flows_commute]
  rw [he] at hl
  have h := hl.unique hr
  simp only [coframe_zero] at h
  change embed (K (SourceGaugeScaleTransport.coreFlow t f))=
    SourceGaugeScaleTransport.hilbertFlow t (embed (K f)) at h
  exact h.trans (SourceGaugeScaleTransport.hilbertFlow_on_core t (K f))

theorem G_coframe_flow (s : ℝ) (f : QuantumTest) : G (coframeFlow s f)=coframeFlow s (G f) := by
  apply embed_injective
  have hl := SourceGaugeScaleTransport.strong_core_derivative (coframeFlow s f) 0
  have hr := bounded_derivative (coframeHilbert s).toContinuousLinearEquiv.toContinuousLinearMap
    (SourceGaugeScaleTransport.strong_core_derivative f 0)
  have he : (fun t => embed (SourceGaugeScaleTransport.coreFlow t (coframeFlow s f)))=
      fun t => coframeHilbert s (embed (SourceGaugeScaleTransport.coreFlow t f)) := by
    funext t
    rw [core_flows_commute]
    exact (SourceCoframeScaleTransport.hilbertFlow_on_core _ _).symm
  rw [he] at hl
  have h := hl.unique hr
  simp only [SourceGaugeScaleTransport.coreFlow_zero] at h
  change embed (G (coframeFlow s f))=coframeHilbert s (embed (G f)) at h
  exact h.trans (SourceCoframeScaleTransport.hilbertFlow_on_core _ _)

private theorem K_pair (f g : QuantumTest) : sourcePair f (K g)= -sourcePair (K f) g := by
  have hc : star (3*Complex.I/2 : ℂ)= -(3*Complex.I/2 : ℂ) := by simp; ring
  have hd := SourceCoframeDilation.dilation_pair f g
  change sourcePair f ((3*Complex.I/2 : ℂ) • dilation g)=
    -sourcePair ((3*Complex.I/2 : ℂ) • dilation f) g
  simp only [sourcePair,map_smul,inner_smul_left,inner_smul_right,starRingEnd_apply] at hd ⊢
  rw [hc,hd]
  ring

theorem generators_commute : Commute G K := by
  apply LinearMap.ext
  intro g
  apply GaussCoreLabel.pair_separates
  intro f
  have h₁ := SourceGaugeScaleTransport.weak_flow_derivative f (K g) 0
  have h₂ := (SourceGaugeScaleTransport.weak_flow_derivative (K f) g 0).neg
  have he : (fun t => sourcePair f (SourceGaugeScaleTransport.coreFlow t (K g)))=
      fun t => -sourcePair (K f) (SourceGaugeScaleTransport.coreFlow t g) := by
    funext t
    rw [←K_gauge_flow,K_pair]
  rw [he] at h₁
  have h := h₁.unique h₂
  simp only [SourceGaugeScaleTransport.coreFlow_zero] at h
  change sourcePair f (G (K g))=sourcePair f (K (G g))
  exact h.trans (K_pair f (G g)).symm

theorem K_commutator (A : End) : K*A-A*K=SourceHamiltonianScaleJet.scaleDerivative A := by
  change ((3*Complex.I/2 : ℂ) • dilation)*A-A*((3*Complex.I/2 : ℂ) • dilation)=
    (3*Complex.I/2 : ℂ) • (dilation*A-A*dilation)
  rw [smul_mul_assoc,mul_smul_comm,smul_sub]

def mixedHilbert (s t : ℝ) : H ≃ₗᵢ[ℂ] H := (coframeHilbert s).trans (SourceGaugeScaleTransport.hilbertFlow t)

def sourceTest (a b : ℕ) (f : QuantumTest) : QuantumTest := (K^a) ((G^b) f)

def testJet (a b : ℕ) (f : QuantumTest) (s t : ℝ) : H :=
  SourceGaugeScaleTransport.hilbertFlow t (embed (coframeFlow s (sourceTest a b f)))

private theorem source_coframe (a b : ℕ) (f : QuantumTest) : K (sourceTest a b f)=sourceTest (a+1) b f := by
  rw [sourceTest,sourceTest,pow_succ']
  rfl

private theorem source_gauge (a b : ℕ) (f : QuantumTest) : G (sourceTest a b f)=sourceTest a (b+1) f := by
  have h := LinearMap.congr_fun (generators_commute.pow_right a).eq ((G^b) f)
  change G ((K^a) ((G^b) f))=(K^a) (G ((G^b) f)) at h
  simpa only [sourceTest,pow_succ',Module.End.mul_apply] using h

theorem test_coframe_derivative (a b : ℕ) (f : QuantumTest) (s t : ℝ) :
    HasDerivAt (fun r => testJet a b f r t) (testJet (a+1) b f s t) s := by
  have h := bounded_derivative
    (SourceGaugeScaleTransport.hilbertFlow t).toContinuousLinearEquiv.toContinuousLinearMap
    (coframe_derivative (sourceTest a b f) s)
  simpa only [testJet,source_coframe] using! h

theorem test_gauge_derivative (a b : ℕ) (f : QuantumTest) (s t : ℝ) :
    HasDerivAt (testJet a b f s) (testJet a (b+1) f s t) t := by
  have h := SourceGaugeScaleTransport.strong_core_derivative (coframeFlow s (sourceTest a b f)) t
  change HasDerivAt (fun u => SourceGaugeScaleTransport.hilbertFlow u
    (embed (coframeFlow s (sourceTest a b f))))
    (SourceGaugeScaleTransport.hilbertFlow t (embed (coframeFlow s (sourceTest a (b+1) f)))) t
  simp_rw [SourceGaugeScaleTransport.hilbertFlow_on_core]
  simpa only [G_coframe_flow,source_gauge] using! h

theorem test_jet_zero (f : QuantumTest) (s t : ℝ) : testJet 0 0 f s t=mixedHilbert s t (embed f) := by
  simp only [testJet,sourceTest,pow_zero,Module.End.one_apply,mixedHilbert,
    LinearIsometryEquiv.trans_apply,coframeHilbert,SourceCoframeScaleTransport.hilbertFlow_on_core,coframeFlow]

theorem test_jet_origin (a b : ℕ) (f : QuantumTest) : testJet a b f 0 0=embed (sourceTest a b f) := by
  rw [testJet,coframe_zero,SourceGaugeScaleTransport.hilbertFlow_zero]

theorem test_jet_norm (a b : ℕ) (f : QuantumTest) (s t : ℝ) :
    ‖testJet a b f s t‖=‖embed (sourceTest a b f)‖ := by
  rw [testJet,LinearIsometryEquiv.norm_map]
  exact SourceCoframeScaleTransport.coreFlow_norm _ _

private def coframeLeibniz {R : Type*} [AddCommGroup R] :
    ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R) → ℝ → ℝ → R
  | 0,r,u,v,w,L,s,t => L r u v w s t
  | n+1,r,u,v,w,L,s,t => coframeLeibniz n (r+1) u v w L s t+coframeLeibniz n r u (v+1) w L s t

private def mixedLeibniz {R : Type*} [AddCommGroup R] :
    ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → (ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R) → ℝ → ℝ → R
  | a,0,r,u,v,w,L,s,t => coframeLeibniz a r u v w L s t
  | a,b+1,r,u,v,w,L,s,t => mixedLeibniz a b r (u+1) v w L s t+mixedLeibniz a b r u v (w+1) L s t

private theorem coframe_leibniz_coframe {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R)
    (h : ∀ r u v w s t,HasDerivAt (fun x => L r u v w x t)
      (L (r+1) u v w s t+L r u (v+1) w s t) s)
    (a r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => coframeLeibniz a r u v w L x t)
      (coframeLeibniz (a+1) r u v w L s t) s := by
  induction a generalizing r u v w with
  | zero => exact h r u v w s t
  | succ a ih => exact (ih (r+1) u v w).add (ih r u (v+1) w)

private theorem coframe_leibniz_gauge {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R)
    (h : ∀ r u v w s t,HasDerivAt (L r u v w s)
      (L r (u+1) v w s t+L r u v (w+1) s t) t)
    (a r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (coframeLeibniz a r u v w L s)
      (coframeLeibniz a r (u+1) v w L s t+coframeLeibniz a r u v (w+1) L s t) t := by
  induction a generalizing r u v w with
  | zero => exact h r u v w s t
  | succ a ih =>
    apply ((ih (r+1) u v w).add (ih r u (v+1) w)).congr_deriv
    simp only [coframeLeibniz]
    abel

private theorem mixed_leibniz_coframe {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R)
    (h : ∀ r u v w s t,HasDerivAt (fun x => L r u v w x t)
      (L (r+1) u v w s t+L r u (v+1) w s t) s)
    (a b r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => mixedLeibniz a b r u v w L x t)
      (mixedLeibniz (a+1) b r u v w L s t) s := by
  induction b generalizing r u v w with
  | zero => exact coframe_leibniz_coframe L h a r u v w s t
  | succ b ih => exact (ih r (u+1) v w).add (ih r u v (w+1))

private theorem mixed_leibniz_gauge {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R)
    (h : ∀ r u v w s t,HasDerivAt (L r u v w s)
      (L r (u+1) v w s t+L r u v (w+1) s t) t)
    (a b r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (mixedLeibniz a b r u v w L s)
      (mixedLeibniz a (b+1) r u v w L s t) t := by
  induction b generalizing r u v w with
  | zero => exact coframe_leibniz_gauge L h a r u v w s t
  | succ b ih => exact (ih r (u+1) v w).add (ih r u v (w+1))

private theorem mixed_three_one {R : Type*} [Ring R]
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R) (s t : ℝ) :
    mixedLeibniz 3 1 0 0 0 0 L s t=
      L 3 1 0 0 s t+L 3 0 0 1 s t+
      3*L 2 1 1 0 s t+3*L 2 0 1 1 s t+
      3*L 1 1 2 0 s t+3*L 1 0 2 1 s t+
      L 0 1 3 0 s t+L 0 0 3 1 s t := by
  simp only [mixedLeibniz,coframeLeibniz,Nat.reduceAdd]
  noncomm_ring

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

private def rankLeaf (f g : QuantumTest) (r u v w : ℕ) (s t : ℝ) : Op :=
  rankOne ℂ (testJet r u f s t) (testJet v w g s t)

private theorem rank_leaf_coframe (f g : QuantumTest) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => rankLeaf f g r u v w x t)
      (rankLeaf f g (r+1) u v w s t+rankLeaf f g r u (v+1) w s t) s := by
  simpa only [rankLeaf] using! rank_derivative
    (test_coframe_derivative r u f s t) (test_coframe_derivative v w g s t)

private theorem rank_leaf_gauge (f g : QuantumTest) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (rankLeaf f g r u v w s)
      (rankLeaf f g r (u+1) v w s t+rankLeaf f g r u v (w+1) s t) t := by
  simpa only [rankLeaf] using! rank_derivative
    (test_gauge_derivative r u f s t) (test_gauge_derivative v w g s t)

def rankJet (a b : ℕ) (f g : QuantumTest) (s t : ℝ) : Op :=
  mixedLeibniz a b 0 0 0 0 (rankLeaf f g) s t

private theorem rank_coframe_derivative (a b : ℕ) (f g : QuantumTest) (s t : ℝ) :
    HasDerivAt (fun x => rankJet a b f g x t) (rankJet (a+1) b f g s t) s := by
  simpa only [rankJet] using! mixed_leibniz_coframe (R := Op) (rankLeaf f g)
    (rank_leaf_coframe f g) a b 0 0 0 0 s t

private theorem rank_gauge_derivative (a b : ℕ) (f g : QuantumTest) (s t : ℝ) :
    HasDerivAt (rankJet a b f g s) (rankJet a (b+1) f g s t) t := by
  simpa only [rankJet] using! mixed_leibniz_gauge (R := Op) (rankLeaf f g)
    (rank_leaf_gauge f g) a b 0 0 0 0 s t

open SourceJointResidualEnergy SourceActualResolventEnergy SourceRetardedIncrement
open SourceResolventBandLimit FullYSourceResolventGraphSplice
open SourceMovingJetFlux (eigenTest eigen_test_embed)

def projectionJet (F : Index) (a b : ℕ) (s t : ℝ) : Op :=
  ∑ i : SpectralIndex F,rankJet a b (eigenTest F i) (eigenTest F i) s t

def compressionJet (F : Index) (a b : ℕ) (s t : ℝ) : Op :=
  ∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
    rankJet a b (eigenTest F i) (eigenTest F i) s t

/-- The whole escape-space inverse stays in the zero jet. -/
def resolventJet (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) : Op :=
  (if a=0 ∧ b=0 then -z⁻¹ • (1 : Op) else 0)+
  ∑ i : SpectralIndex F,(((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
    rankJet a b (eigenTest F i) (eigenTest F i) s t

theorem compression_coframe_derivative (F : Index) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => compressionJet F a b x t) (compressionJet F (a+1) b s t) s := by
  unfold compressionJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (rank_coframe_derivative a b (eigenTest F i) (eigenTest F i) s t).const_smul (channelValue F (some i) : ℂ)) using 1
  funext x
  simp only [Finset.sum_apply,Pi.smul_apply]

theorem compression_gauge_derivative (F : Index) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (compressionJet F a b s) (compressionJet F a (b+1) s t) t := by
  unfold compressionJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    (rank_gauge_derivative a b (eigenTest F i) (eigenTest F i) s t).const_smul (channelValue F (some i) : ℂ)) using 1
  funext y
  simp only [Finset.sum_apply,Pi.smul_apply]

theorem resolvent_coframe_derivative (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => resolventJet F z a b x t) (resolventJet F z (a+1) b s t) s := by
  have h := (hasDerivAt_const s (if a=0 ∧ b=0 then -z⁻¹ • (1 : Op) else 0)).add
    (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (rank_coframe_derivative a b (eigenTest F i) (eigenTest F i) s t).const_smul
        (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹)))
  unfold resolventJet
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,false_and,if_false,zero_add]
  simp only [zero_add] at h
  convert! h using 1
  funext x
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply]

theorem resolvent_gauge_derivative (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (resolventJet F z a b s) (resolventJet F z a (b+1) s t) t := by
  have h := (hasDerivAt_const t (if a=0 ∧ b=0 then -z⁻¹ • (1 : Op) else 0)).add
    (HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (rank_gauge_derivative a b (eigenTest F i) (eigenTest F i) s t).const_smul
        (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹)))
  unfold resolventJet
  simp only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,zero_add]
  simp only [zero_add] at h
  convert! h using 1
  funext y
  simp only [Finset.sum_apply,Pi.smul_apply,Pi.add_apply]

private theorem conjugate_rank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    U.conjStarAlgEquiv (rankOne ℂ x y)=rankOne ℂ (U x) (U y) := by
  apply ContinuousLinearMap.ext
  intro z
  change U (inner ℂ y (U.symm z) • x)=inner ℂ (U y) z • U x
  rw [map_smul,←U.inner_map_map y (U.symm z),U.apply_symm_apply]

private theorem conjugate_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (U : E ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) (a : ℂ) (c : ι → ℂ) (v : ι → E)
    (hA : A=a • (1 : E →L[ℂ] E)+∑ i,c i • rankOne ℂ (v i) (v i)) :
    a • (1 : E →L[ℂ] E)+(∑ i,c i • rankOne ℂ (U (v i)) (U (v i)))=U.conjStarAlgEquiv A := by
  rw [hA,map_add,map_smul,map_one,map_sum]
  simp only [map_smul,conjugate_rank]

private theorem conjugate_linear_spectral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (U : E ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) (c : ι → ℂ) (v : ι → E)
    (hA : A=∑ i,c i • rankOne ℂ (v i) (v i)) :
    (∑ i,c i • rankOne ℂ (U (v i)) (U (v i)))=U.conjStarAlgEquiv A := by
  rw [hA,map_sum]
  simp only [map_smul,conjugate_rank]

private theorem compression_spectral (F : Index) :
    GaussGradedCompression.compression F=
      ∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  simpa only [SourceMovingJetFlux.compressionOrbitJet,SourceMovingJetFlux.rankJet,
    SourceMovingJetFlux.frame_zero,mul_zero,SourceCoframeScaleTransport.hilbertFlow_zero,
    eigen_test_embed] using! (SourceMovingJetFlux.compression_orbit_zero F).symm

private theorem resolvent_spectral (F : Index) (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z= -z⁻¹ • (1 : Op)+
      ∑ i : SpectralIndex F,(((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹) •
        rankOne ℂ (sourceBasis F i : H) (sourceBasis F i : H) := by
  simpa only [SourceMovingJetFlux.resolventOrbitJet,SourceMovingJetFlux.rankJet,
    SourceMovingJetFlux.frame_zero,mul_zero,SourceCoframeScaleTransport.hilbertFlow_zero,
    eigen_test_embed,if_true] using! (SourceMovingJetFlux.resolvent_orbit_zero F z hz).symm

theorem actual_mixed_projection (F : Index) (s t : ℝ) :
    projectionJet F 0 0 s t=(mixedHilbert s t).conjStarAlgEquiv (supportProjection F) := by
  classical
  rw [supportProjection,(sourceBasis F).starProjection_eq_sum_rankOne,map_sum]
  simp only [projectionJet,rankJet,mixedLeibniz,coframeLeibniz,rankLeaf,test_jet_zero,eigen_test_embed,conjugate_rank]

theorem actual_mixed_compression (F : Index) (s t : ℝ) :
    compressionJet F 0 0 s t=(mixedHilbert s t).conjStarAlgEquiv (GaussGradedCompression.compression F) := by
  simpa only [compressionJet,rankJet,mixedLeibniz,coframeLeibniz,rankLeaf,test_jet_zero,eigen_test_embed] using!
    conjugate_linear_spectral (E := H) (mixedHilbert s t) (GaussGradedCompression.compression F)
      (fun i : SpectralIndex F => (channelValue F (some i) : ℂ))
      (fun i => (sourceBasis F i : H)) (compression_spectral F)

theorem actual_mixed_resolvent (F : Index) (z : ℂ) (hz : z.im≠0) (s t : ℝ) :
    resolventJet F z 0 0 s t=(mixedHilbert s t).conjStarAlgEquiv (finiteResolvent F z) := by
  simpa only [resolventJet,rankJet,mixedLeibniz,coframeLeibniz,rankLeaf,test_jet_zero,eigen_test_embed,if_true,and_self] using!
    conjugate_spectral (E := H) (mixedHilbert s t) (finiteResolvent F z) (-z⁻¹)
      (fun i : SpectralIndex F => (((channelValue F (some i) : ℂ)-z)⁻¹+z⁻¹))
      (fun i => (sourceBasis F i : H)) (resolvent_spectral F z hz)

/-- Ordered original source derivatives, without replacing either by a compressed commutator. -/
def sourceJet (a b : ℕ) : End :=
  (SourceScalarGaugeScale.deltaGauge^b) ((SourceHamiltonianScaleJet.scaleDerivative^a) diagonalAction)

def compressionCorrection (F : Index) (a b : ℕ) : Op :=
  compressionJet F a b 0 0-SourceJointScaleBudget.sourceCompression F (sourceJet a b)

theorem source_compression_return (F : Index) (a b : ℕ) :
    compressionJet F a b 0 0=SourceJointScaleBudget.sourceCompression F (sourceJet a b)+compressionCorrection F a b := by
  unfold compressionCorrection
  abel

def rankSource (F : Index) (i : SpectralIndex F) (a b c d : ℕ) : Op :=
  rankOne ℂ (embed (sourceTest a b (eigenTest F i))) (embed (sourceTest c d (eigenTest F i)))

/-- All eight mixed rank terms are retained in the genuine (3,1) projection discrepancy. -/
theorem compression_correction_three_one (F : Index) :
    compressionCorrection F 3 1=
      (∑ i : SpectralIndex F,(channelValue F (some i) : ℂ) •
        (rankSource F i 3 1 0 0+rankSource F i 3 0 0 1+
          3*rankSource F i 2 1 1 0+3*rankSource F i 2 0 1 1+
          3*rankSource F i 1 1 2 0+3*rankSource F i 1 0 2 1+
          rankSource F i 0 1 3 0+rankSource F i 0 0 3 1))-
      SourceJointScaleBudget.sourceCompression F (sourceJet 3 1) := by
  simp only [compressionCorrection,compressionJet,rankJet,mixed_three_one,rankLeaf,test_jet_origin,rankSource]

/-- A finite, whole-frequency bound for every actual fixed mixed test, uniform in F and both scale parameters. -/
theorem fixed_mixed_jet_energy (F : Index) (μ : ℝ) (hμ : 0<μ) (a b : ℕ)
    (f : QuantumTest) (s t : ℝ) :
    (∫ w : ℝ, ‖finiteResolvent F (line μ w) (testJet a b f s t)‖^2)=
      (Real.pi/μ)*‖embed (sourceTest a b f)‖^2 := by
  simpa only [line,mul_comm (μ : ℂ) Complex.I,test_jet_norm] using!
    actual_square_integral F μ hμ (testJet a b f s t)

private def shiftedJet (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) : Op :=
  compressionJet F a b s t-(if a=0 ∧ b=0 then z • (1 : Op) else 0)

private theorem shifted_coframe_derivative (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => shiftedJet F z a b x t) (shiftedJet F z (a+1) b s t) s := by
  simpa only [shiftedJet,Nat.add_eq_zero_iff,one_ne_zero,and_false,false_and,if_false,sub_zero] using!
    (compression_coframe_derivative F a b s t).sub_const (if a=0 ∧ b=0 then z • (1 : Op) else 0)

private theorem shifted_gauge_derivative (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (shiftedJet F z a b s) (shiftedJet F z a (b+1) s t) t := by
  simpa only [shiftedJet,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false,sub_zero] using!
    (compression_gauge_derivative F a b s t).sub_const (if a=0 ∧ b=0 then z • (1 : Op) else 0)

private def productLeaf (F : Index) (z : ℂ) (r u v w : ℕ) (s t : ℝ) : Op :=
  shiftedJet F z r u s t*resolventJet F z v w s t

private theorem product_leaf_coframe (F : Index) (z : ℂ) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => productLeaf F z r u v w x t)
      (productLeaf F z (r+1) u v w s t+productLeaf F z r u (v+1) w s t) s := by
  simpa only [productLeaf] using! (shifted_coframe_derivative F z r u s t).mul
    (resolvent_coframe_derivative F z v w s t)

private theorem product_leaf_gauge (F : Index) (z : ℂ) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (productLeaf F z r u v w s)
      (productLeaf F z r (u+1) v w s t+productLeaf F z r u v (w+1) s t) t := by
  simpa only [productLeaf] using! (shifted_gauge_derivative F z r u s t).mul
    (resolvent_gauge_derivative F z v w s t)

/-- All two-sided Leibniz crosses of the actual bounded inverse product. -/
def inverseLeibniz (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) : Op :=
  mixedLeibniz a b 0 0 0 0 (productLeaf F z) s t

private theorem inverse_leibniz_coframe (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => inverseLeibniz F z a b x t) (inverseLeibniz F z (a+1) b s t) s := by
  simpa only [inverseLeibniz] using! mixed_leibniz_coframe (R := Op) (productLeaf F z)
    (product_leaf_coframe F z) a b 0 0 0 0 s t

private theorem inverse_leibniz_gauge (F : Index) (z : ℂ) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (inverseLeibniz F z a b s) (inverseLeibniz F z a (b+1) s t) t := by
  simpa only [inverseLeibniz] using! mixed_leibniz_gauge (R := Op) (productLeaf F z)
    (product_leaf_gauge F z) a b 0 0 0 0 s t

private theorem map_inverse_product {R S : Type*} [Ring R] [Ring S]
    [Module ℂ R] [Module ℂ S] [Star R] [Star S]
    (e : R ≃⋆ₐ[ℂ] S) (A B : R) (z : ℂ) (h : (A-z • (1 : R))*B=1) :
    (e A-z • (1 : S))*e B=1 := by
  simpa only [map_mul,map_sub,map_smul,map_one] using congrArg e h

private theorem inverse_product (F : Index) (z : ℂ) (hz : z.im≠0) (s t : ℝ) :
    inverseLeibniz F z 0 0 s t=1 := by
  have h := map_inverse_product (R := Op) (S := Op) (mixedHilbert s t).conjStarAlgEquiv
    (GaussGradedCompression.compression F) (finiteResolvent F z) z
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  simpa only [inverseLeibniz,mixedLeibniz,coframeLeibniz,productLeaf,shiftedJet,and_self,if_true,
    actual_mixed_compression,actual_mixed_resolvent F z hz] using! h

private theorem derivative_constant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) (c v : E) (t : ℝ) (h : HasDerivAt f v t) (he : ∀ s,f s=c) : v=0 := by
  have hc : HasDerivAt f 0 t := (hasDerivAt_const t c).congr_of_eventuallyEq (Filter.Eventually.of_forall he)
  exact h.unique hc

private theorem inverse_coframe_leibniz (F : Index) (z : ℂ) (hz : z.im≠0) (a : ℕ) (s t : ℝ) :
    inverseLeibniz F z a 0 s t=if a=0 then 1 else 0 := by
  induction a generalizing s with
  | zero =>
    rw [if_pos rfl]
    simpa only using! inverse_product F z hz s t
  | succ a ih =>
    have h := derivative_constant (E := Op) (fun x => inverseLeibniz F z a 0 x t)
      (if a=0 then (1 : Op) else 0) (inverseLeibniz F z (a+1) 0 s t) s
      (inverse_leibniz_coframe F z a 0 s t) ih
    simpa only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false] using! h

/-- Exact inverse jets, including all mixed cross terms, generated from the actual two-parameter inverse identity. -/
theorem actual_mixed_inverse_leibniz (F : Index) (z : ℂ) (hz : z.im≠0) (a b : ℕ) (s t : ℝ) :
    inverseLeibniz F z a b s t=if a=0 ∧ b=0 then 1 else 0 := by
  induction b generalizing t with
  | zero => simpa only [and_true] using! inverse_coframe_leibniz F z hz a s t
  | succ b ih =>
    have h := derivative_constant (E := Op) (inverseLeibniz F z a b s)
      (if a=0 ∧ b=0 then (1 : Op) else 0) (inverseLeibniz F z a (b+1) s t) t
      (inverse_leibniz_gauge F z a b s t) ih
    simpa only [Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false] using! h

private theorem origin_conjugate (A : Op) : (mixedHilbert 0 0).conjStarAlgEquiv A=A := by
  have hu (x : H) : mixedHilbert 0 0 x=x := by
    simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 (A ((mixedHilbert 0 0).symm x))=A x
  have he : (mixedHilbert 0 0).symm x=x := by
    apply (mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [he,hu]

private theorem compression_origin (F : Index) : compressionJet F 0 0 0 0=GaussGradedCompression.compression F :=
  (actual_mixed_compression F 0 0).trans (origin_conjugate _)

private theorem resolvent_origin (F : Index) (z : ℂ) (hz : z.im≠0) : resolventJet F z 0 0 0 0=finiteResolvent F z :=
  (actual_mixed_resolvent F z hz 0 0).trans (origin_conjugate _)

/-- Each vertex combines the exact ordered source derivative with its generated projection discrepancy. -/
def sourceVertex (F : Index) (a b : ℕ) : Op :=
  SourceJointScaleBudget.sourceCompression F (sourceJet a b)+compressionCorrection F a b

private theorem vertex_return (F : Index) (a b : ℕ) : compressionJet F a b 0 0=sourceVertex F a b :=
  source_compression_return F a b

private theorem solve_inverse_row {R : Type*} [Ring R] (r l q u : R)
    (hr : r*l=1) (hd : q+l*u=0) : u= -r*q := by
  have h := congrArg (fun x : R => r*x) hd
  rw [mul_add,←mul_assoc r l u,hr,one_mul,mul_zero] at h
  exact (eq_neg_of_add_eq_zero_right h).trans (neg_mul _ _).symm

/-- The requested (3,1) inverse response keeps all seven lower mixed crosses and every same-F source/projection vertex. -/
theorem actual_mixed_inverse_three_one (F : Index) (z : ℂ) (hz : z.im≠0) :
    resolventJet F z 3 1 0 0= -(finiteResolvent F z)*(
      sourceVertex F 3 1*finiteResolvent F z+
      sourceVertex F 3 0*resolventJet F z 0 1 0 0+
      3*sourceVertex F 2 1*resolventJet F z 1 0 0 0+
      3*sourceVertex F 2 0*resolventJet F z 1 1 0 0+
      3*sourceVertex F 1 1*resolventJet F z 2 0 0 0+
      3*sourceVertex F 1 0*resolventJet F z 2 1 0 0+
      sourceVertex F 0 1*resolventJet F z 3 0 0 0) := by
  have h := actual_mixed_inverse_leibniz F z hz 3 1 0 0
  norm_num only [inverseLeibniz,mixed_three_one,productLeaf,shiftedJet,and_self,and_true,
    false_and,and_false,if_false,if_true,sub_zero] at h
  rw [compression_origin,resolvent_origin F z hz] at h
  simp only [vertex_return] at h
  have hr : finiteResolvent F z*(GaussGradedCompression.compression F-z • (1 : Op))=1 :=
    resolvent_left _ (GaussGradedCompression.compression_selfAdjoint F) z hz
  have hh :
      (sourceVertex F 3 1*finiteResolvent F z+
      sourceVertex F 3 0*resolventJet F z 0 1 0 0+
      3*sourceVertex F 2 1*resolventJet F z 1 0 0 0+
      3*sourceVertex F 2 0*resolventJet F z 1 1 0 0+
      3*sourceVertex F 1 1*resolventJet F z 2 0 0 0+
      3*sourceVertex F 1 0*resolventJet F z 2 1 0 0+
      sourceVertex F 0 1*resolventJet F z 3 0 0 0)+
      (GaussGradedCompression.compression F-z • (1 : Op))*resolventJet F z 3 1 0 0=0 := by
    simpa only [mul_assoc] using! h
  exact solve_inverse_row _ _ _ _ hr hh

end LowEnergy.SourceGaugeCoframeJets
