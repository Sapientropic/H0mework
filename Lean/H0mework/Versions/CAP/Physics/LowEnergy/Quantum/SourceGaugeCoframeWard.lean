import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceGaugeCoframeJets
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarEndpointCost
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarGaugeEndpoint
import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceScalarCoframeInvariant

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceGaugeCoframeWard
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert
open GaussDiagonalHistory GaussUnitaryHistory GaussNativeEnergy GaussYukawaCoefficient
open SourceCoframeVolumeCurrent SourceMixedNativeReturn SourceScalarDoubleCurrent
open SourceScalarGaugeScale SourceHamiltonianScaleJet SourceJointScaleBudget
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open FullYSourceResolventGraphSplice SourceResolventBandLimit
open MeasureTheory Filter Set Function InnerProductSpace
open scoped ContDiff Topology InnerProductSpace ENNReal
abbrev End := SourceScalarGaugeScale.End
abbrev Op := H →L[ℂ] H

private def nativeRead (F : Index) (g : diagonal.domain) : End →ₗ[ℂ] Op where
  toFun A := sourceRead F g A
  map_add' A B := by
    apply ContinuousLinearMap.ext
    intro x
    exact map_add embed _ _
  map_smul' c A := by
    apply ContinuousLinearMap.ext
    intro x
    exact map_smul embed c _

def coreJet (a b : ℕ) (A : End) : End := (deltaGauge^b) ((scaleDerivative^a) A)

def select {V : Type*} [AddCommGroup V] [Module ℂ V] (A : ℕ → ℕ → V) : V :=
  A 3 1+(12 : ℂ) • A 2 1+(44 : ℂ) • A 1 1+(48 : ℂ) • A 0 1+
  A 3 0+(12 : ℂ) • A 2 0+(44 : ℂ) • A 1 0+(48 : ℂ) • A 0 0

def corePolynomial (A : End) : End := deltaGauge (cubic A)+cubic A

def sourceDouble (sharp : Bool) (m ell : ℕ) : End :=
  bracket diagonalAction (bracket diagonalAction (fullInsertion sharp m ell))

theorem source_polynomial_select (A : End) : select (fun a b => coreJet a b A)=corePolynomial A := by
  simp only [select,coreJet,pow_zero,pow_succ,Module.End.mul_apply,Module.End.one_apply,
    corePolynomial,cubic,LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,
    LinearMap.id_apply,map_add,map_smul]
  abel

private theorem linear_scaled_read {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (l : V →ₗ[ℂ] W) (A B : V) (c : ℂ) (h : A=c • B) :
    l A=c • l B := by rw [h,map_smul]

/-- The complete ordered source equation is read on the original finite input carrier. -/
theorem actual_source_polynomial_read (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    sourceRead F g (corePolynomial (sourceDouble sharp m ell))=
      (-96*(sourceTime 0 : ℂ)^2) •
        sourceRead F g (bracket SourceScalarRadialContact.scalarEulerAction (fullInsertion sharp m ell)) := by
  have h := congrArg (nativeRead F g) (original_gauge_coframe_return sharp m ell)
  rw [map_smul] at h
  -- Only the opaque proof-instance caches differ; the full term is checked by the kernel.
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
    Lean.Elab.Tactic.replaceMainGoal []

private theorem gauge_remainder (sharp : Bool) (m ell : ℕ) :
    scaleGaugeRemainder sharp m ell=corePolynomial (sourceDouble sharp m ell)-(48 : ℂ) • sourceDouble sharp m ell := by
  simp only [scaleGaugeRemainder,corePolynomial,sourceDouble,cubic,scaleDoubleRemainder,
    LinearMap.add_apply,LinearMap.comp_apply,LinearMap.smul_apply,LinearMap.id_apply]
  abel

private theorem read_force_algebra {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (l : V →ₗ[ℂ] W) (a : ℂ) (C T P J : V) (D S : W) :
    l (-a • C+a • T-(1/48 : ℂ) • (P-(48 : ℂ) • J))-(l J-D)-S=
      D-(1/48 : ℂ) • l P-a • l C+a • l T-S := by
  simp only [map_sub,map_add,map_smul]
  module

private theorem force_read_return {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (l : V →ₗ[ℂ] W) (a : ℂ) (C T P J F : V) (B D S Phi : W)
    (hB : B=l F-Phi-S) (hF : F= -a • C+a • T-(1/48 : ℂ) • (P-(48 : ℂ) • J))
    (hPhi : Phi=l J-D) : B=D-(1/48 : ℂ) • l P-a • l C+a • l T-S := by
  rw [hB,hF,hPhi]
  exact read_force_algebra l a C T P J D S

/-- GaugeScale10 enters the actual balanced force with all three defects and the full Hardy subtraction. -/
theorem actual_balanced_polynomial_return (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    SourceScalarForceBudget.balancedForce sharp m ell F g=
      SourceScalarForceBudget.doubleResponse sharp m ell F g-
      (1/48 : ℂ) • sourceRead F g (corePolynomial (sourceDouble sharp m ell))-
      (2*(sourceTime 0 : ℂ)^2) • sourceRead F g (fullAction sharp*cutoffEuler m ell)+
      (2*(sourceTime 0 : ℂ)^2) • sourceRead F g (constantAction sharp vacuum*thetaAction m ell)-
      (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F := by
  have hr : gaugeScaleForce sharp m ell=
      -(2*(sourceTime 0 : ℂ)^2) • (fullAction sharp*cutoffEuler m ell)+
      (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-
      (1/48 : ℂ) • (corePolynomial (sourceDouble sharp m ell)-(48 : ℂ) • sourceDouble sharp m ell) :=
    congrArg (fun R : End => -(2*(sourceTime 0 : ℂ)^2) • (fullAction sharp*cutoffEuler m ell)+
      (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*thetaAction m ell)-(1/48 : ℂ) • R)
      (gauge_remainder sharp m ell)
  have hp : doubleProjectionFlux sharp m ell F g=
      nativeRead F g (sourceDouble sharp m ell)-SourceScalarForceBudget.doubleResponse sharp m ell F g := by
    have h := actual_double_projection_flux sharp m ell F g
    run_tac Lean.Elab.Tactic.withMainContext do
      (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
      Lean.Elab.Tactic.replaceMainGoal []
  have hb : SourceScalarForceBudget.balancedForce sharp m ell F g=
      nativeRead F g (gaugeScaleForce sharp m ell)-doubleProjectionFlux sharp m ell F g-
      (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F := by
    have h := actual_balanced_gauge_return sharp m ell F g
    run_tac Lean.Elab.Tactic.withMainContext do
      (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
      Lean.Elab.Tactic.replaceMainGoal []
  exact force_read_return (V := End) (W := Op) (nativeRead F g)
      (2*(sourceTime 0 : ℂ)^2) (fullAction sharp*cutoffEuler m ell)
      (constantAction sharp vacuum*thetaAction m ell) (corePolynomial (sourceDouble sharp m ell))
      (sourceDouble sharp m ell) (gaugeScaleForce sharp m ell)
      (SourceScalarForceBudget.balancedForce sharp m ell F g)
      (SourceScalarForceBudget.doubleResponse sharp m ell F g)
      ((SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F)
      (doubleProjectionFlux sharp m ell F g) hb hr hp

abbrev InputIndex (F : Index) (g : diagonal.domain) := Fin (Module.finrank ℂ (inputSpan F g))

def inputBasis (F : Index) (g : diagonal.domain) : OrthonormalBasis (InputIndex F g) ℂ (inputSpan F g) :=
  stdOrthonormalBasis ℂ (inputSpan F g)

def inputTest (F : Index) (g : diagonal.domain) (i : InputIndex F g) : QuantumTest :=
  coreEquiv.symm (Submodule.inclusion (input_span_core F g) (inputBasis F g i))

theorem input_test_embed (F : Index) (g : diagonal.domain) (i : InputIndex F g) :
    embed (inputTest F g i)=(inputBasis F g i : H) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

private theorem input_coefficient (F : Index) (g : diagonal.domain) (i : InputIndex F g) (x : H) :
    (inputBasis F g).repr ((inputSpan F g).orthogonalProjectionOnto x) i=
      inner ℂ (inputBasis F g i : H) x := by
  rw [OrthonormalBasis.repr_apply_apply]
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left (inputBasis F g i) x

/-- The literal sourceRead is generated on its original input span, including the original escape vector. -/
theorem source_read_rank (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g A=∑ i : InputIndex F g,
      rankOne ℂ (embed (A (inputTest F g i))) (embed (inputTest F g i)) := by
  classical
  apply ContinuousLinearMap.ext
  intro x
  let l : inputSpan F g →ₗ[ℂ] H := embed.comp (A.comp
    (coreEquiv.symm.toLinearMap.comp (Submodule.inclusion (input_span_core F g))))
  have h := congrArg l ((inputBasis F g).sum_repr ((inputSpan F g).orthogonalProjectionOnto x))
  simp only [map_sum,map_smul] at h
  change (∑ i : InputIndex F g,(inputBasis F g).repr ((inputSpan F g).orthogonalProjectionOnto x) i •
    embed (A (inputTest F g i)))=sourceRead F g A x at h
  trans ∑ i : InputIndex F g,(inputBasis F g).repr ((inputSpan F g).orthogonalProjectionOnto x) i •
    embed (A (inputTest F g i))
  · exact h.symm
  simp only [input_coefficient,sum_apply,rankOne_apply,input_test_embed]

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
  rankOne ℂ (SourceGaugeCoframeJets.testJet r u f s t) (SourceGaugeCoframeJets.testJet v w g s t)

private theorem rank_leaf_coframe (f g : QuantumTest) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => rankLeaf f g r u v w x t)
      (rankLeaf f g (r+1) u v w s t+rankLeaf f g r u (v+1) w s t) s := by
  simpa only [rankLeaf] using! rank_derivative
    (SourceGaugeCoframeJets.test_coframe_derivative r u f s t) (SourceGaugeCoframeJets.test_coframe_derivative v w g s t)

private theorem rank_leaf_gauge (f g : QuantumTest) (r u v w : ℕ) (s t : ℝ) :
    HasDerivAt (rankLeaf f g r u v w s)
      (rankLeaf f g r (u+1) v w s t+rankLeaf f g r u v (w+1) s t) t := by
  simpa only [rankLeaf] using! rank_derivative
    (SourceGaugeCoframeJets.test_gauge_derivative r u f s t) (SourceGaugeCoframeJets.test_gauge_derivative v w g s t)

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


def readOrbitJet (F : Index) (g : diagonal.domain) (A : End) (a b : ℕ) (s t : ℝ) : Op :=
  ∑ i : InputIndex F g,rankJet a b (A (inputTest F g i)) (inputTest F g i) s t

theorem read_orbit_coframe_derivative (F : Index) (g : diagonal.domain) (A : End)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => readOrbitJet F g A a b x t) (readOrbitJet F g A (a+1) b s t) s := by
  unfold readOrbitJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    rank_coframe_derivative a b (A (inputTest F g i)) (inputTest F g i) s t) using 1
  funext x
  simp only [Finset.sum_apply]

theorem read_orbit_gauge_derivative (F : Index) (g : diagonal.domain) (A : End)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (readOrbitJet F g A a b s) (readOrbitJet F g A a (b+1) s t) t := by
  unfold readOrbitJet
  convert! HasDerivAt.sum (u := Finset.univ) (fun i _ =>
    rank_gauge_derivative a b (A (inputTest F g i)) (inputTest F g i) s t) using 1
  funext y
  simp only [Finset.sum_apply]

private theorem conjugate_rank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (x y : E) :
    U.conjStarAlgEquiv (rankOne ℂ x y)=rankOne ℂ (U x) (U y) := by
  apply ContinuousLinearMap.ext
  intro z
  change U (inner ℂ y (U.symm z) • x)=inner ℂ (U y) z • U x
  rw [map_smul,←U.inner_map_map y (U.symm z),U.apply_symm_apply]

private theorem conjugate_kernel {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] {ι : Type*} [Fintype ι] (U : E ≃ₗᵢ[ℂ] E)
    (A : E →L[ℂ] E) (v w : ι → E) (hA : A=∑ i,rankOne ℂ (v i) (w i)) :
    (∑ i,rankOne ℂ (U (v i)) (U (w i)))=U.conjStarAlgEquiv A := by
  rw [hA,map_sum]
  simp only [conjugate_rank]

/-- The actual input-span source read has a genuine mixed norm-smooth finite-rank orbit. -/
theorem actual_read_orbit (F : Index) (g : diagonal.domain) (A : End) (s t : ℝ) :
    readOrbitJet F g A 0 0 s t=(SourceGaugeCoframeJets.mixedHilbert s t).conjStarAlgEquiv (sourceRead F g A) := by
  simpa only [readOrbitJet,rankJet,mixedLeibniz,coframeLeibniz,rankLeaf,
    SourceGaugeCoframeJets.test_jet_zero] using!
    conjugate_kernel (E := H) (SourceGaugeCoframeJets.mixedHilbert s t) (sourceRead F g A)
      (fun i => embed (A (inputTest F g i))) (fun i => embed (inputTest F g i)) (source_read_rank F g A)

private theorem read_orbit_origin (F : Index) (g : diagonal.domain) (A : End) :
    readOrbitJet F g A 0 0 0 0=sourceRead F g A := by
  simpa only [readOrbitJet,rankJet,mixedLeibniz,coframeLeibniz,rankLeaf,
    SourceGaugeCoframeJets.test_jet_origin,SourceGaugeCoframeJets.sourceTest,pow_zero,Module.End.one_apply] using!
    (source_read_rank F g A).symm

/-- The discrepancy is generated from the literal read's moving input projection and actual Core derivatives. -/
def inputFlux (F : Index) (g : diagonal.domain) (A : End) (a b : ℕ) : Op :=
  readOrbitJet F g A a b 0 0-sourceRead F g (coreJet a b A)

private def readRank (F : Index) (g : diagonal.domain) (A : End) (i : InputIndex F g)
    (r u v w : ℕ) : Op :=
  rankOne ℂ (embed (SourceGaugeCoframeJets.sourceTest r u (A (inputTest F g i))))
    (embed (SourceGaugeCoframeJets.sourceTest v w (inputTest F g i)))

/-- The full (3,1) input-projection discrepancy is an explicit eight-term source rank sum. -/
theorem input_flux_three_one (F : Index) (g : diagonal.domain) (A : End) :
    inputFlux F g A 3 1=
      (∑ i : InputIndex F g,
        (readRank F g A i 3 1 0 0+readRank F g A i 3 0 0 1+
        3*readRank F g A i 2 1 1 0+3*readRank F g A i 2 0 1 1+
        3*readRank F g A i 1 1 2 0+3*readRank F g A i 1 0 2 1+
        readRank F g A i 0 1 3 0+readRank F g A i 0 0 3 1))-sourceRead F g (coreJet 3 1 A) := by
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset (InputIndex F g))) rfl
    (fun i _ => mixed_three_one (R := Op) (rankLeaf (A (inputTest F g i)) (inputTest F g i)) 0 0)
  have h := congrArg (fun T : Op => T-sourceRead F g (coreJet 3 1 A)) hs
  simp only [rankLeaf,SourceGaugeCoframeJets.test_jet_origin] at h
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
    Lean.Elab.Tactic.replaceMainGoal []

private theorem select_linear {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (l : V →ₗ[ℂ] W) (A : ℕ → ℕ → V) :
    select (fun a b => l (A a b))=l (select A) := by
  simp only [select,map_add,map_smul]

private theorem select_sub {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : ℕ → ℕ → V) : select (fun a b => A a b-B a b)=select A-select B := by
  simp only [select,smul_sub]
  abel

private theorem read_select_residual {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (l : V →ₗ[ℂ] W) (J : ℕ → ℕ → W)
    (S : ℕ → ℕ → V) (P : V) (hP : select S=P) :
    l P=select J-select (fun a b => J a b-l (S a b)) := by
  rw [select_sub,select_linear,hP]
  abel

/-- The ordered source polynomial and its whole input-projection correction share the same actual read orbit. -/
theorem source_read_orbit_polynomial (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g (corePolynomial A)=
      select (fun a b => readOrbitJet F g A a b 0 0)-select (inputFlux F g A) := by
  have h := read_select_residual (nativeRead F g) (fun a b => readOrbitJet F g A a b 0 0)
    (fun a b => coreJet a b A) (corePolynomial A) (source_polynomial_select A)
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
    Lean.Elab.Tactic.replaceMainGoal []

private def productLeaf {R : Type*} [Mul R] (A B : ℕ → ℕ → ℝ → ℝ → R)
    (r u v w : ℕ) (s t : ℝ) : R := A r u s t*B v w s t

private def productJet {R : Type*} [Ring R] (A B : ℕ → ℕ → ℝ → ℝ → R)
    (a b : ℕ) (s t : ℝ) : R := mixedLeibniz a b 0 0 0 0 (productLeaf A B) s t

private theorem product_coframe {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℕ → ℕ → ℝ → ℝ → R)
    (hA : ∀ a b s t,HasDerivAt (fun x => A a b x t) (A (a+1) b s t) s)
    (hB : ∀ a b s t,HasDerivAt (fun x => B a b x t) (B (a+1) b s t) s)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => productJet A B a b x t) (productJet A B (a+1) b s t) s := by
  exact mixed_leibniz_coframe (productLeaf A B)
    (fun r u v w s t => (hA r u s t).mul (hB v w s t)) a b 0 0 0 0 s t

private theorem product_gauge {R : Type*} [NormedRing R] [NormedAlgebra ℝ R]
    (A B : ℕ → ℕ → ℝ → ℝ → R)
    (hA : ∀ a b s t,HasDerivAt (A a b s) (A a (b+1) s t) t)
    (hB : ∀ a b s t,HasDerivAt (B a b s) (B a (b+1) s t) t)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (productJet A B a b s) (productJet A B a (b+1) s t) t := by
  exact mixed_leibniz_gauge (productLeaf A B)
    (fun r u v w s t => (hA r u s t).mul (hB v w s t)) a b 0 0 0 0 s t

private def constantJet (A : Op) (a b : ℕ) (_s _t : ℝ) : Op :=
  if a=0 ∧ b=0 then A else 0

private theorem constant_coframe (A : Op) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => constantJet A a b x t) (constantJet A (a+1) b s t) s := by
  simpa only [constantJet,Nat.add_eq_zero_iff,one_ne_zero,and_false,false_and,if_false]
    using! hasDerivAt_const s (if a=0 ∧ b=0 then A else 0)

private theorem constant_gauge (A : Op) (a b : ℕ) (s t : ℝ) :
    HasDerivAt (constantJet A a b s) (constantJet A a (b+1) s t) t := by
  simpa only [constantJet,Nat.add_eq_zero_iff,one_ne_zero,and_false,if_false]
    using! hasDerivAt_const t (if a=0 ∧ b=0 then A else 0)

private def commutatorJet (A B : ℕ → ℕ → ℝ → ℝ → Op) (a b : ℕ) (s t : ℝ) : Op :=
  productJet A B a b s t-productJet B A a b s t

private theorem commutator_coframe (A B : ℕ → ℕ → ℝ → ℝ → Op)
    (hA : ∀ a b s t,HasDerivAt (fun x => A a b x t) (A (a+1) b s t) s)
    (hB : ∀ a b s t,HasDerivAt (fun x => B a b x t) (B (a+1) b s t) s)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => commutatorJet A B a b x t) (commutatorJet A B (a+1) b s t) s :=
  (product_coframe A B hA hB a b s t).sub (product_coframe B A hB hA a b s t)

private theorem commutator_gauge (A B : ℕ → ℕ → ℝ → ℝ → Op)
    (hA : ∀ a b s t,HasDerivAt (A a b s) (A a (b+1) s t) t)
    (hB : ∀ a b s t,HasDerivAt (B a b s) (B a (b+1) s t) t)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (commutatorJet A B a b s) (commutatorJet A B a (b+1) s t) t :=
  (product_gauge A B hA hB a b s t).sub (product_gauge B A hB hA a b s t)

private def surroundJet (F : Index) (z : ℂ) (A : ℕ → ℕ → ℝ → ℝ → Op) :=
  productJet (SourceGaugeCoframeJets.resolventJet F z)
    (productJet A (SourceGaugeCoframeJets.resolventJet F z))

private theorem surround_coframe (F : Index) (z : ℂ) (A : ℕ → ℕ → ℝ → ℝ → Op)
    (hA : ∀ a b s t,HasDerivAt (fun x => A a b x t) (A (a+1) b s t) s)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => surroundJet F z A a b x t) (surroundJet F z A (a+1) b s t) s :=
  product_coframe _ _ (SourceGaugeCoframeJets.resolvent_coframe_derivative F z)
    (product_coframe _ _ hA (SourceGaugeCoframeJets.resolvent_coframe_derivative F z)) a b s t

private theorem surround_gauge (F : Index) (z : ℂ) (A : ℕ → ℕ → ℝ → ℝ → Op)
    (hA : ∀ a b s t,HasDerivAt (A a b s) (A a (b+1) s t) t)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (surroundJet F z A a b s) (surroundJet F z A a (b+1) s t) t :=
  product_gauge _ _ (SourceGaugeCoframeJets.resolvent_gauge_derivative F z)
    (product_gauge _ _ hA (SourceGaugeCoframeJets.resolvent_gauge_derivative F z)) a b s t

/-- The actual two-sided finite resolvent orbit, with every mixed Leibniz cross. -/
def sandwichJet (F : Index) (g : diagonal.domain) (z : ℂ) (A : End) :=
  surroundJet F z (readOrbitJet F g A)

theorem sandwich_coframe_derivative (F : Index) (g : diagonal.domain) (z : ℂ) (A : End)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => sandwichJet F g z A a b x t) (sandwichJet F g z A (a+1) b s t) s :=
  surround_coframe F z _ (read_orbit_coframe_derivative F g A) a b s t

theorem sandwich_gauge_derivative (F : Index) (g : diagonal.domain) (z : ℂ) (A : End)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (sandwichJet F g z A a b s) (sandwichJet F g z A a (b+1) s t) t :=
  surround_gauge F z _ (read_orbit_gauge_derivative F g A) a b s t

/-- The main actor shared with the fixed-source endpoint budget. -/
def doubleOrbitJet (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) :=
  surroundJet F z (commutatorJet (SourceGaugeCoframeJets.compressionJet F)
    (commutatorJet (SourceGaugeCoframeJets.compressionJet F)
      (constantJet (SourceEscapeSeedTail.actualIncrement sharp m ell))))

theorem double_orbit_coframe_derivative (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (fun x => doubleOrbitJet sharp m ell F z a b x t)
      (doubleOrbitJet sharp m ell F z (a+1) b s t) s :=
  surround_coframe F z _ (commutator_coframe _ _
    (SourceGaugeCoframeJets.compression_coframe_derivative F)
    (commutator_coframe _ _ (SourceGaugeCoframeJets.compression_coframe_derivative F)
      (constant_coframe _))) a b s t

theorem double_orbit_gauge_derivative (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (a b : ℕ) (s t : ℝ) :
    HasDerivAt (doubleOrbitJet sharp m ell F z a b s)
      (doubleOrbitJet sharp m ell F z a (b+1) s t) t :=
  surround_gauge F z _ (commutator_gauge _ _
    (SourceGaugeCoframeJets.compression_gauge_derivative F)
    (commutator_gauge _ _ (SourceGaugeCoframeJets.compression_gauge_derivative F)
      (constant_gauge _))) a b s t

theorem double_orbit_base (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ) (s t : ℝ) :
    doubleOrbitJet sharp m ell F z 0 0 s t=
      SourceGaugeCoframeJets.resolventJet F z 0 0 s t*
      (SourceGaugeCoframeJets.compressionJet F 0 0 s t*
        (SourceGaugeCoframeJets.compressionJet F 0 0 s t*SourceEscapeSeedTail.actualIncrement sharp m ell-
         SourceEscapeSeedTail.actualIncrement sharp m ell*SourceGaugeCoframeJets.compressionJet F 0 0 s t)-
       (SourceGaugeCoframeJets.compressionJet F 0 0 s t*SourceEscapeSeedTail.actualIncrement sharp m ell-
         SourceEscapeSeedTail.actualIncrement sharp m ell*SourceGaugeCoframeJets.compressionJet F 0 0 s t)*
        SourceGaugeCoframeJets.compressionJet F 0 0 s t)*SourceGaugeCoframeJets.resolventJet F z 0 0 s t := by
  simp only [doubleOrbitJet,surroundJet,commutatorJet,productJet,mixedLeibniz,coframeLeibniz,
    productLeaf,constantJet,and_self,if_true,mul_assoc]

private theorem origin_conjugate (A : Op) :
    (SourceGaugeCoframeJets.mixedHilbert 0 0).conjStarAlgEquiv A=A := by
  have hu (x : H) : SourceGaugeCoframeJets.mixedHilbert 0 0 x=x := by
    simp only [SourceGaugeCoframeJets.mixedHilbert,LinearIsometryEquiv.trans_apply,
      SourceGaugeCoframeJets.coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change SourceGaugeCoframeJets.mixedHilbert 0 0
    (A ((SourceGaugeCoframeJets.mixedHilbert 0 0).symm x))=A x
  have he : (SourceGaugeCoframeJets.mixedHilbert 0 0).symm x=x := by
    apply (SourceGaugeCoframeJets.mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [he,hu]

private theorem resolvent_origin (F : Index) (z : ℂ) (hz : z.im≠0) :
    SourceGaugeCoframeJets.resolventJet F z 0 0 0 0=finiteResolvent F z :=
  (SourceGaugeCoframeJets.actual_mixed_resolvent F z hz 0 0).trans (origin_conjugate _)

private theorem compression_origin (F : Index) :
    SourceGaugeCoframeJets.compressionJet F 0 0 0 0=GaussGradedCompression.compression F :=
  (SourceGaugeCoframeJets.actual_mixed_compression F 0 0).trans (origin_conjugate _)

/-- The (3,1) inverse cell is actually replaced by the seven source/projection crosses. -/
def resolvedInverse (F : Index) (z : ℂ) (a b : ℕ) : Op :=
  if a=3 ∧ b=1 then -(finiteResolvent F z)*(
    SourceGaugeCoframeJets.sourceVertex F 3 1*finiteResolvent F z+
    SourceGaugeCoframeJets.sourceVertex F 3 0*SourceGaugeCoframeJets.resolventJet F z 0 1 0 0+
    3*SourceGaugeCoframeJets.sourceVertex F 2 1*SourceGaugeCoframeJets.resolventJet F z 1 0 0 0+
    3*SourceGaugeCoframeJets.sourceVertex F 2 0*SourceGaugeCoframeJets.resolventJet F z 1 1 0 0+
    3*SourceGaugeCoframeJets.sourceVertex F 1 1*SourceGaugeCoframeJets.resolventJet F z 2 0 0 0+
    3*SourceGaugeCoframeJets.sourceVertex F 1 0*SourceGaugeCoframeJets.resolventJet F z 2 1 0 0+
    SourceGaugeCoframeJets.sourceVertex F 0 1*SourceGaugeCoframeJets.resolventJet F z 3 0 0 0)
  else SourceGaugeCoframeJets.resolventJet F z a b 0 0

theorem resolved_inverse_return (F : Index) (z : ℂ) (hz : z.im≠0) (a b : ℕ) :
    resolvedInverse F z a b=SourceGaugeCoframeJets.resolventJet F z a b 0 0 := by
  unfold resolvedInverse
  split_ifs with h
  · rcases h with ⟨rfl,rfl⟩
    exact (SourceGaugeCoframeJets.actual_mixed_inverse_three_one F z hz).symm
  · rfl

private theorem coframe_origin {R : Type*} [AddCommGroup R]
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R) (a r u v w : ℕ) (s t : ℝ) :
    coframeLeibniz a r u v w (fun i j k l _ _ => L i j k l 0 0) s t=
      coframeLeibniz a r u v w L 0 0 := by
  induction a generalizing r u v w with
  | zero => rfl
  | succ a ih => simp only [coframeLeibniz,ih]

private theorem mixed_origin {R : Type*} [AddCommGroup R]
    (L : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R) (a b r u v w : ℕ) (s t : ℝ) :
    mixedLeibniz a b r u v w (fun i j k l _ _ => L i j k l 0 0) s t=
      mixedLeibniz a b r u v w L 0 0 := by
  induction b generalizing r u v w with
  | zero => exact coframe_origin L a r u v w s t
  | succ b ih => simp only [mixedLeibniz,ih]

private theorem product_origin {R : Type*} [Ring R] (A B : ℕ → ℕ → ℝ → ℝ → R) (a b : ℕ) (s t : ℝ) :
    productJet (fun i j _ _ => A i j 0 0) (fun i j _ _ => B i j 0 0) a b s t=
      productJet A B a b 0 0 := mixed_origin (productLeaf A B) a b 0 0 0 0 s t

/-- Every mixed inverse Leibniz term, including the whole-carrier inverse, is retained. -/
def inverseCross (F : Index) (g : diagonal.domain) (z : ℂ) (A : End) (a b : ℕ) : Op :=
  productJet (fun i j _ _ => resolvedInverse F z i j)
    (productJet (fun i j _ _ => readOrbitJet F g A i j 0 0)
      (fun i j _ _ => resolvedInverse F z i j)) a b 0 0-
  finiteResolvent F z*readOrbitJet F g A a b 0 0*finiteResolvent F z

private theorem resolved_surround {R : Type*} [Ring R]
    (J A : ℕ → ℕ → ℝ → ℝ → R) (Q : ℕ → ℕ → R)
    (hQ : ∀ a b,Q a b=J a b 0 0) (a b : ℕ) :
    productJet (fun i j _ _ => Q i j)
      (productJet (fun i j _ _ => A i j 0 0) (fun i j _ _ => Q i j)) a b 0 0=
      productJet J (productJet A J) a b 0 0 := by
  have hR : (fun i j (_s _t : ℝ) => Q i j)=(fun i j (_s _t : ℝ) => J i j 0 0) :=
    funext (fun i => funext (fun j => funext (fun _ => funext (fun _ => hQ i j))))
  rw [hR]
  have hP : productJet (fun i j (_s _t : ℝ) => A i j 0 0)
      (fun i j (_s _t : ℝ) => J i j 0 0)=
      fun i j (_s _t : ℝ) => productJet A J i j 0 0 := by
    funext i j s t
    exact product_origin A J i j s t
  rw [hP,product_origin]

private theorem cross_return (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A : End) (a b : ℕ) :
    inverseCross F g z A a b=sandwichJet F g z A a b 0 0-
      finiteResolvent F z*readOrbitJet F g A a b 0 0*finiteResolvent F z := by
  have h := congrArg (fun x : Op => x-finiteResolvent F z*readOrbitJet F g A a b 0 0*finiteResolvent F z)
    (resolved_surround (R := Op) (SourceGaugeCoframeJets.resolventJet F z) (readOrbitJet F g A)
      (resolvedInverse F z) (resolved_inverse_return F z hz) a b)
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
    Lean.Elab.Tactic.replaceMainGoal []

private def sandwichRead {R : Type*} [Ring R] [Module ℂ R] [IsScalarTower ℂ R R]
    [SMulCommClass ℂ R R] (r : R) : R →ₗ[ℂ] R where
  toFun x := r*x*r
  map_add' x y := by noncomm_ring
  map_smul' c x := by simp only [mul_smul_comm,smul_mul_assoc,RingHom.id_apply]

private theorem retarded_select {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (r P : R) (S O X I : ℕ → ℕ → R) (hP : P=select O-select I)
    (hX : ∀ a b,X a b=S a b-r*O a b*r) :
    r*P*r=select S-select X-r*select I*r := by
  have h := congrArg (sandwichRead r) hP
  rw [map_sub,←select_linear] at h
  have hc : select X=select S-select (fun a b => sandwichRead r (O a b)) := by
    have he : X=fun a b => S a b-r*O a b*r := funext (fun a => funext (hX a))
    rw [he,select_sub]
    rfl
  change _= _-select X-sandwichRead r (select I)
  rw [hc]
  exact h.trans (by abel)

private theorem source_retarded_polynomial (F : Index) (g : diagonal.domain) (z : ℂ)
    (hz : z.im≠0) (A : End) :
    finiteResolvent F z*sourceRead F g (corePolynomial A)*finiteResolvent F z=
      select (fun a b => sandwichJet F g z A a b 0 0)-select (inverseCross F g z A)-
      finiteResolvent F z*select (inputFlux F g A)*finiteResolvent F z := by
  have h := retarded_select (R := Op) (finiteResolvent F z) (sourceRead F g (corePolynomial A))
    (fun a b => sandwichJet F g z A a b 0 0) (fun a b => readOrbitJet F g A a b 0 0)
    (inverseCross F g z A) (inputFlux F g A) (source_read_orbit_polynomial F g A)
    (cross_return F g z hz A)
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
    Lean.Elab.Tactic.replaceMainGoal []


private theorem coframe_sub {R : Type*} [AddCommGroup R]
    (L M : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R) (a r u v w : ℕ) (s t : ℝ) :
    coframeLeibniz a r u v w (fun i j k l s t => L i j k l s t-M i j k l s t) s t=
      coframeLeibniz a r u v w L s t-coframeLeibniz a r u v w M s t := by
  induction a generalizing r u v w with
  | zero => rfl
  | succ a ih => simp only [coframeLeibniz,ih]; abel

private theorem mixed_sub {R : Type*} [AddCommGroup R]
    (L M : ℕ → ℕ → ℕ → ℕ → ℝ → ℝ → R) (a b r u v w : ℕ) (s t : ℝ) :
    mixedLeibniz a b r u v w (fun i j k l s t => L i j k l s t-M i j k l s t) s t=
      mixedLeibniz a b r u v w L s t-mixedLeibniz a b r u v w M s t := by
  induction b generalizing r u v w with
  | zero => exact coframe_sub L M a r u v w s t
  | succ b ih => simp only [mixedLeibniz,ih]; abel

private theorem product_sub_left {R : Type*} [Ring R]
    (A B C : ℕ → ℕ → ℝ → ℝ → R) (a b : ℕ) (s t : ℝ) :
    productJet (fun i j s t => A i j s t-B i j s t) C a b s t=
      productJet A C a b s t-productJet B C a b s t := by
  unfold productJet productLeaf
  simp only [sub_mul]
  exact mixed_sub (R := R) _ _ a b 0 0 0 0 s t

private theorem product_sub_right {R : Type*} [Ring R]
    (A B C : ℕ → ℕ → ℝ → ℝ → R) (a b : ℕ) (s t : ℝ) :
    productJet A (fun i j s t => B i j s t-C i j s t) a b s t=
      productJet A B a b s t-productJet A C a b s t := by
  unfold productJet productLeaf
  simp only [mul_sub]
  exact mixed_sub (R := R) _ _ a b 0 0 0 0 s t

private theorem surround_sub (F : Index) (z : ℂ) (A B : ℕ → ℕ → ℝ → ℝ → Op)
    (a b : ℕ) (s t : ℝ) :
    surroundJet F z (fun i j s t => A i j s t-B i j s t) a b s t=
      surroundJet F z A a b s t-surroundJet F z B a b s t := by
  have he : productJet (fun i j s t => A i j s t-B i j s t)
      (SourceGaugeCoframeJets.resolventJet F z)=fun i j s t =>
      productJet A (SourceGaugeCoframeJets.resolventJet F z) i j s t-
      productJet B (SourceGaugeCoframeJets.resolventJet F z) i j s t := by
    funext i j s t
    exact product_sub_left A B _ i j s t
  unfold surroundJet
  rw [he,product_sub_right]

private def readDoubleJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :=
  commutatorJet (SourceGaugeCoframeJets.compressionJet F)
    (commutatorJet (SourceGaugeCoframeJets.compressionJet F)
      (readOrbitJet F g (fullInsertion sharp m ell)))

/-- All three original nested finite-compression defects, evolved by the same actual group. -/
def tripleFluxJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (a b : ℕ) (s t : ℝ) : Op :=
  readOrbitJet F g (sourceDouble sharp m ell) a b s t-readDoubleJet sharp m ell F g a b s t

/-- The complete left input-span shadow; no cutoff-dependent vector is declared supported. -/
def shadowJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (a b : ℕ) (s t : ℝ) : Op :=
  commutatorJet (SourceGaugeCoframeJets.compressionJet F)
    (commutatorJet (SourceGaugeCoframeJets.compressionJet F)
      (constantJet (SourceEscapeSeedTail.actualIncrement sharp m ell))) a b s t-
    readDoubleJet sharp m ell F g a b s t

theorem triple_flux_origin (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    tripleFluxJet sharp m ell F g 0 0 0 0=doubleProjectionFlux sharp m ell F g := by
  have hp : sourceRead F g (sourceDouble sharp m ell)-
      SourceScalarForceBudget.doubleResponse sharp m ell F g=doubleProjectionFlux sharp m ell F g := by
    have h := (actual_double_projection_flux sharp m ell F g).symm
    run_tac Lean.Elab.Tactic.withMainContext do
      (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
      Lean.Elab.Tactic.replaceMainGoal []
  have hc : tripleFluxJet sharp m ell F g 0 0 0 0=
      sourceRead F g (sourceDouble sharp m ell)-SourceScalarForceBudget.doubleResponse sharp m ell F g := by
    simp only [tripleFluxJet,readDoubleJet,commutatorJet,productJet,mixedLeibniz,coframeLeibniz,
      productLeaf,compression_origin,read_orbit_origin]
    rfl
  exact hc.trans hp

private theorem source_read_full (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    sourceRead F g (fullInsertion sharp m ell)=
      SourceEscapeSeedTail.actualIncrement sharp m ell*(inputSpan F g).starProjection := by
  apply ContinuousLinearMap.ext
  intro x
  let q := coreEquiv.symm (Submodule.inclusion (input_span_core F g)
    ((inputSpan F g).orthogonalProjectionOnto x))
  have h := SourceCutoffDilationWard.literal_increment_core sharp m ell q
  have hf := congrArg embed (LinearMap.congr_fun (SourceMixedNativeReturn.literal_full_return sharp m ell) q)
  have hq : embed q=(inputSpan F g).starProjection x :=
    congrArg Subtype.val (coreEquiv.apply_symm_apply
      (Submodule.inclusion (input_span_core F g) ((inputSpan F g).orthogonalProjectionOnto x)))
  change embed (fullInsertion sharp m ell q)=
    SourceEscapeSeedTail.actualIncrement sharp m ell ((inputSpan F g).starProjection x)
  rw [←hq]
  exact hf.symm.trans h.symm

def inputShadow (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) : Op :=
  SourceEscapeSeedTail.actualIncrement sharp m ell*(1-(inputSpan F g).starProjection)

private theorem double_shadow {R : Type*} [Ring R] (C B P : R) :
    (C*(C*B-B*C)-(C*B-B*C)*C)-
      (C*(C*(B*P)-(B*P)*C)-(C*(B*P)-(B*P)*C)*C)=
    C*(C*(B*(1-P))-(B*(1-P))*C)-(C*(B*(1-P))-(B*(1-P))*C)*C := by noncomm_ring

/-- The shadow at the origin is the actual double compression commutator of B(1−Πinput). -/
theorem input_shadow_origin (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) :
    shadowJet sharp m ell F g 0 0 0 0=
      GaussGradedCompression.compression F*
        (GaussGradedCompression.compression F*inputShadow sharp m ell F g-
          inputShadow sharp m ell F g*GaussGradedCompression.compression F)-
        (GaussGradedCompression.compression F*inputShadow sharp m ell F g-
          inputShadow sharp m ell F g*GaussGradedCompression.compression F)*GaussGradedCompression.compression F := by
  simp only [shadowJet,readDoubleJet,commutatorJet,productJet,mixedLeibniz,coframeLeibniz,
    productLeaf,constantJet,and_self,if_true,compression_origin,read_orbit_origin,source_read_full,inputShadow]
  exact double_shadow _ _ _

def tripleResponseJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) :=
  surroundJet F z (tripleFluxJet sharp m ell F g)

def shadowResponseJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) :=
  surroundJet F z (shadowJet sharp m ell F g)

private theorem actual_sandwich_split (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (a b : ℕ) (s t : ℝ) :
    sandwichJet F g z (sourceDouble sharp m ell) a b s t=
      doubleOrbitJet sharp m ell F z a b s t+tripleResponseJet sharp m ell F g z a b s t-
        shadowResponseJet sharp m ell F g z a b s t := by
  unfold sandwichJet doubleOrbitJet tripleResponseJet shadowResponseJet tripleFluxJet shadowJet
  rw [surround_sub,surround_sub]
  abel

private theorem select_add {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A B : ℕ → ℕ → V) : select (fun a b => A a b+B a b)=select A+select B := by
  simp only [select,smul_add]
  abel

/-- Complete actual source/finite Ward square, keeping the original three defects, input shadow, and inverse crosses. -/
theorem actual_ordered_source_ward (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z*sourceRead F g (corePolynomial (sourceDouble sharp m ell))*finiteResolvent F z=
      select (fun a b => doubleOrbitJet sharp m ell F z a b 0 0)+
      select (fun a b => tripleResponseJet sharp m ell F g z a b 0 0)-
      select (fun a b => shadowResponseJet sharp m ell F g z a b 0 0)-
      select (inverseCross F g z (sourceDouble sharp m ell))-
      finiteResolvent F z*select (inputFlux F g (sourceDouble sharp m ell))*finiteResolvent F z := by
  have h := source_retarded_polynomial F g z hz (sourceDouble sharp m ell)
  simpa only [actual_sandwich_split,select_sub,select_add] using! h

/-- The complete source response, before any norm or triangle bound. -/
def orderedResponse (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  select (fun a b => doubleOrbitJet sharp m ell F z a b 0 0)+
  select (fun a b => tripleResponseJet sharp m ell F g z a b 0 0)-
  select (fun a b => shadowResponseJet sharp m ell F g z a b 0 0)-
  select (inverseCross F g z (sourceDouble sharp m ell))-
  finiteResolvent F z*select (inputFlux F g (sourceDouble sharp m ell))*finiteResolvent F z

private theorem finite_current_return (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z*SourceScalarForceBudget.doubleResponse sharp m ell F g*finiteResolvent F z=
      doubleOrbitJet sharp m ell F z 0 0 0 0-shadowResponseJet sharp m ell F g z 0 0 0 0 := by
  have h : doubleOrbitJet sharp m ell F z 0 0 0 0-shadowResponseJet sharp m ell F g z 0 0 0 0=
      surroundJet F z (readDoubleJet sharp m ell F g) 0 0 0 0 := by
    unfold doubleOrbitJet shadowResponseJet shadowJet
    rw [surround_sub]
    abel
  apply Eq.symm
  refine h.trans ?_
  simp only [surroundJet,readDoubleJet,commutatorJet,productJet,mixedLeibniz,coframeLeibniz,
    productLeaf,resolvent_origin F z hz,compression_origin,read_orbit_origin]
  simp only [SourceScalarForceBudget.doubleResponse,bracket,mul_assoc]

/-- The complete balanced force Ward word, with literal cutoff Euler, vacuum, and Hardy terms. -/
def wardOperator (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  doubleOrbitJet sharp m ell F z 0 0 0 0-shadowResponseJet sharp m ell F g z 0 0 0 0-
  (1/48 : ℂ) • orderedResponse sharp m ell F g z-
  (2*(sourceTime 0 : ℂ)^2) •
    (finiteResolvent F z*sourceRead F g (fullAction sharp*cutoffEuler m ell)*finiteResolvent F z)+
  (2*(sourceTime 0 : ℂ)^2) •
    (finiteResolvent F z*sourceRead F g (constantAction sharp vacuum*thetaAction m ell)*finiteResolvent F z)-
  (SourceScalarForceBudget.oscillatorMass : ℂ) •
    (finiteResolvent F z*SourceScalarForceBudget.solverOperator sharp m ell F*finiteResolvent F z)

private theorem balanced_sandwich {R : Type*} [Ring R] [Module ℂ R]
    [IsScalarTower ℂ R R] [SMulCommClass ℂ R R]
    (r B D P E V S W D' : R) (a mass : ℂ)
    (hB : B=D-(1/48 : ℂ) • P-a • E+a • V-mass • S)
    (hP : r*P*r=W) (hD : r*D*r=D') :
    r*B*r=D'-(1/48 : ℂ) • W-a • (r*E*r)+a • (r*V*r)-mass • (r*S*r) := by
  have h := congrArg (sandwichRead r) hB
  simp only [map_sub,map_add,map_smul,sandwichRead,LinearMap.coe_mk,AddHom.coe_mk] at h
  simpa only [hP,hD] using h

/-- The literal original balanced force equals the generated complete Ward word on all H. -/
theorem actual_balanced_ward (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    finiteResolvent F z*SourceScalarForceBudget.balancedForce sharp m ell F g*finiteResolvent F z=
      wardOperator sharp m ell F g z := by
  have hp : finiteResolvent F z*sourceRead F g (corePolynomial (sourceDouble sharp m ell))*finiteResolvent F z=
      orderedResponse sharp m ell F g z := by
    have h := actual_ordered_source_ward sharp m ell F g z hz
    run_tac Lean.Elab.Tactic.withMainContext do
      (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
      Lean.Elab.Tactic.replaceMainGoal []
  have h := balanced_sandwich (R := Op) (finiteResolvent F z)
    (SourceScalarForceBudget.balancedForce sharp m ell F g)
    (SourceScalarForceBudget.doubleResponse sharp m ell F g)
    (sourceRead F g (corePolynomial (sourceDouble sharp m ell)))
    (sourceRead F g (fullAction sharp*cutoffEuler m ell))
    (sourceRead F g (constantAction sharp vacuum*thetaAction m ell))
    (SourceScalarForceBudget.solverOperator sharp m ell F) (orderedResponse sharp m ell F g z)
    (doubleOrbitJet sharp m ell F z 0 0 0 0-shadowResponseJet sharp m ell F g z 0 0 0 0)
    (2*(sourceTime 0 : ℂ)^2) (SourceScalarForceBudget.oscillatorMass : ℂ)
    (actual_balanced_polynomial_return sharp m ell F g)
    hp (finite_current_return sharp m ell F g z hz)
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
    Lean.Elab.Tactic.replaceMainGoal []

def wardProfile (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain) (z : ℂ) : ℂ :=
  inner ℂ (k : H) (wardOperator sharp m ell F g z (g : H))

private theorem pair_sandwich {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (r B W : E →L[ℂ] E) (g k : E) (h : r*B*r=W) :
    inner ℂ k (r (B (r g)))=inner ℂ k (W g) :=
  congrArg (fun A : E →L[ℂ] E => inner ℂ k (A g)) h

theorem actual_ward_profile (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    SourceScalarForceBudget.response F z (SourceScalarForceBudget.balancedForce sharp m ell F g)
      (g : H) (k : H)=wardProfile sharp m ell F g k z := by
  have h := pair_sandwich (E := H) (finiteResolvent F z)
    (SourceScalarForceBudget.balancedForce sharp m ell F g) (wardOperator sharp m ell F g z)
    (g : H) (k : H) (actual_balanced_ward sharp m ell F g z hz)
  run_tac Lean.Elab.Tactic.withMainContext do
    (← Lean.Elab.Tactic.getMainGoal).assign (← Lean.Meta.getFVarFromUserName `h)
    Lean.Elab.Tactic.replaceMainGoal []

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
    Complex.I_im,Complex.ofReal_re,zero_mul,one_mul,mul_one,zero_add,mul_zero,add_zero] using hμ.ne'

/-- The complete Ward word has the exact finite whole-channel Gram energy, including all signed crosses. -/
theorem actual_ward_energy (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain)
    (μ : ℝ) (hμ : 0<μ) :
    (∫ w : ℝ, ‖wardProfile sharp m ell F g k (line μ w)‖^2)=
      SourceScalarForceBudget.pairEnergy F μ (SourceScalarForceBudget.balancedForce sharp m ell F g)
        (g : H) (k : H) := by
  have h := SourceScalarForceBudget.actual_response_energy F μ hμ
    (SourceScalarForceBudget.balancedForce sharp m ell F g) (g : H) (k : H)
  simpa only [actual_ward_profile sharp m ell F g k _ (line_nonreal μ hμ _)] using! h

theorem actual_ward_integrable (sharp : Bool) (m ell : ℕ) (F : Index) (g k : diagonal.domain)
    (μ : ℝ) (hμ : 0<μ) : Integrable (fun w : ℝ => ‖wardProfile sharp m ell F g k (line μ w)‖^2) := by
  have h := SourceScalarForceBudget.actual_response_integrable F μ hμ
    (SourceScalarForceBudget.balancedForce sharp m ell F g) (g : H) (k : H)
  simpa only [actual_ward_profile sharp m ell F g k _ (line_nonreal μ hμ _)] using! h

/-- The complete same-source Ward response is consumed by the original ε/N/m/ell/sourceFilter target. -/
theorem actual_joint_ward_tail_iff (sharp : Bool) (g k : diagonal.domain) (μ : ℝ) (hμ : 0<μ) :
    (∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        SourceFourPoleEnergyClosed.closedJointCost sharp m ell F μ (g : H) (k : H) ≤ ε) ↔
    (∀ ε : ℝ, 0<ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫ w : ℝ, ‖wardProfile sharp m ell F g k (line μ w)‖^2) ≤ ε) := by
  simpa only [actual_ward_energy sharp _ _ _ g k μ hμ] using!
    SourceScalarEndpointCost.actual_joint_force_tail_iff sharp g k μ hμ

private theorem commute_conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (B : E →L[ℂ] E)
    (h : Commute B U.toContinuousLinearEquiv.toContinuousLinearMap) : U.conjStarAlgEquiv B=B := by
  apply ContinuousLinearMap.ext
  intro x
  have he := congrArg (fun A : E →L[ℂ] E => A (U.symm x)) h.eq
  change B (U (U.symm x))=U (B (U.symm x)) at he
  rw [LinearIsometryEquiv.apply_symm_apply] at he
  exact he.symm

private theorem conjugate_trans {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U V : E ≃ₗᵢ[ℂ] E) (B : E →L[ℂ] E) :
    (U.trans V).conjStarAlgEquiv B=V.conjStarAlgEquiv (U.conjStarAlgEquiv B) := rfl

/-- The full bounded source insertion is fixed by the actual two-parameter unitary. -/
theorem actual_increment_mixed_invariant (sharp : Bool) (m ell : ℕ) (s t : ℝ) :
    (SourceGaugeCoframeJets.mixedHilbert s t).conjStarAlgEquiv
      (SourceEscapeSeedTail.actualIncrement sharp m ell)=SourceEscapeSeedTail.actualIncrement sharp m ell := by
  have hc := SourceScalarCoframeInvariant.actual_increment_coframe_invariant sharp m ell ((3/2 : ℝ)*s)
  have hg := commute_conjugate (E := H) (SourceGaugeScaleTransport.hilbertFlow t)
    (SourceEscapeSeedTail.actualIncrement sharp m ell)
    (SourceScalarGaugeEndpoint.actual_increment_gauge_commute sharp m ell t)
  exact (conjugate_trans (E := H) (SourceGaugeCoframeJets.coframeHilbert s)
    (SourceGaugeScaleTransport.hilbertFlow t) (SourceEscapeSeedTail.actualIncrement sharp m ell)).trans
      ((congrArg (SourceGaugeScaleTransport.hilbertFlow t).conjStarAlgEquiv hc).trans hg)

private theorem map_double_return {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (r c B rs cs : R) (hr : rs=e r) (hc : cs=e c) (hB : e B=B) :
    rs*(cs*(cs*B-B*cs)-(cs*B-B*cs)*cs)*rs=
      e (r*(c*(c*B-B*c)-(c*B-B*c)*c)*r) := by
  simp only [hr,hc,map_mul,map_sub,hB]

/-- The main mixed double-current jet is the actual conjugated whole-H double response at order zero. -/
theorem actual_double_mixed_orbit (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (s t : ℝ) :
    doubleOrbitJet sharp m ell F z 0 0 s t=
      (SourceGaugeCoframeJets.mixedHilbert s t).conjStarAlgEquiv
        (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F z) := by
  exact (double_orbit_base sharp m ell F z s t).trans
    (map_double_return (R := Op) (SourceGaugeCoframeJets.mixedHilbert s t).conjStarAlgEquiv
      (finiteResolvent F z) (GaussGradedCompression.compression F)
      (SourceEscapeSeedTail.actualIncrement sharp m ell)
      (SourceGaugeCoframeJets.resolventJet F z 0 0 s t)
      (SourceGaugeCoframeJets.compressionJet F 0 0 s t)
      (SourceGaugeCoframeJets.actual_mixed_resolvent F z hz s t)
      (SourceGaugeCoframeJets.actual_mixed_compression F s t)
      (actual_increment_mixed_invariant sharp m ell s t))

private theorem pair_conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (U : E ≃ₗᵢ[ℂ] E) (B : E →L[ℂ] E) (x y : E) :
    inner ℂ x (U.conjStarAlgEquiv B y)=inner ℂ (U.symm x) (B (U.symm y)) := by
  change inner ℂ x (U (B (U.symm y)))=_
  simpa only [LinearIsometryEquiv.apply_symm_apply] using
    U.inner_map_map (U.symm x) (B (U.symm y))

/-- The exact moving main profile uses fixed original vectors transported by the real source group. -/
theorem actual_double_mixed_profile (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (hz : z.im≠0) (s t : ℝ) (g k : H) :
    inner ℂ k (doubleOrbitJet sharp m ell F z 0 0 s t g)=
      inner ℂ ((SourceGaugeCoframeJets.mixedHilbert s t).symm k)
        (SourceScalarGaugeEndpoint.wholeDouble sharp m ell F z
          ((SourceGaugeCoframeJets.mixedHilbert s t).symm g)) := by
  have h := congrArg (fun A : Op => inner ℂ k (A g))
    (actual_double_mixed_orbit sharp m ell F z hz s t)
  exact h.trans (pair_conjugate (E := H) (SourceGaugeCoframeJets.mixedHilbert s t) _ k g)

end LowEnergy.SourceGaugeCoframeWard
