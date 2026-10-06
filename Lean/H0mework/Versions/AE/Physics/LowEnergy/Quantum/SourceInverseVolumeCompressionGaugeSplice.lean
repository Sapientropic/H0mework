import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceInverseVolumeCompressionGaugeBudget

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseCompressionGaugeSplice
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarGaugeScale
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceScalarGaugeForce SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceInverseFirstCurrentRemainder SourceInverseProjectionCurrentRemainder
open SourceInverseGaugeSingleDefectJoin SourceInverseCompressionGaugeBudget Filter MeasureTheory SourceResolventBandLimit
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction matterAction
  sourceRead state sourcePair defectAction compressionCore deltaGauge
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  singleDefect singleDefectRemainder linearDefectJet matterInsertion matterHamiltonianCurrent
  readOrbitJet sandwichJet inverseCross inputFlux resolventJet
  cutoffEuler scaleDoubleRemainder constantAction SourceScalarForceBudget.solverOperator
  SourceScalarForceBudget.oscillatorMass wardOperator

private theorem origin_conjugate (A : Op) : (mixedHilbert 0 0).conjStarAlgEquiv A=A := by
  have hu (x : H) : mixedHilbert 0 0 x=x := by
    simp only [mixedHilbert,LinearIsometryEquiv.trans_apply,coframeHilbert,mul_zero,
      SourceCoframeScaleTransport.hilbertFlow_zero,SourceGaugeScaleTransport.hilbertFlow_zero]
  apply ContinuousLinearMap.ext
  intro x
  change mixedHilbert 0 0 (A ((mixedHilbert 0 0).symm x))=A x
  have hi : (mixedHilbert 0 0).symm x=x := by
    apply (mixedHilbert 0 0).injective
    rw [LinearIsometryEquiv.apply_symm_apply,hu]
  rw [hi,hu]

private theorem map_sandwich {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (r a : R) : e r*(e a*e r)=e (r*a*r) := by
  simp only [map_mul,mul_assoc]

private theorem sandwich_orbit (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (t : ℝ) :
    sandwichJet F g z A 0 0 0 t=(mixedHilbert 0 t).conjStarAlgEquiv
      (finiteResolvent F z*sourceRead F g A*finiteResolvent F z) := by
  unfold sandwichJet
  change resolventJet F z 0 0 0 t*(readOrbitJet F g A 0 0 0 t*resolventJet F z 0 0 0 t)=_
  exact (congrArg₂ (fun r a : Op => r*(a*r))
    (actual_mixed_resolvent F z hz 0 t) (actual_read_orbit F g A 0 t)).trans
      (map_sandwich _ _ _)

private theorem map_sandwich_sub {R : Type*} [Ring R] [Module ℂ R] [Star R]
    (e : R ≃⋆ₐ[ℂ] R) (r a b : R) : e (r*(a-b)*r)=e (r*a*r)-e (r*b*r) := by
  simp only [mul_sub,sub_mul,map_sub]

private theorem sandwich_sub (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A B : End) (n : ℕ) (t : ℝ) :
    sandwichJet F g z (A-B) 0 n 0 t=sandwichJet F g z A 0 n 0 t-sandwichJet F g z B 0 n 0 t := by
  induction n generalizing t with
  | zero =>
    have hr := sandwich_orbit F g z hz (A-B) t
    have hm : sourceRead F g (A-B)=sourceRead F g A-sourceRead F g B := map_sub (sourceRead F g) A B
    have he := congrArg (fun a : Op => (mixedHilbert 0 t).conjStarAlgEquiv
      (finiteResolvent F z*a*finiteResolvent F z)) hm
    have ho := congrArg₂ (fun a b : Op => a-b) (sandwich_orbit F g z hz A t) (sandwich_orbit F g z hz B t)
    exact hr.trans (he.trans ((map_sandwich_sub _ _ _ _).trans ho.symm))
  | succ n ih =>
    have hd := (sandwich_gauge_derivative F g z A 0 n 0 t).sub (sandwich_gauge_derivative F g z B 0 n 0 t)
    exact (sandwich_gauge_derivative F g z (A-B) 0 n 0 t).unique
      (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall ih))

/-- The full uncompressed source commutator, with the original H on its outer leg. -/
def secondHamiltonianCurrent (sharp : Bool) (m ell : ℕ) : End :=
  bracket diagonalAction (firstHamiltonianCurrent sharp m ell)

def hamiltonianGaugeForce (sharp : Bool) (m ell : ℕ) : End :=
  bracket (deltaGauge diagonalAction) (firstHamiltonianCurrent sharp m ell)

def hamiltonianCorrectionJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  sandwichJet F g z (secondHamiltonianCurrent sharp m ell) 0 (n+1) 0 t-
    sandwichJet F g z (deltaGauge (secondHamiltonianCurrent sharp m ell)) 0 n 0 t

def hamiltonianGaugeJet (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (n : ℕ) (t : ℝ) : Op :=
  sandwichJet F g z (hamiltonianGaugeForce sharp m ell) 0 n 0 t

private theorem single_split (sharp : Bool) (m ell : ℕ) (F : Index) :
    singleDefect sharp m ell F=secondHamiltonianCurrent sharp m ell-compressionFirst sharp m ell F := by
  unfold singleDefect secondHamiltonianCurrent compressionFirst firstHamiltonianCurrent defectAction bracket
  noncomm_ring

private theorem gauge_force_split (sharp : Bool) (m ell : ℕ) (F : Index) :
    gaugeDefectCurrent sharp m ell F=hamiltonianGaugeForce sharp m ell-compressionGaugeForce sharp m ell F := by
  have hd : gaugeDefect F=deltaGauge diagonalAction-deltaGauge (compressionCore F) :=
    (original_gauge_defect F).symm.trans (by unfold defectAction; exact map_sub deltaGauge _ _)
  unfold gaugeDefectCurrent hamiltonianGaugeForce compressionGaugeForce
  rw [hd]
  unfold bracket
  noncomm_ring

private theorem compression_gauge_split (sharp : Bool) (m ell : ℕ) (F : Index) :
    compressionMatter sharp m ell F=deltaGauge (compressionFirst sharp m ell F)-compressionGaugeForce sharp m ell F := by
  have h (A B : End) : deltaGauge (bracket A B)=bracket (deltaGauge A) B+bracket A (deltaGauge B) := by
    unfold deltaGauge bracket
    change SourceGaugeRadialPair.gaugeEulerAction*(A*B-B*A)-(A*B-B*A)*SourceGaugeRadialPair.gaugeEulerAction=
      (SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)*B-
        B*(SourceGaugeRadialPair.gaugeEulerAction*A-A*SourceGaugeRadialPair.gaugeEulerAction)+
      (A*(SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)-
        (SourceGaugeRadialPair.gaugeEulerAction*B-B*SourceGaugeRadialPair.gaugeEulerAction)*A)
    noncomm_ring
  have hs := h (compressionCore F) (firstHamiltonianCurrent sharp m ell)
  rw [original_first_current_gauge] at hs
  change deltaGauge (compressionFirst sharp m ell F)=compressionGaugeForce sharp m ell F+compressionMatter sharp m ell F at hs
  exact eq_sub_of_add_eq (add_comm _ _ |>.trans hs.symm)

attribute [local irreducible] firstHamiltonianCurrent secondHamiltonianCurrent hamiltonianGaugeForce
  compressionFirst compressionMatter compressionGaugeForce gaugeDefectCurrent
  derivativeCorrectionJet gaugeDefectResponseJet singleResponseJet correctedCompressionJet
  hamiltonianCorrectionJet hamiltonianGaugeJet

private theorem source_jet_sub (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0)
    (A B C : End) (he : A=B-C) (n : ℕ) (t : ℝ) :
    sandwichJet F g z A 0 n 0 t=sandwichJet F g z B 0 n 0 t-sandwichJet F g z C 0 n 0 t :=
  (congrArg (fun D : End => sandwichJet F g z D 0 n 0 t) he).trans (sandwich_sub F g z hz B C n t)

/-- The original two signed corrections split off exactly the compression-gauge current whose tail has been generated. -/
theorem actual_correction_split (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) (n : ℕ) (t : ℝ) :
    derivativeCorrectionJet sharp m ell F g z n t+gaugeDefectResponseJet sharp m ell F g z n t=
      hamiltonianCorrectionJet sharp m ell F g z n t+hamiltonianGaugeJet sharp m ell F g z n t-
        correctedCompressionJet sharp m ell F g z n t := by
  have hU := source_jet_sub F g z hz _ _ _ (single_split sharp m ell F) (n+1) t
  have hdU : deltaGauge (singleDefect sharp m ell F)=
      deltaGauge (secondHamiltonianCurrent sharp m ell)-deltaGauge (compressionFirst sharp m ell F) :=
    (congrArg deltaGauge (single_split sharp m ell F)).trans (map_sub deltaGauge _ _)
  have hD := source_jet_sub F g z hz _ _ _ hdU n t
  have hT := source_jet_sub F g z hz _ _ _ (gauge_force_split sharp m ell F) n t
  have hC := source_jet_sub F g z hz _ _ _ (compression_gauge_split sharp m ell F) n t
  simp only [derivativeCorrectionJet,gaugeDefectResponseJet,singleResponseJet,hamiltonianCorrectionJet,
    hamiltonianGaugeJet,correctedCompressionJet]
  linear_combination (norm := module) hU-hD+hT-hC

/-- The remainder keeps the full U_F family and original inverse legs, with the already paid CF gauge-force block removed. -/
def reducedGaugeRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • (joinedPolynomial (fun n => singleResponseJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => hamiltonianCorrectionJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => hamiltonianGaugeJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*
      finiteResolvent F z)+
  finiteResolvent F z*(sourceRead F g
    (-(2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
      (2*(GaussNativeEnergy.sourceTime 0 : ℂ)^2) •
        (constantAction sharp SourceQuantumScalarChart.vacuum*SourceMixedNativeReturn.thetaAction m ell)-
      (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-
    (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F)*finiteResolvent F z

/-- The paid joint compression correction is extracted with its original sign and source coefficient. -/
theorem actual_joined_remainder_split (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) : joinedRemainder sharp m ell F g z=
      reducedGaugeRemainder sharp m ell F g z+
        (1/6 : ℂ) • gaugeFilter (fun n => correctedCompressionJet sharp m ell F g z n 0) := by
  have h0 := actual_correction_split sharp m ell F g z hz 0 0
  have h1 := actual_correction_split sharp m ell F g z hz 1 0
  have h2 := actual_correction_split sharp m ell F g z hz 2 0
  simp only [joinedRemainder,reducedGaugeRemainder,gaugeFilter]
  linear_combination (norm := module) -(1/6 : ℂ) • h2+(1/2 : ℂ) • h1-(1/3 : ℂ) • h0

/-- Same actual input, dual and cofinal event: the whole Ward is the reduced source remainder plus the two generated paid currents. -/
theorem actual_ward_reduced_gauge (m ell : ℕ) (f k : QuantumTest) :
    ∀ᶠ F in (sourceFilter : Filter Index),∀ (sharp : Bool) (z : ℂ),z.im≠0 →
      inner ℂ (embed k) (wardOperator sharp m ell F (coreEquiv f) z (embed f))=
        inner ℂ (embed k) (reducedGaugeRemainder sharp m ell F (coreEquiv f) z (embed f))+
        (1/6 : ℂ)*filteredProfile sharp m ell F z f k+
        (1/6 : ℂ)*inner ℂ (embed k)
          (gaugeFilter (fun n => correctedCompressionJet sharp m ell F (coreEquiv f) z n 0) (embed f)) := by
  filter_upwards [actual_ward_joined_remainder m ell f k] with F hF
  intro sharp z hz
  have hs := congrArg (fun A : Op => inner ℂ (embed k) (A (embed f)))
    (actual_joined_remainder_split sharp m ell F (coreEquiv f) z hz)
  simp only [add_apply,smul_apply,inner_add_right,inner_smul_right] at hs
  exact (hF sharp z hz).trans ((congrArg (fun a : ℂ => (1/6 : ℂ)*filteredProfile sharp m ell F z f k+a) hs).trans (by ring))

private def gp (A B : ℕ → ℝ → Op) : ℕ → ℕ → ℕ → ℝ → Op
  | 0,r,u,w => A r w*B u w
  | n+1,r,u,w => gp A B n (r+1) u w+gp A B n r (u+1) w

private theorem gp_continuous (A B : ℕ → ℝ → Op) (hA : ∀ r,Continuous (A r))
    (hB : ∀ u,Continuous (B u)) (n r u : ℕ) : Continuous (gp A B n r u) := by
  induction n generalizing r u with
  | zero => exact (hA r).mul (hB u)
  | succ n ih => exact (ih (r+1) u).add (ih r (u+1))

private theorem inverse_jet_continuous (F : Index) (μ : ℝ) (hμ : 0<μ) (j : ℕ) :
    Continuous (fun w : ℝ => resolventJet F (line μ w) 0 j 0 0) := by
  have hz (w : ℝ) : line μ w≠0 := by
    intro he
    have hi := congrArg Complex.im he
    exact hμ.ne' (by simpa only [line_im,Complex.zero_im] using hi)
  have hd (r w : ℝ) : (r : ℂ)-line μ w≠0 := by
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im,Complex.ofReal_im,line_im,Complex.zero_im,zero_sub,neg_eq_zero] at hi
    exact hμ.ne' hi
  have hl : Continuous (line μ) := by unfold line; fun_prop
  have hzi := hl.inv₀ hz
  have hdi (r : ℝ) := (continuous_const.sub hl).inv₀ (hd r)
  unfold resolventJet
  have hs : Continuous (fun w : ℝ => ∑ i : SourceJointResidualEnergy.SpectralIndex F,
      ((((SourceJointResidualEnergy.channelValue F (some i) : ℂ)-line μ w)⁻¹+(line μ w)⁻¹) •
        SourceGaugeCoframeJets.rankJet 0 j (SourceMovingJetFlux.eigenTest F i) (SourceMovingJetFlux.eigenTest F i) 0 0)) := by
    apply continuous_finsetSum
    intro i _
    exact ((hdi _).add hzi).smul continuous_const
  split_ifs
  · exact (hzi.neg.smul continuous_const).add hs
  · exact continuous_const.add hs

private theorem small_sandwich (F : Index) (seed : diagonal.domain) (A : End) (μ w : ℝ) (n : Fin 4) :
    sandwichJet F seed (line μ w) A 0 n 0 0=
      gp (fun j w => resolventJet F (line μ w) 0 j 0 0)
        (fun j w => gp (fun a _ => readOrbitJet F seed A 0 a 0 0)
          (fun a w => resolventJet F (line μ w) 0 a 0 0) j 0 0 w) n 0 0 w := by
  unfold sandwichJet
  fin_cases n <;> rfl

private theorem small_sandwich_continuous (F : Index) (seed : diagonal.domain) (A : End)
    (μ : ℝ) (hμ : 0<μ) (n : Fin 4) :
    Continuous (fun w : ℝ => sandwichJet F seed (line μ w) A 0 n 0 0) := by
  have hc := gp_continuous (fun j w => resolventJet F (line μ w) 0 j 0 0)
    (fun j w => gp (fun a _ => readOrbitJet F seed A 0 a 0 0)
      (fun a w => resolventJet F (line μ w) 0 a 0 0) j 0 0 w)
    (inverse_jet_continuous F μ hμ)
    (fun j => gp_continuous _ _ (fun _ => continuous_const) (inverse_jet_continuous F μ hμ) j 0 0) n 0 0
  exact hc.congr (fun w => (small_sandwich F seed A μ w n).symm)

private theorem corrected_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (seed : diagonal.domain)
    (μ : ℝ) (hμ : 0<μ) (n : Fin 3) (f k : QuantumTest) :
    Continuous (fun w : ℝ => inner ℂ (embed k)
      (correctedCompressionJet sharp m ell F seed (line μ w) n 0 (embed f))) := by
  unfold correctedCompressionJet
  have h1 := small_sandwich_continuous F seed (compressionFirst sharp m ell F) μ hμ ⟨n+1,by omega⟩
  have h0 := small_sandwich_continuous F seed (compressionMatter sharp m ell F) μ hμ ⟨n,by omega⟩
  exact continuous_const.inner ((h1.sub h0).clm_apply continuous_const)

private def Tail (f : ℕ → ℕ → Index → ℝ → ℂ) : Prop :=
  ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
    ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖f m ell F w‖^2))≤ENNReal.ofReal ε

private theorem tail_add (f g : ℕ → ℕ → Index → ℝ → ℂ)
    (hc : ∀ m ell F, Continuous (f m ell F))
    (hf : Tail f) (hg : Tail g) :
    Tail (fun m ell F w => f m ell F w+g m ell F w) := by
  intro ε hε
  obtain ⟨N₁,h₁⟩ := hf (ε/4) (by positivity)
  obtain ⟨N₂,h₂⟩ := hg (ε/4) (by positivity)
  refine ⟨max N₁ N₂,fun m hm ell hell => ?_⟩
  filter_upwards [h₁ m ((Nat.le_max_left _ _).trans hm) ell hell,
    h₂ m ((Nat.le_max_right _ _).trans hm) ell hell] with F hl hr
  have hp (a b : ℂ) : ‖a+b‖^2 ≤ 2*(‖a‖^2+‖b‖^2) := by
    have h := norm_add_le a b
    nlinarith [sq_nonneg (‖a‖-‖b‖),norm_nonneg (a+b),norm_nonneg a,norm_nonneg b]
  calc
    _ ≤ ∫⁻ w : ℝ, ENNReal.ofReal 2*(ENNReal.ofReal (‖f m ell F w‖^2)+
        ENNReal.ofReal (‖g m ell F w‖^2)) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [←ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
        ←ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
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

private theorem tail_congr (f h : ℕ → ℕ → Index → ℝ → ℂ)
    (he : ∀ m ell,∀ᶠ F in (sourceFilter : Filter Index),∀ w,f m ell F w=h m ell F w)
    (hh : Tail h) : Tail f := by
  intro ε hε
  obtain ⟨N,hN⟩ := hh ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell,he m ell] with F hF hEq
  simpa only [hEq] using hF

private theorem filter_coefficients (J : ℕ → Op) (f k : QuantumTest) :
    (1/6 : ℂ)*inner ℂ (embed k) (gaugeFilter J (embed f))=
      inner ℂ (embed k) (J 2 (embed ((1/6 : ℂ) • f)))+
      inner ℂ (embed k) (J 1 (embed ((-1/2 : ℂ) • f)))+
      inner ℂ (embed k) (J 0 (embed ((1/3 : ℂ) • f))) := by
  simp only [gaugeFilter,map_smul,add_apply,sub_apply,smul_apply,inner_add_right,inner_sub_right,inner_smul_right]
  ring

/-- The original Pg coefficient is consumed by the actual three finite jets of the paid signed CF correction. -/
theorem actual_corrected_filter_tail (sharp : Bool) (seed : diagonal.domain) (μ : ℝ) (hμ : 0<μ)
    (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖(1/6 : ℂ)*inner ℂ (embed k)
          (gaugeFilter (fun n => correctedCompressionJet sharp m ell F seed (line μ w) n 0) (embed f))‖^2))≤ENNReal.ofReal ε := by
  have h2 := actual_corrected_compression_tail sharp seed μ hμ 2 ((1/6 : ℂ) • f) k
  have h1 := actual_corrected_compression_tail sharp seed μ hμ 1 ((-1/2 : ℂ) • f) k
  have h0 := actual_corrected_compression_tail sharp seed μ hμ 0 ((1/3 : ℂ) • f) k
  have ht := tail_add _ _
    (fun m ell F => (corrected_continuous sharp m ell F seed μ hμ 2 _ k).add
      (corrected_continuous sharp m ell F seed μ hμ 1 _ k))
    (tail_add _ _ (fun m ell F => corrected_continuous sharp m ell F seed μ hμ 2 _ k) h2 h1) h0
  exact tail_congr _ _ (fun _ _ => Filter.Eventually.of_forall (fun _ _ => filter_coefficients _ f k)) ht

private theorem filtered_smul (sharp : Bool) (m ell : ℕ) (F : Index) (z : ℂ)
    (c : ℂ) (f k : QuantumTest) : filteredProfile sharp m ell F z (c • f) k=c*filteredProfile sharp m ell F z f k := by
  simp only [filteredProfile,gaugeFilter,SourceInverseFirstCurrentGaugeJets.profile,map_smul,inner_smul_right,smul_eq_mul]
  ring

private theorem filtered_continuous (sharp : Bool) (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ)
    (f k : QuantumTest) : Continuous (fun w : ℝ => (1/6 : ℂ)*filteredProfile sharp m ell F (line μ w) f k) := by
  have hc (a b : QuantumTest) : Continuous (fun w : ℝ => inner ℂ (embed b)
      (wholeResponse sharp m ell F (line μ w) (embed a))) := by
    have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
    unfold wholeResponse
    exact continuous_const.inner (((hr.mul continuous_const).mul hr).clm_apply continuous_const)
  have hs := ((((hc (G (G f)) k).add ((hc (G f) (G k)).const_mul (2 : ℂ))).add
    (hc f (G (G k)))).add ((hc (G f) k).const_mul (3 : ℂ))).add
      ((hc f (G k)).const_mul (3 : ℂ)) |>.add ((hc f k).const_mul (2 : ℂ))
  have h : Continuous (fun w : ℝ => filteredProfile sharp m ell F (line μ w) f k) :=
    hs.congr (fun w => (actual_filtered_profile sharp m ell F (line μ w)
      (by simpa only [line_im] using hμ.ne') f k).symm)
  exact continuous_const.mul h

/-- The literal whole Ward differs from the reduced joined remainder by a source-generated common full-frequency tail. -/
theorem actual_ward_reduced_difference_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (embed k)
          (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
          inner ℂ (embed k) (reducedGaugeRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))‖^2))≤ENNReal.ofReal ε := by
  have hfirst : Tail (fun m ell F w => (1/6 : ℂ)*filteredProfile sharp m ell F (line μ w) f k) := by
    intro ε hε
    obtain ⟨N,hN⟩ := actual_filtered_profile_tail sharp μ hμ ((1/6 : ℂ) • f) k ε hε
    refine ⟨N,fun m hm ell hell => Filter.Eventually.of_forall (fun F => ?_)⟩
    simpa only [filtered_smul] using hN m hm ell hell F
  have hpaid := tail_add _ _ (fun m ell F => filtered_continuous sharp m ell F μ hμ f k)
    hfirst (actual_corrected_filter_tail sharp (coreEquiv f) μ hμ f k)
  apply tail_congr _ _ ?_ hpaid
  intro m ell
  filter_upwards [actual_ward_reduced_gauge m ell f k] with F hF
  intro w
  have h := hF sharp (line μ w) (by simpa only [line_im] using hμ.ne')
  exact sub_eq_of_eq_add (h.trans (by ring))

end LowEnergy.SourceInverseCompressionGaugeSplice
