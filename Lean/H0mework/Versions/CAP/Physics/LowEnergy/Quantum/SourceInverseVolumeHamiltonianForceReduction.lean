import H0mework.Versions.CAP.Physics.LowEnergy.Quantum.SourceInverseVolumeCompressionGaugeSplice

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceInverseHamiltonianForceReduction
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussQuantumMultiplier
open GaussNativeForm GaussNativePotential GaussNativeEnergy GaussDiagonalHistory GaussUnitaryHistory GaussMatterCore
open SourceScalarPairedTransport SourceScalarPositiveBulkWard SourceScalarVirialBulk SourceScalarGaugeScale
open SourceMixedNativeReturn SourceJointScaleBudget SourceRetardedIncrement SourceMinimalGraphParticular
open SourceInverseCompressionCurrent SourceScalarDoubleCurrent SourceScalarGaugeForce SourceGaugeCoframeWard
open SourceGaugeCoframeJets FullYSourceResolventGraphSplice SourceInverseFirstCurrentGaugeJets
open SourceInverseFirstCurrentRemainder SourceInverseProjectionCurrentRemainder
open SourceInverseGaugeSingleDefectJoin SourceInverseCompressionGaugeBudget SourceInverseCompressionGaugeSplice
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge SourceGaugeRadialCurrent SourceGaugeRadialPair SourceDilationRemainder
open Filter MeasureTheory SourceResolventBandLimit
open scoped ContDiff InnerProductSpace
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev Op := H →L[ℂ] H
attribute [local irreducible] diagonalAction scalarKinetic gaugeKinetic GaussCoframeForm.coframeAction matterAction
  sourceRead state sourcePair defectAction compressionCore deltaGauge
  SourceScalarDoubleCurrent.fullInsertion SourceMixedNativeReturn.fullAction SourceMixedNativeReturn.thetaAction
  firstHamiltonianCurrent matterInsertion matterHamiltonianCurrent hamiltonianGaugeForce
  readOrbitJet sandwichJet inverseCross inputFlux resolventJet
  scalarSpatialAction magneticAction cutoffEuler scaleDoubleRemainder constantAction
  SourceScalarForceBudget.solverOperator SourceScalarForceBudget.oscillatorMass wardOperator

private def massAction : End := multiply potential potential_smooth-scalarSpatialAction-magneticAction

private theorem mass_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    massAction f z=(sourceTime 0*volume z*inner ℝ (z.2.1 : Scalar) (z.2.1 : Scalar) : ℂ) • f z := by
  unfold massAction scalarSpatialAction magneticAction
  change (potential z : ℂ) • f z-
      ((-(sourceTime 0*volume z/2*∑ i : Fin 3,∑ j : Fin 3,inverseSpatial z i j*
        inner ℝ (scalarGradient z i) (scalarGradient z j)) : ℝ) : ℂ) • f z-
      (magneticPotential z : ℂ) • f z=_
  unfold potential scalarPotential
  push_cast
  module

private theorem invariant_derivative {E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : V →L[ℝ] V) (f h : E → V) (γ : ℝ → E) (z e : E)
    (hg : HasDerivAt γ e 1) (hz : γ 1=z)
    (hf : DifferentiableAt ℝ f z) (hh : DifferentiableAt ℝ h z)
    (law : ∀ r,h (γ r)=A (f (γ r))) :
    fderiv ℝ h z e=A (fderiv ℝ f z e) := by
  have hf0 := hf.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hh0 := hh.hasFDerivAt.comp_hasDerivAt_of_eq 1 hg hz.symm
  have hp := A.hasFDerivAt.comp_hasDerivAt 1 hf0
  have he : h ∘ γ=A ∘ (f ∘ γ) := funext law
  rw [he] at hh0
  exact hh0.unique hp

private theorem mass_gauge : deltaGauge massAction=0 := by
  unfold deltaGauge
  apply sub_eq_zero.mpr
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change gaugeEulerAction (massAction f) z=massAction (gaugeEulerAction f) z
  rw [gauge_euler_apply,mass_apply,gauge_euler_apply]
  let c : ℂ := (sourceTime 0*volume z*inner ℝ (z.2.1 : Scalar) (z.2.1 : Scalar) : ℂ)
  have h := invariant_derivative (E := SourceCoordinateSlice) (V := FockFiber)
    ((c • ContinuousLinearMap.id ℂ FockFiber).restrictScalars ℝ) f (massAction f)
    (fun r => gaugeScale r z) z (gaugeEuler z) (gauge_scale_derivative z 1) (gauge_scale_one z)
    ((f.contDiff.differentiable (by simp)) z) (((massAction f).contDiff.differentiable (by simp)) z)
    (fun r => by rw [mass_apply]; rfl)
  simpa only [ContinuousLinearMap.coe_restrictScalars',smul_apply,ContinuousLinearMap.id_apply] using! h

/-- The complete original H-gauge derivative retains the true signed spatial and magnetic forces. -/
theorem original_hamiltonian_gauge_source :
    deltaGauge diagonalAction=(-2 : ℂ) • gaugeKinetic+matterAction+
      (2 : ℂ) • scalarSpatialAction+(4 : ℂ) • magneticAction := by
  have hp : multiply potential potential_smooth=massAction+scalarSpatialAction+magneticAction := by
    unfold massAction
    abel
  rw [diagonalAction,nativeAction,hp]
  simp only [map_add,original_scalar_kinetic_gauge,original_gauge_kinetic_gauge,mass_gauge,
    original_signed_spatial_gauge,original_magnetic_gauge,original_coframe_gauge,original_matter_gauge]
  module

private theorem gauge_product (A B : End) : deltaGauge (A*B)=deltaGauge A*B+A*deltaGauge B := by
  unfold deltaGauge
  change gaugeEulerAction*(A*B)-(A*B)*gaugeEulerAction=
    (gaugeEulerAction*A-A*gaugeEulerAction)*B+A*(gaugeEulerAction*B-B*gaugeEulerAction)
  noncomm_ring
private theorem gauge_bracket (A B : End) :
    deltaGauge (bracket A B)=bracket (deltaGauge A) B+bracket A (deltaGauge B) := by
  simp only [bracket,map_sub,gauge_product]
  noncomm_ring

private theorem real_local (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (A : SourceCoordinateSlice → FockFiber →L[ℂ] FockFiber)
    (hA : ∀ z : physicalChart,ContDiffAt ℝ ∞ A z.val) :
    Commute (multiply c hc) (localMultiplier A hA) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (A z) (c z : ℂ) (f z)).symm

private theorem real_matter (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute (multiply c hc) matterAction := by
  unfold matterAction
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro b _
  exact real_local _ _ _ _

private theorem real_full (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) :
    Commute (multiply c hc) (SourceMixedNativeReturn.fullAction sharp) := by
  unfold SourceMixedNativeReturn.fullAction
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  cases sharp
  · exact (map_smul (GaussYukawaCoefficient.sourceMap (scalarField z)) (c z : ℂ) (f z)).symm
  · exact (map_smul (GaussFullHamiltonian.adjointMap (scalarField z)) (c z : ℂ) (f z)).symm

private theorem real_theta (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (m ell : ℕ) :
    Commute (multiply c hc) (SourceMixedNativeReturn.thetaAction m ell) := by
  unfold SourceMixedNativeReturn.thetaAction
  change Commute (multiply c hc) ((1-GaussRadialDomain.inverseAction)^(m+1)-(1-GaussRadialDomain.inverseAction)^(ell+1))
  rw [←SourceNativeCutoffContact.theta_action_polynomial]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (SourceNativeCutoffContact.theta m ell z : ℂ) (f z)

private theorem real_matter_insertion (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (sharp : Bool) (m ell : ℕ) :
    Commute (multiply c hc) (matterInsertion sharp m ell) := by
  have hi : Commute (multiply c hc) (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
    unfold SourceScalarDoubleCurrent.fullInsertion
    exact (real_full c hc sharp).mul_right (real_theta c hc m ell)
  unfold matterInsertion bracket
  exact ((real_matter c hc).mul_right hi).sub_right (hi.mul_right (real_matter c hc))

/-- The gauge-neutral first H-current remains the full source B−W; no kinetic cross is set to zero. -/
def neutralCurrent (sharp : Bool) (m ell : ℕ) : End :=
  firstHamiltonianCurrent sharp m ell-matterInsertion sharp m ell

def kineticMagneticForce (sharp : Bool) (m ell : ℕ) : End :=
  bracket (magneticAction-gaugeKinetic) (neutralCurrent sharp m ell)

private theorem matter_gauge (sharp : Bool) (m ell : ℕ) :
    deltaGauge (matterInsertion sharp m ell)=matterInsertion sharp m ell := by
  rw [matterInsertion,gauge_bracket,original_matter_gauge,original_insertion_gauge_scale]
  simp only [bracket,mul_zero,zero_mul,sub_self,add_zero]

private theorem neutral_gauge (sharp : Bool) (m ell : ℕ) : deltaGauge (neutralCurrent sharp m ell)=0 := by
  rw [neutralCurrent,map_sub,original_first_current_gauge,matter_gauge,sub_self]

private def forceFilter : End →ₗ[ℂ] End := deltaGauge.comp deltaGauge-(3 : ℂ) • deltaGauge+(2 : ℂ) • LinearMap.id

private theorem bracket_weight (A B : End) (a b : ℂ)
    (ha : deltaGauge A=a • A) (hb : deltaGauge B=b • B) :
    deltaGauge (bracket A B)=(a+b) • bracket A B := by
  rw [gauge_bracket,ha,hb]
  simp only [bracket,smul_mul_assoc,mul_smul_comm]
  module

private theorem filtered_weight (A : End) (a : ℂ) (ha : deltaGauge A=a • A) :
    forceFilter A=(a^2-3*a+2) • A := by
  simp only [forceFilter,LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,
    LinearMap.comp_apply,LinearMap.id_apply,ha,map_smul,smul_smul]
  module

private theorem electric_current (sharp : Bool) (m ell : ℕ) :
    electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)=
      bracket gaugeKinetic (matterInsertion sharp m ell) := by
  have hs : Commute spatialAction (matterInsertion sharp m ell) := real_matter_insertion _ _ sharp m ell
  rw [original_electric_matter_current,←matterInsertion,electricSpatial]
  unfold bracket
  linear_combination (norm := noncomm_ring) hs.eq

/-- Three genuine matter/spatial blocks vanish in the original filter, leaving only the magnetic/kinetic source cross and E. -/
theorem original_filtered_hamiltonian_force (sharp : Bool) (m ell : ℕ) :
    deltaGauge (deltaGauge (hamiltonianGaugeForce sharp m ell))-
      (3 : ℂ) • deltaGauge (hamiltonianGaugeForce sharp m ell)+(2 : ℂ) • hamiltonianGaugeForce sharp m ell=
      (24 : ℂ) • kineticMagneticForce sharp m ell-
        (12 : ℂ) • electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell) := by
  let Q := neutralCurrent sharp m ell
  let W := matterInsertion sharp m ell
  have hQ : deltaGauge Q=(0 : ℂ) • Q := by simp only [Q,neutral_gauge,zero_smul]
  have hW : deltaGauge W=(1 : ℂ) • W := by simp only [W,matter_gauge,one_smul]
  have hB : firstHamiltonianCurrent sharp m ell=Q+W := by dsimp only [Q,W,neutralCurrent]; abel
  have hS : Commute scalarSpatialAction W := by unfold scalarSpatialAction; exact real_matter_insertion _ _ sharp m ell
  have hM : Commute magneticAction W := by unfold magneticAction; exact real_matter_insertion _ _ sharp m ell
  have hs : hamiltonianGaugeForce sharp m ell=
      (-2 : ℂ) • bracket gaugeKinetic Q+(-2 : ℂ) • bracket gaugeKinetic W+
      bracket matterAction Q+bracket matterAction W+(2 : ℂ) • bracket scalarSpatialAction Q+
      (4 : ℂ) • bracket magneticAction Q := by
    rw [hamiltonianGaugeForce,original_hamiltonian_gauge_source,hB]
    unfold bracket
    simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm]
    linear_combination (norm := module) (2 : ℂ) • hS.eq+(4 : ℂ) • hM.eq
  have hKQ := filtered_weight _ (-2) (by simpa only [add_zero] using
    (bracket_weight gaugeKinetic Q (-2) 0 original_gauge_kinetic_gauge hQ))
  have hKW := filtered_weight (bracket gaugeKinetic W) (-1) (by
    convert bracket_weight gaugeKinetic W (-2) 1 original_gauge_kinetic_gauge hW using 1
    norm_num)
  have hMQ := filtered_weight _ 1 (by simpa only [add_zero] using
    (bracket_weight matterAction Q 1 0 (by simpa using original_matter_gauge) hQ))
  have hMW := filtered_weight (bracket matterAction W) 2 (by
    convert bracket_weight matterAction W 1 1 (by simpa using original_matter_gauge) hW using 1
    norm_num)
  have hSQ := filtered_weight _ 2 (by simpa only [add_zero] using
    (bracket_weight scalarSpatialAction Q 2 0 original_signed_spatial_gauge hQ))
  have hVQ := filtered_weight _ 4 (by simpa only [add_zero] using
    (bracket_weight magneticAction Q 4 0 original_magnetic_gauge hQ))
  change forceFilter (hamiltonianGaugeForce sharp m ell)=_
  rw [hs]
  simp only [map_add,map_smul,hKQ,hKW,hMQ,hMW,hSQ,hVQ]
  rw [electric_current]
  simp only [kineticMagneticForce,bracket,sub_mul,mul_sub,Q,W]
  module

private theorem inverse_cross (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) (n : ℕ) (hn : n≤2) :
    inverseCross F g z A 0 n=sandwichJet F g z A 0 n 0 0-
      finiteResolvent F z*readOrbitJet F g A 0 n 0 0*finiteResolvent F z := by
  interval_cases n <;> simp only [inverseCross,resolved_inverse_return F z hz,sandwichJet] <;> rfl

private theorem read_filter (F : Index) (g : diagonal.domain) (A : End) :
    sourceRead F g (deltaGauge (deltaGauge A)-(3 : ℂ) • deltaGauge A+(2 : ℂ) • A)=
      gaugeFilter (fun n => readOrbitJet F g A 0 n 0 0)-gaugeFilter (fun n => inputFlux F g A 0 n) := by
  simp only [gaugeFilter,inputFlux,coreJet,pow_zero,pow_succ,Module.End.one_apply,
    Module.End.mul_apply,map_add,map_sub,map_smul]
  module

private theorem filtered_split {V : Type*} [AddCommGroup V] [Module ℂ V]
    {S0 S1 S2 R0 R1 R2 I0 I1 I2 T Z : V}
    (h0 : I0=S0-R0) (h1 : I1=S1-R1) (h2 : I2=S2-R2)
    (hT : T=R2-(3 : ℂ) • R1+(2 : ℂ) • R0-Z) :
    S2-(3 : ℂ) • S1+(2 : ℂ) • S0=T+(I2-(3 : ℂ) • I1+(2 : ℂ) • I0)+Z := by
  rw [h0,h1,h2,hT]
  module

private theorem sandwich_filter (F : Index) (g : diagonal.domain) (z : ℂ) (hz : z.im≠0) (A : End) :
    gaugeFilter (fun n => sandwichJet F g z A 0 n 0 0)=
      finiteResolvent F z*sourceRead F g
        (deltaGauge (deltaGauge A)-(3 : ℂ) • deltaGauge A+(2 : ℂ) • A)*finiteResolvent F z+
      gaugeFilter (fun n => inverseCross F g z A 0 n)+
      finiteResolvent F z*gaugeFilter (fun n => inputFlux F g A 0 n)*finiteResolvent F z := by
  have h0 := inverse_cross F g z hz A 0 (by omega)
  have h1 := inverse_cross F g z hz A 1 (by omega)
  have h2 := inverse_cross F g z hz A 2 (by omega)
  have hr := congrArg (fun B : Op => finiteResolvent F z*B*finiteResolvent F z) (read_filter F g A)
  simp only [gaugeFilter,mul_sub,sub_mul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc] at hr ⊢
  exact filtered_split h0 h1 h2 hr

attribute [local irreducible] neutralCurrent kineticMagneticForce hamiltonianGaugeJet

/-- Actual two-leg response of the reduced H-force, with every inverse and input correction retained. -/
theorem actual_hamiltonian_force_response (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) :
    gaugeFilter (fun n => hamiltonianGaugeJet sharp m ell F g z n 0)=
      (24 : ℂ) • (finiteResolvent F z*sourceRead F g (kineticMagneticForce sharp m ell)*finiteResolvent F z)-
      (12 : ℂ) • (finiteResolvent F z*sourceRead F g
        (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell))*finiteResolvent F z)+
      gaugeFilter (fun n => inverseCross F g z (hamiltonianGaugeForce sharp m ell) 0 n)+
      finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (hamiltonianGaugeForce sharp m ell) 0 n)*
        finiteResolvent F z := by
  have hr := sandwich_filter F g z hz (hamiltonianGaugeForce sharp m ell)
  have hs := congrArg (sourceRead F g) (original_filtered_hamiltonian_force sharp m ell)
  simp only [map_sub,map_smul] at hs
  have hsr := congrArg (fun A : Op => finiteResolvent F z*A*finiteResolvent F z) hs
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc] at hsr
  unfold hamiltonianGaugeJet
  exact hr.trans (congrArg (fun A : Op => A+
    gaugeFilter (fun n => inverseCross F g z (hamiltonianGaugeForce sharp m ell) 0 n)+
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (hamiltonianGaugeForce sharp m ell) 0 n)*
      finiteResolvent F z) hsr)

/-- Literal reduced source word after matter/spatial H-force cancellation. The kinetic/magnetic cross remains explicit. -/
def nativeForceRemainder (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain) (z : ℂ) : Op :=
  (1/6 : ℂ) • (joinedPolynomial (fun n => singleResponseJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => hamiltonianCorrectionJet sharp m ell F g z n 0)-
    gaugeFilter (fun n => inverseCross F g z (hamiltonianGaugeForce sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (hamiltonianGaugeForce sharp m ell) 0 n)*finiteResolvent F z-
    gaugeFilter (fun n => inverseCross F g z (matterHamiltonianCurrent sharp m ell) 0 n)-
    finiteResolvent F z*gaugeFilter (fun n => inputFlux F g (matterHamiltonianCurrent sharp m ell) 0 n)*finiteResolvent F z)+
  finiteResolvent F z*(sourceRead F g
    (-(2*(sourceTime 0 : ℂ)^2) • (SourceMixedNativeReturn.fullAction sharp*cutoffEuler m ell)+
      (2*(sourceTime 0 : ℂ)^2) • (constantAction sharp vacuum*SourceMixedNativeReturn.thetaAction m ell)-
      (1/48 : ℂ) • scaleDoubleRemainder sharp m ell)-
    (SourceScalarForceBudget.oscillatorMass : ℂ) • SourceScalarForceBudget.solverOperator sharp m ell F-
    (4 : ℂ) • sourceRead F g (kineticMagneticForce sharp m ell)+
    (2 : ℂ) • sourceRead F g (electricMatterCurrent (SourceScalarDoubleCurrent.fullInsertion sharp m ell)))*finiteResolvent F z

/-- The actual reduced remainder consumes the physical H-force cancellation before taking any norms. -/
theorem actual_reduced_native_force (sharp : Bool) (m ell : ℕ) (F : Index) (g : diagonal.domain)
    (z : ℂ) (hz : z.im≠0) : reducedGaugeRemainder sharp m ell F g z=nativeForceRemainder sharp m ell F g z := by
  have hf := actual_hamiltonian_force_response sharp m ell F g z hz
  simp only [reducedGaugeRemainder,nativeForceRemainder,mul_sub,sub_mul,mul_add,add_mul,mul_smul_comm,smul_mul_assoc]
  linear_combination (norm := module) -(1/6 : ℂ) • hf

/-- The original whole Ward keeps its generated common tail when the reduced physical H-force word is installed. -/
theorem actual_ward_native_force_difference_tail (sharp : Bool) (μ : ℝ) (hμ : 0<μ) (f k : QuantumTest) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m, N ≤ m → ∀ ell, m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        (∫⁻ w : ℝ,ENNReal.ofReal (‖inner ℂ (embed k)
          (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
          inner ℂ (embed k) (nativeForceRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))‖^2))≤ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N,hN⟩ := actual_ward_reduced_difference_tail sharp μ hμ f k ε hε
  refine ⟨N,fun m hm ell hell => ?_⟩
  filter_upwards [hN m hm ell hell] with F hF
  have he (w : ℝ) := congrArg (fun A : Op => inner ℂ (embed k) (A (embed f)))
    (actual_reduced_native_force sharp m ell F (coreEquiv f) (line μ w) (by simpa only [line_im] using hμ.ne'))
  have hfun : (fun w : ℝ => ENNReal.ofReal (‖inner ℂ (embed k)
      (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
      inner ℂ (embed k) (nativeForceRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))‖^2))=
    (fun w : ℝ => ENNReal.ofReal (‖inner ℂ (embed k)
      (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-
      inner ℂ (embed k) (reducedGaugeRemainder sharp m ell F (coreEquiv f) (line μ w) (embed f))‖^2)) := by
    funext w
    exact congrArg (fun c : ℂ => ENNReal.ofReal (‖inner ℂ (embed k)
      (wardOperator sharp m ell F (coreEquiv f) (line μ w) (embed f))-c‖^2)) (he w).symm
  rw [hfun]
  exact hF

end LowEnergy.SourceInverseHamiltonianForceReduction
