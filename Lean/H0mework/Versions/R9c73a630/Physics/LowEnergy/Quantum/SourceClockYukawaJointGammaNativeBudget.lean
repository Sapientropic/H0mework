import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaJointDualFieldBudget
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceClockYukawaSpinNativeJet

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.SourceClockYukawaJointGammaNativeBudget
open GaussQuantumMultiplier SourceClockYukawaRadialJoinedHessian SourceClockReflectedForm
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open GaussNativePotential GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussRadialDomain GaussYukawaCoefficient
open GaussScalarTransport GaussDensityCore SourceNativeMomentumCurvature SourceNativeDensityTrace SourceNativeCoframeCompatibility
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceMixedNativeReturn SourceScalarDoubleCurrent SourceScalarPairedTransport SourcePhysicalKineticSquare
open SourceClockYukawaRadialNativeDivergence SourceClockYukawaRadialNativeHessian SourceClockYukawaRadialMixedCore
open SourceCoframeVolume SourceHamiltonianVolume SourceLocalizedInverseFormPayment SourceCutoffDilationWard
open PositiveScalarWeakBudget PositiveScalarCoefficientDecay SourceYukawaCoefficientCommutator SourceScalarGaugeForce
open scoped ContDiff InnerProductSpace BigOperators Topology
abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
abbrev FiberEnd := FockFiber →L[ℂ] FockFiber
private abbrev W : End := multiply scalarWeight scalarWeight_smooth
private abbrev M (sharp : Bool) (a : ScalarIndex) : End := constantAction sharp (scalarBasis a)
private abbrev P (a : ScalarIndex) : End := covariantMomentum (scalarDirection a)
private abbrev Pa (a : ScalarIndex) : End := GaussMomentumAdjoint.adjoint (scalarDirection a)
attribute [local irreducible] fullAction compressionCore defectAction

abbrev Op := H →L[ℂ] H
open SourceClockYukawaSpinClosure SourceClockYukawaSpinNativeJet SourceClockYukawaSpinNativeBudget
open SourceClockYukawaJointRadialZero SourceClockYukawaGammaPrincipalForm SourceClockYukawaJointDualFieldBudget
open SourceClockYukawaSpinJointForce SourceClockYukawaSpinNativeAbsorption SourceInverseNeutralSpinCurrent
open SourceScalarPositiveBulkWard SourceClockYukawaCubicCurrent SourceClockYukawaRadialCoefficient
open SourceRelativePowerTail SourceHardyRetardedTail SourceRetardedForcingTail SourceClockYukawaRadialMixedBudget
open SourceEscapeSeedTail FullYSourceResolventGraphSplice SourceResolventBandLimit SourceFourPoleEnergyClosed MeasureTheory Filter
attribute [local irreducible] jointState windowState errorColumn scalarColumn constantBounded

private def constantFiber (sharp : Bool) (a : ScalarIndex) (z : SourceCoordinateSlice) : FiberEnd :=
  connection (scalarDirection a) z*branchMap sharp (scalarBasis a)-branchMap sharp (scalarBasis a)*connection (scalarDirection a) z
private theorem constant_smooth (sharp : Bool) (a : ScalarIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (constantFiber sharp a) z.val :=
  ((connection_smooth (scalarDirection a) z).mul contDiffAt_const).sub
    (contDiffAt_const.mul (connection_smooth (scalarDirection a) z))

private theorem density_smooth (N : ℕ) (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (SourceNativeMomentumCurvature.divergenceCoefficient N v) z.val := by
  apply ContDiffAt.sum
  intro i _
  exact (inverseDensity_smooth N z).mul
    ((((complexDensity_smooth N z).mul (coefficient_smooth v i z)).fderiv_right (by simp)).clm_apply contDiffAt_const)
private theorem correction_smooth (v : Ambient) (z : physicalChart) :
    ContDiffAt ℝ ∞ (nativeDensityCorrection v) z.val := by
  have he : nativeDensityCorrection v=ᶠ[nhds z.val] (fun x => (SourceNativeMomentumCurvature.divergenceCoefficient 0 v x).re) := by
    filter_upwards [physicalChart.isOpen.mem_nhds z.property] with x hx
    have h := congrArg Complex.re (original_density_gamma_return 0 v ⟨x,hx⟩)
    simpa only [Complex.ofReal_re,nativeDensityCorrection,intrinsicDensity] using h.symm
  exact (Complex.reCLM.contDiff.contDiffAt.comp z.val (density_smooth 0 v z)).congr_of_eventuallyEq he

private def densityFiber (sharp : Bool) (a : ScalarIndex) (z : SourceCoordinateSlice) : FiberEnd :=
  constantFiber sharp a z+(nativeDensityCorrection (scalarDirection a) z:ℂ) • branchMap sharp (scalarBasis a)
private theorem density_fiber_smooth (sharp : Bool) (a : ScalarIndex) (z : physicalChart) :
    ContDiffAt ℝ ∞ (densityFiber sharp a) z.val :=
  (constant_smooth sharp a z).add
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (correction_smooth (scalarDirection a) z)).smul contDiffAt_const)


private theorem native_weight (v : Ambient) : Commute (covariantMomentum v) (multiply scalarWeight scalarWeight_smooth) := by
  have hvu : (volumeAction:End)*inverseVolumeAction=1 := by apply LinearMap.ext;intro f;exact volume_inverse f
  have huv : inverseVolumeAction*(volumeAction:End)=1 := by
    have hc : Commute inverseVolumeAction (volumeAction:End) := by
      apply LinearMap.ext
      intro f
      apply DFunLike.ext
      intro z
      exact smul_comm (reciprocalVolume z:ℂ) (volume z:ℂ) (f z)
    rw [hc.eq]
    exact hvu
  have hP := (native_momentum_volume v).eq
  have hu : Commute (covariantMomentum v) inverseVolumeAction := by
    calc
      _=inverseVolumeAction*(volumeAction*covariantMomentum v)*inverseVolumeAction := by rw [←mul_assoc inverseVolumeAction volumeAction,huv,one_mul]
      _=inverseVolumeAction*(covariantMomentum v*volumeAction)*inverseVolumeAction := by rw [hP.symm]
      _=_ := by rw [mul_assoc,mul_assoc,hvu,mul_one]
  have hw : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    apply PiLp.ext
    intro word
    change (scalarWeight z:ℂ)*f z word=(-(sourceTime 0:ℂ))*((reciprocalVolume z:ℂ)*f z word)
    unfold scalarWeight reciprocalVolume
    push_cast
    ring
  rw [hw]
  exact hu.smul_right _

private theorem row_algebra (P D W A : End) (hp : Commute P W) (hw : Commute W A) :
    A*W*P-(P-Complex.I • D)*W*A=
      -W*bracket P A+Complex.I • (D*W*A) := by
  have h1 := congrArg (fun B : End => B*P) hw.eq
  have h2 := congrArg (fun B : End => B*A) hp.eq
  simp only [bracket,sub_mul,smul_mul_assoc,mul_sub,neg_mul,mul_assoc] at *
  linear_combination (norm := module) -h1-h2


private theorem constant_directional (sharp : Bool) (a : ScalarIndex) (f : QuantumTest) (z : SourceCoordinateSlice) :
    directional (scalarDirection a) (M sharp a f) z=branchMap sharp (scalarBasis a) (directional (scalarDirection a) f z) := by
  have h := ((branchMap sharp (scalarBasis a)).restrictScalars ℝ).hasFDerivAt.comp z
    (f.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  rw [directional_apply,directional_apply]
  change fderiv ℝ (((branchMap sharp (scalarBasis a)).restrictScalars ℝ) ∘ f) z (direction (scalarDirection a) z)=_
  rw [h.fderiv]
  rfl

private theorem native_constant (sharp : Bool) (a : ScalarIndex) :
    bracket (P a) (M sharp a)=(-Complex.I) • localMultiplier (constantFiber sharp a) (constant_smooth sharp a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change (-Complex.I) • (directional (scalarDirection a) (M sharp a f) z+
    connection (scalarDirection a) z (branchMap sharp (scalarBasis a) (f z)))-
    branchMap sharp (scalarBasis a) ((-Complex.I) •
      (directional (scalarDirection a) f z+connection (scalarDirection a) z (f z)))=
      (-Complex.I) • constantFiber sharp a z (f z)
  rw [constant_directional]
  simp only [constantFiber,sub_apply,mul_apply_eq_comp,map_smul,map_add]
  module

private def constantDivergence (sharp : Bool) (a : ScalarIndex) : End := M sharp a*W*P a-Pa a*W*M sharp a

private theorem constant_divergence_source (sharp : Bool) (a : ScalarIndex) :
    constantDivergence sharp a=Complex.I •
      (W*localMultiplier (densityFiber sharp a) (density_fiber_smooth sharp a)) := by
  have hw : Commute W (M sharp a) := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    exact (map_smul (branchMap sharp (scalarBasis a)) (scalarWeight z:ℂ) (f z)).symm
  rw [constantDivergence,Pa,original_adjoint_divergence,row_algebra _ _ _ _ (native_weight _) hw,native_constant,
    original_native_density_multiplier]
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  simp only [LinearMap.add_apply,LinearMap.neg_apply,Module.End.mul_apply,LinearMap.smul_apply]
  change -((scalarWeight z:ℂ) • ((-Complex.I) • constantFiber sharp a z (f z)))+
    Complex.I • ((nativeDensityCorrection (scalarDirection a) z:ℂ) • ((scalarWeight z:ℂ) • branchMap sharp (scalarBasis a) (f z)))=
      Complex.I • ((scalarWeight z:ℂ) • densityFiber sharp a z (f z))
  simp only [densityFiber,add_apply,smul_apply,smul_smul]
  module

private theorem constant_density_sum (sharp : Bool) :
    (∑ a : ScalarIndex,constantDivergence sharp a)=(-Complex.I) • (W*gammaAction sharp) := by
  have hg : (∑ a : ScalarIndex,localMultiplier (densityFiber sharp a) (density_fiber_smooth sharp a))=-gammaAction sharp := by
    apply LinearMap.ext
    intro f
    apply DFunLike.ext
    intro z
    let ev : QuantumTest →ₗ[ℂ] FockFiber :=
      { toFun := fun q => q z
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    change ev ((∑ a : ScalarIndex,localMultiplier (densityFiber sharp a) (density_fiber_smooth sharp a)) f)=_
    simp only [LinearMap.sum_apply,map_sum]
    change (∑ a : ScalarIndex,densityFiber sharp a z (f z))=-(branchMap sharp (gammaGradient z) (f z))
    have h := congrArg (fun A : FiberEnd => A (f z)) (original_constant_density_hessian sharp z)
    simpa only [densityFiber,constantFiber,sum_apply,neg_apply] using h
  simp_rw [constant_divergence_source]
  rw [←Finset.smul_sum,←Finset.mul_sum,hg,mul_neg,smul_neg,neg_smul]

private def ad (J : End) : End →ₗ[ℂ] End where
  toFun A := bracket J A
  map_add' A B := by unfold bracket;noncomm_ring
  map_smul' c A := by simp only [bracket,mul_smul_comm,smul_mul_assoc,smul_sub,RingHom.id_apply]

private def recipe (mu : Fin 8) : End →ₗ[ℂ] End :=
  if h0 : mu.val=0 then LinearMap.id else
  if h1 : mu.val<5 then ad (activeSpin ⟨mu.val-1,by omega⟩) else
    (ad (activeSpin ⟨mu.val-5,by omega⟩)).comp (ad (activeSpin 3))

private theorem ad_bimodule (J L A R : End) (hL : Commute J L) (hR : Commute J R) :
    bracket J (L*A*R)=L*bracket J A*R := by
  unfold bracket
  linear_combination (norm := noncomm_ring) hL.eq*A*R+L*A*hR.eq

private theorem recipe_bimodule (mu : Fin 8) (L A R : End)
    (hL : ∀ j : Fin 4,Commute (activeSpin j) L)
    (hR : ∀ j : Fin 4,Commute (activeSpin j) R) :
    recipe mu (L*A*R)=L*recipe mu A*R := by
  unfold recipe
  split_ifs with h0 h1
  · rfl
  · exact ad_bimodule _ _ _ _ (hL _) (hR _)
  · change bracket _ (bracket _ (L*A*R))=L*bracket _ (bracket _ A)*R
    rw [ad_bimodule _ _ _ _ (hL 3) (hR 3),ad_bimodule _ _ _ _ (hL _) (hR _)]

private theorem recipe_left (mu : Fin 8) (L A : End) (hL : ∀ j : Fin 4,Commute (activeSpin j) L) :
    recipe mu (L*A)=L*recipe mu A := by
  simpa only [mul_one] using recipe_bimodule mu L A 1 hL (fun _ => Commute.one_right _)
private theorem recipe_right (mu : Fin 8) (A R : End) (hR : ∀ j : Fin 4,Commute (activeSpin j) R) :
    recipe mu (A*R)=recipe mu A*R := by
  simpa only [one_mul] using recipe_bimodule mu 1 A R (fun _ => Commute.one_right _) hR
private theorem spin_weight (j : Fin 4) : Commute (activeSpin j) W := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussCoframeSpin.full (activeIndex j))) (scalarWeight z:ℂ) (f z)
private theorem spin_P (j : Fin 4) (a : ScalarIndex) : Commute (activeSpin j) (P a) :=
  original_spin_native_commute (activeIndex j) (scalarDirection a)
private theorem spin_Pa (j : Fin 4) (a : ScalarIndex) : Commute (activeSpin j) (Pa a) :=
  original_spin_adjoint_native_commute (activeIndex j) (scalarDirection a)
private def M8 (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) : End := constantCoefficient sharp mu (scalarBasis a)
private theorem recipe_M (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) : recipe mu (M sharp a)=M8 sharp mu a := by
  unfold recipe M8 constantCoefficient
  split_ifs <;> rfl
private theorem recipe_gamma (sharp : Bool) (mu : Fin 8) : recipe mu (gammaAction sharp)=gammaCore sharp mu := rfl
private theorem M8_native_source (sharp : Bool) (mu : Fin 8) :
    (∑ a : ScalarIndex,(M8 sharp mu a*W*P a-Pa a*W*M8 sharp mu a))=
      (-Complex.I) • (W*gammaCore sharp mu) := by
  have h := congrArg (recipe mu) (constant_density_sum sharp)
  have hm (a : ScalarIndex) : recipe mu (constantDivergence sharp a)=
      M8 sharp mu a*W*P a-Pa a*W*M8 sharp mu a := by
    unfold constantDivergence
    rw [map_sub,show M sharp a*W*P a=M sharp a*(W*P a) by noncomm_ring,
      recipe_right mu _ _ (fun j => (spin_weight j).mul_right (spin_P j a)),
      recipe_left mu _ _ (fun j => (spin_Pa j a).mul_right (spin_weight j)),recipe_M]
    noncomm_ring
  simp only [map_sum,hm,map_smul,recipe_left mu W _ spin_weight,recipe_gamma] at h
  exact h

private def parity (mu : Fin 8) : ℂ := if 0 < mu.val ∧ mu.val < 5 then -1 else 1
def constantDagger (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) : End := parity mu • M8 (!sharp) mu a

private theorem constant_pair (sharp : Bool) (a : ScalarIndex) :
    GaussCoframeForm.Paired (M sharp a) (M (!sharp) a) := by
  intro p q
  have hadj : (constantBounded sharp (scalarBasis a)).adjoint=constantBounded (!sharp) (scalarBasis a) := by
    unfold constantBounded
    cases sharp <;> simp
  change inner ℂ (embed p) (embed (M sharp a q))=inner ℂ (embed (M (!sharp) a p)) (embed q)
  rw [←constant_bounded_core sharp,←constant_bounded_core (!sharp)]
  rw [←hadj,ContinuousLinearMap.adjoint_inner_left]

private theorem bracket_pair (J A B : End) (hJ : GaussCoframeForm.Paired J J)
    (hAB : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired (bracket J A) (-bracket J B) := by
  intro p q
  have h1 := hJ p (A q)
  have h2 := hAB (J p) q
  have h3 := hAB p (J q)
  have h4 := hJ (B p) q
  simp only [bracket,LinearMap.sub_apply,LinearMap.neg_apply,Module.End.mul_apply,
    sourcePair,map_sub,map_neg,inner_sub_right,inner_sub_left,inner_neg_left] at *
  linear_combination h1+h2-h3-h4

private theorem paired_symm {A B : End} (h : GaussCoframeForm.Paired A B) : GaussCoframeForm.Paired B A := by
  intro p q
  have h' := congrArg (starRingEnd ℂ) (h q p)
  simpa only [sourcePair,inner_conj_symm] using h'.symm

private theorem active_pair (j : Fin 4) : GaussCoframeForm.Paired (activeSpin j) (activeSpin j) :=
  GaussCoframeSpin.current_pair (activeIndex j)

private theorem double_pair (j : Fin 4) (A B : End) (hAB : GaussCoframeForm.Paired A B) :
    GaussCoframeForm.Paired (bracket (activeSpin j) (bracket (activeSpin 3) A))
      (bracket (activeSpin j) (bracket (activeSpin 3) B)) := by
  have h1 := bracket_pair (activeSpin 3) A B (active_pair 3) hAB
  have h2 := bracket_pair (activeSpin j) (bracket (activeSpin 3) A)
    (-bracket (activeSpin 3) B) (active_pair j) h1
  have he : -bracket (activeSpin j) (-bracket (activeSpin 3) B)=
      bracket (activeSpin j) (bracket (activeSpin 3) B) := by unfold bracket;noncomm_ring
  rw [he] at h2
  exact h2

private theorem M8_pair (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) :
    GaussCoframeForm.Paired (M8 sharp mu a) (constantDagger sharp mu a) := by
  unfold constantDagger M8 constantCoefficient
  by_cases h0 : mu.val=0
  · have hs : parity mu=1 := by simp [parity,h0]
    simpa [h0,hs] using constant_pair sharp a
  · by_cases h1 : mu.val<5
    · have hp : 0 < mu.val := Nat.pos_of_ne_zero h0
      have hs : parity mu=-1 := by simp [parity,hp,h1]
      simpa [h0,h1,hs] using bracket_pair (activeSpin ⟨mu.val-1,by omega⟩)
        (M sharp a) (M (!sharp) a) (active_pair _) (constant_pair sharp a)
    · have hs : parity mu=1 := by unfold parity;rw [if_neg (by omega)]
      simpa [h0,h1,hs] using double_pair ⟨mu.val-5,by omega⟩ (M sharp a) (M (!sharp) a) (constant_pair sharp a)

private theorem recipe_bracket (mu : Fin 8) (P A : End) (hP : ∀ j : Fin 4,Commute (activeSpin j) P) :
    bracket P (recipe mu A)=recipe mu (bracket P A) := by
  simp only [bracket,map_sub,recipe_left mu P A hP,recipe_right mu A P hP]

private theorem recipe_commute (mu : Fin 8) (A B : End)
    (hB : ∀ j : Fin 4,Commute (activeSpin j) B) (hA : Commute B A) : Commute B (recipe mu A) := by
  apply sub_eq_zero.mp
  change bracket B (recipe mu A)=0
  rw [recipe_bracket mu B A hB,show bracket B A=0 from sub_eq_zero.mpr hA.eq,map_zero]

private theorem real_spin (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) (j : Fin 4) :
    Commute (activeSpin j) (multiply c hc) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (quantized (GaussCoframeSpin.full (activeIndex j))) (c z:ℂ) (f z)

private theorem inverse_constant (sharp : Bool) (a : ScalarIndex) : Commute inverseVolumeAction (M sharp a) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact (map_smul (branchMap sharp (scalarBasis a)) (reciprocalVolume z:ℂ) (f z)).symm
private theorem inverse_M8 (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) :
    Commute inverseVolumeAction (M8 sharp mu a) := by
  rw [←recipe_M]
  exact recipe_commute mu _ _ (real_spin _ _) (inverse_constant sharp a)
private theorem inverse_constantDagger (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) :
    Commute inverseVolumeAction (constantDagger sharp mu a) := (inverse_M8 (!sharp) mu a).smul_right _

private theorem native_inverse (v : Ambient) : Commute (covariantMomentum v) inverseVolumeAction := by
  have h := SourceHamiltonianVolume.native_momentum_volume v
  have hVU : Commute inverseVolumeAction SourceCoframeVolume.volumeAction := by
    unfold inverseVolumeAction
    exact SourceHamiltonianVolume.real_volume _ _
  apply LinearMap.ext
  intro f
  have hi (q : QuantumTest) : inverseVolumeAction (SourceCoframeVolume.volumeAction q)=q :=
    (LinearMap.congr_fun hVU.eq q).trans (volume_inverse q)
  have he := congrArg inverseVolumeAction (LinearMap.congr_fun h.eq (inverseVolumeAction f))
  simpa only [Module.End.mul_apply,volume_inverse,hi] using he.symm

private theorem weight_inverse : multiply scalarWeight scalarWeight_smooth=(-(sourceTime 0:ℂ)) • inverseVolumeAction := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  unfold inverseVolumeAction
  change (scalarWeight z:ℂ) • f z=(-(sourceTime 0:ℂ)) • ((reciprocalVolume z:ℂ) • f z)
  rw [smul_smul,←Complex.ofReal_neg,←Complex.ofReal_mul]
  congr 1

private theorem gamma_native_action (sharp : Bool) (mu : Fin 8) :
    ((sourceTime 0:ℂ)/2) • (inverseVolumeAction*gammaCore sharp mu)=
      (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,(M8 sharp mu a*W*P a-Pa a*W*M8 sharp mu a)) := by
  rw [M8_native_source,show W=(-(sourceTime 0:ℂ)) • inverseVolumeAction from weight_inverse]
  simp only [smul_mul_assoc,smul_smul]
  have hc : (-Complex.I/2)*(-Complex.I)*(-(sourceTime 0:ℂ))=(sourceTime 0:ℂ)/2 := by
    calc _= -(Complex.I*Complex.I)*(sourceTime 0:ℂ)/2 := by ring
         _=_ := by rw [Complex.I_mul_I];ring
  rw [←mul_assoc,hc]

private theorem native_gamma_row (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (q u : QuantumTest) :
    sourcePair q ((M8 sharp mu a*W*P a-Pa a*W*M8 sharp mu a) u)=
      (sourceTime 0:ℂ)*(sourcePair (P a (inverseVolumeAction q)) (M8 sharp mu a u)-
        sourcePair (constantDagger sharp mu a (inverseVolumeAction q)) (P a u)) := by
  have hfirst := M8_pair sharp mu a q (W (P a u))
  have hsecond := adjoint_pair (scalarDirection a) q (W (M8 sharp mu a u))
  have hP := LinearMap.congr_fun (native_inverse (scalarDirection a)).eq q
  change P a (inverseVolumeAction q)=inverseVolumeAction (P a q) at hP
  have hM := LinearMap.congr_fun (inverse_constantDagger sharp mu a).eq q
  change inverseVolumeAction (constantDagger sharp mu a q)=constantDagger sharp mu a (inverseVolumeAction q) at hM
  simp only [sourcePair,Module.End.mul_apply,LinearMap.sub_apply,map_sub,inner_sub_right] at *
  rw [hfirst,hsecond,show W=(-(sourceTime 0:ℂ)) • inverseVolumeAction from weight_inverse]
  simp only [LinearMap.smul_apply,map_smul,inner_smul_right]
  have hi (p f : QuantumTest) : inner ℂ (embed p) (embed (inverseVolumeAction f))=
      inner ℂ (embed (inverseVolumeAction p)) (embed f) := multiply_pair _ _ _ _
  rw [hi,hi,hM,←hP]
  ring

/-- The retained native projection uses the actual adjoint coefficient and the original P on the common u. -/
def nativeProjection (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℂ :=
  ∑ sharp : Bool,∑ mu : Fin 8,∑ a : ScalarIndex,
    sourcePair (constantDagger sharp mu a (inverseVolumeAction (jointState sharp m ell F z hz g mu)))
      (P a (windowState m ell F z hz g))
private def leftNativePair (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) : ℂ :=
  ∑ sharp : Bool,∑ mu : Fin 8,∑ a : ScalarIndex,
    sourcePair (P a (inverseVolumeAction (jointState sharp m ell F z hz g mu)))
      (M8 sharp mu a (windowState m ell F z hz g))

/-- Gamma returns as a genuine native paired current, retaining every original connection and density row. -/
theorem actual_joint_gamma_native_source (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    (∑ sharp : Bool,∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (gammaWord sharp m ell F z hz g mu)).im=
      -(sourceTime 0/2)*(leftNativePair m ell F z hz g).re+
        (sourceTime 0/2)*(nativeProjection m ell F z hz g).re := by
  have hgamma (sharp : Bool) (mu : Fin 8) : gammaWord sharp m ell F z hz g mu=
      (-Complex.I/2:ℂ) • (∑ a : ScalarIndex,(M8 sharp mu a*W*P a-Pa a*W*M8 sharp mu a)
        (windowState m ell F z hz g)) := by
    have h := LinearMap.congr_fun (gamma_native_action sharp mu) (windowState m ell F z hz g)
    simpa only [gammaWord,LinearMap.smul_apply,LinearMap.sum_apply,Module.End.mul_apply] using h
  simp_rw [hgamma]
  simp only [sourcePair,map_smul,map_sum,inner_smul_right,inner_sum]
  have hfold (p q : QuantumTest) : inner ℂ (embed p) (embed q)=sourcePair p q := rfl
  simp_rw [hfold,native_gamma_row]
  simp only [←Finset.mul_sum,Finset.sum_sub_distrib]
  unfold nativeProjection leftNativePair
  have he : (-Complex.I/2)*(sourceTime 0:ℂ)=(-Complex.I)*((sourceTime 0/2:ℝ):ℂ) := by push_cast;ring
  rw [←mul_assoc,he]
  simp only [Complex.mul_im,Complex.mul_re,Complex.sub_re,Complex.I_re,Complex.I_im,Complex.neg_re,Complex.neg_im,
    Complex.ofReal_re,Complex.ofReal_im,mul_zero]
  ring

private def boundedM (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) : Op :=
  if h0 : mu.val=0 then constantBounded sharp (scalarBasis a) else
  if h1 : mu.val<5 then bracket (spinBounded ⟨mu.val-1,by omega⟩) (constantBounded sharp (scalarBasis a)) else
    bracket (spinBounded ⟨mu.val-5,by omega⟩) (bracket (spinBounded 3) (constantBounded sharp (scalarBasis a)))
private theorem spin_core (j : Fin 4) (f : QuantumTest) : spinBounded j (embed f)=embed (activeSpin j f) := by
  unfold spinBounded
  exact GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f
private theorem bracket_core (A B : Op) (a b : End)
    (ha : ∀ f,A (embed f)=embed (a f)) (hb : ∀ f,B (embed f)=embed (b f)) (f : QuantumTest) :
    bracket A B (embed f)=embed (bracket a b f) := by
  simp only [bracket,mul_apply_eq_comp,sub_apply,Module.End.mul_apply,LinearMap.sub_apply,ha,hb,map_sub]
private theorem bounded_M_core (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) (f : QuantumTest) :
    boundedM sharp mu a (embed f)=embed (M8 sharp mu a f) := by
  have hM := constant_bounded_core sharp (scalarBasis a)
  have hJ (j : Fin 4) := bracket_core (spinBounded j) (constantBounded sharp (scalarBasis a))
    (activeSpin j) (M sharp a) (spin_core j) hM
  have hJJ (j : Fin 4) := bracket_core (spinBounded j) (bracket (spinBounded 3) (constantBounded sharp (scalarBasis a)))
    (activeSpin j) (bracket (activeSpin 3) (M sharp a)) (spin_core j) (hJ 3)
  unfold boundedM M8 constantCoefficient
  split
  · exact hM f
  · split
    · exact hJ _ f
    · exact hJJ _ f
private def constantPrice : ℝ := ∑ sharp : Bool,∑ mu : Fin 8,∑ a : ScalarIndex,‖boundedM sharp mu a‖^2
private theorem constant_price_nonnegative : 0 ≤ constantPrice := by unfold constantPrice;positivity

private theorem gram_bound {ι : Type*} [Fintype ι] (p q : ι → QuantumTest) :
    ‖∑ a,sourcePair (p a) (q a)‖^2 ≤ (∑ a,‖embed (p a)‖^2)*(∑ a,‖embed (q a)‖^2) := by
  have h := (norm_sum_le (Finset.univ : Finset ι) (fun a => sourcePair (p a) (q a))).trans
    (Finset.sum_le_sum (fun a _ => norm_inner_le_norm (𝕜 := ℂ) (embed (p a)) (embed (q a))))
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => ‖embed (p a)‖) (fun a => ‖embed (q a)‖))

private theorem left_native_square (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    ‖leftNativePair m ell F z hz g‖^2 ≤
      (∑ sharp : Bool,scalarColumn (jointState sharp m ell F z hz g))*
        (constantPrice*‖embed (windowState m ell F z hz g)‖^2) := by
  have h := gram_bound (ι := Bool×Fin 8×ScalarIndex)
    (fun t => P t.2.2 (inverseVolumeAction (jointState t.1 m ell F z hz g t.2.1)))
    (fun t => M8 t.1 t.2.1 t.2.2 (windowState m ell F z hz g))
  have hb : (∑ sharp : Bool,∑ mu : Fin 8,∑ a : ScalarIndex,
      ‖embed (M8 sharp mu a (windowState m ell F z hz g))‖^2) ≤
        constantPrice*‖embed (windowState m ell F z hz g)‖^2 := by
    unfold constantPrice
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro sharp _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro mu _
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro a _
    rw [←bounded_M_core]
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((boundedM sharp mu a).le_opNorm (embed (windowState m ell F z hz g))) 2
  simp only [Fintype.sum_prod_type,leftNativePair,scalarColumn,scalarForm] at h ⊢
  exact h.trans (mul_le_mul_of_nonneg_left hb (by positivity))

private theorem young_square (a p e η : ℝ) (hp : 0 ≤ p) (he : 0 ≤ e) (hη : 0<η)
    (hs : a^2 ≤ p*e) : a ≤ η*p+e/(4*η) := by
  have hi : 4*(η*p)*(e/(4*η))=p*e := by field_simp [hη.ne']
  have hr : 0 ≤ η*p+e/(4*η) := add_nonneg (mul_nonneg hη.le hp) (div_nonneg he (by positivity))
  nlinarith only [hs,hi,hr,sq_nonneg (η*p-e/(4*η))]

private theorem left_native_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain)
    (β : ℝ) (hβ : 0<β) :
    (sourceTime 0/2)*(leftNativePair m ell F z hz g).re ≤
      β*(sourceTime 0)^2*(∑ sharp : Bool,scalarColumn (jointState sharp m ell F z hz g))+
        (constantPrice/(16*β))*‖embed (windowState m ell F z hz g)‖^2 := by
  have h := left_native_square m ell F z hz g
  have hr := pow_le_pow_left₀ (abs_nonneg (leftNativePair m ell F z hz g).re)
    (Complex.abs_re_le_norm (leftNativePair m ell F z hz g)) 2
  rw [sq_abs] at hr
  have hp : 0 ≤ (sourceTime 0)^2*(∑ sharp : Bool,scalarColumn (jointState sharp m ell F z hz g)) := by
    unfold scalarColumn scalarForm
    positivity
  have he : 0 ≤ constantPrice*‖embed (windowState m ell F z hz g)‖^2/4 :=
    div_nonneg (mul_nonneg constant_price_nonnegative (sq_nonneg _)) (by norm_num)
  have hs : ((sourceTime 0/2)*(leftNativePair m ell F z hz g).re)^2 ≤
      ((sourceTime 0)^2*(∑ sharp : Bool,scalarColumn (jointState sharp m ell F z hz g)))*
        (constantPrice*‖embed (windowState m ell F z hz g)‖^2/4) := by
    calc
      _ = (sourceTime 0/2)^2*((leftNativePair m ell F z hz g).re)^2 := by ring
      _ ≤ (sourceTime 0/2)^2*((∑ sharp : Bool,scalarColumn (jointState sharp m ell F z hz g))*
          (constantPrice*‖embed (windowState m ell F z hz g)‖^2)) :=
        mul_le_mul_of_nonneg_left (hr.trans h) (sq_nonneg (sourceTime 0/2))
      _ = _ := by ring
  exact (young_square _ _ _ β hp he hβ hs).trans_eq (by ring)

/-- No gamma multiplier or gamma-weighted error is hidden in this returned field current. -/
def gammaNativePrice (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain)
    (η ξ ζ τ β : ℝ) : ℝ :=
  (η+ζ+τ)*(sourceTime 0)^2*(∑ sharp : Bool,jointCoframe (jointState sharp m ell F z hz g))+
    (ξ+β)*(sourceTime 0)^2*(∑ sharp : Bool,scalarColumn (jointState sharp m ell F z hz g))-
    (sourceTime 0/2)*(nativeProjection m ell F z hz g).re-
    (∑ sharp : Bool,∑ mu : Fin 8,sourcePair (jointState sharp m ell F z hz g mu)
      (SourceClockYukawaJointCoframeForce.matterWord sharp m ell F z hz g mu+
        SourceClockYukawaJointDefectForce.coherentDefectWord sharp m ell F z hz g mu)).im

def gammaNativeBudget (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η ξ ζ τ β : ℝ) : ENNReal :=
  ∫⁻ w : ℝ,ENNReal.ofReal (gammaNativePrice m ell F (line μ w)
    (by simpa only [line_im] using hμ.ne') g η ξ ζ τ β)

private theorem bool_pair_sum (f : Bool → ℂ) : (∑ sharp : Bool,f sharp)=f false+f true := by
  simp only [Fintype.sum_bool]
  ring

/-- The actual native scalar slot pays the first half of the whole sixteen-component gamma current. -/
theorem actual_joint_gamma_native_price (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0)
    (g : diagonal.domain) (η ξ ζ τ β : ℝ) (hβ : 0<β) :
    dualFieldPrice m ell F z hz g η ξ ζ τ ≤ gammaNativePrice m ell F z hz g η ξ ζ τ β+
      (constantPrice/(16*β))*‖embed (windowState m ell F z hz g)‖^2 := by
  have hn := left_native_price m ell F z hz g β hβ
  have hgamma := actual_joint_gamma_native_source m ell F z hz g
  have hg := actual_joint_gamma_word_form m ell F z hz g
  rw [bool_pair_sum] at hgamma
  rw [←Finset.sum_add_distrib] at hgamma
  unfold dualFieldPrice dualFieldImag gammaNativePrice
  linarith only [hn,hgamma,hg]

private theorem line_nonreal (μ : ℝ) (hμ : 0<μ) (w : ℝ) : (line μ w).im≠0 := by
  simpa only [line_im] using hμ.ne'
private theorem resolvent_embed (F : Index) (z : ℂ) (hz : z.im≠0) (f : QuantumTest) :
    embed (resolventCore F z hz f)=finiteResolvent F z (embed f) := by
  unfold resolventCore SourceScalarPositiveBulkWard.state
  exact congrArg Subtype.val (coreEquiv.apply_symm_apply _)
private theorem theta_inverse (m ell : ℕ) : Commute (relativeTail m ell) inverseRadius := by
  have hi : Commute (thetaAction m ell) inverseAction := by
    unfold thetaAction
    exact (((Commute.one_left inverseAction).sub_left (Commute.refl inverseAction)).pow_left _).sub_left
      (((Commute.one_left inverseAction).sub_left (Commute.refl inverseAction)).pow_left _)
  apply GaussYukawaGrade.core_ext
  intro f
  simp only [mul_apply_eq_comp,SourceMixedNativeReturn.theta_core,inverse_core]
  exact congrArg embed (LinearMap.congr_fun hi.eq f)
private def inverseInput (g : diagonal.domain) : diagonal.domain := coreEquiv (inverseAction (inputCore g))
private theorem inverse_input_embed (g : diagonal.domain) : (inverseInput g:H)=inverseRadius (radiusSource g:H) := by
  have he : embed (inputCore g)=(radiusSource g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  change embed (inverseAction (inputCore g))=_
  rw [←inverse_core,he]

private theorem window_embed (m ell : ℕ) (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    embed (windowState m ell F z hz g)=
      inverseRadius (relativeTail m ell (finiteResolvent F z (radiusSource g:H)))-
        relativeTail m ell (finiteResolvent F z (inverseInput g:H)) := by
  have he : embed (inputCore g)=(radiusSource g:H) := congrArg Subtype.val (coreEquiv.apply_symm_apply _)
  have hS := congrArg (fun A : Op => A (finiteResolvent F z (radiusSource g:H))) (theta_inverse m ell).eq
  simp only [windowState,radialMap,Module.End.mul_apply,LinearMap.sub_apply,map_sub,
    ←SourceMixedNativeReturn.theta_core,←inverse_core,resolvent_embed,he,←inverse_input_embed]
  exact congrArg (fun v : H => v-relativeTail m ell (finiteResolvent F z (inverseInput g:H))) hS

private theorem inverse_norm : ‖inverseRadius‖ ≤ 1 := by
  unfold inverseRadius
  exact GaussBoundedMultiplier.extension_norm _ _ _ _ _ _
private theorem two_square (x y : H) : ‖x-y‖^2≤2*‖x‖^2+2*‖y‖^2 := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith only [h,sq_nonneg (‖x‖-‖y‖)]
private theorem window_energy_measurable (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    Measurable (fun w : ℝ => ENNReal.ofReal
      (‖embed (windowState m ell F (line μ w) (line_nonreal μ hμ w) g)‖^2)) := by
  simp_rw [window_embed]
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  exact (((inverseRadius.continuous.comp ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const))).sub
    ((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const))).norm.pow 2).measurable.ennreal_ofReal

private theorem window_energy_common_tail (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
      (∫⁻ w : ℝ,ENNReal.ofReal (‖embed (windowState m ell F (line μ w)
        (line_nonreal μ hμ w) g)‖^2)) ≤ ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀,h₀⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail μ hμ (radiusSource g) (ε/4) (by positivity)
  obtain ⟨N₁,h₁⟩ := SourceRetardedForcingTail.actual_theta_full_frequency_tail μ hμ (inverseInput g) (ε/4) (by positivity)
  refine ⟨max N₀ N₁,fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hx hy
  have hr := SourceRetardedBandCurrent.finite_frequency_continuous μ hμ F
  have hmy : Measurable (fun w : ℝ => ENNReal.ofReal 2*ENNReal.ofReal
      (‖relativeTail m ell (finiteResolvent F (line μ w) (inverseInput g:H))‖^2)) :=
    ((((relativeTail m ell).continuous.comp (hr.clm_apply continuous_const)).norm.pow 2).measurable.ennreal_ofReal).const_mul _
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal 2*ENNReal.ofReal
        (‖relativeTail m ell (finiteResolvent F (line μ w) (radiusSource g:H))‖^2)+
      ENNReal.ofReal 2*ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (inverseInput g:H))‖^2) := by
      apply lintegral_mono
      intro w
      dsimp only
      rw [window_embed,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
      apply (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
      have h := (inverseRadius.le_opNorm (relativeTail m ell (finiteResolvent F (line μ w) (radiusSource g:H)))).trans
        (mul_le_mul_of_nonneg_right inverse_norm (norm_nonneg _))
      have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
      simp only [one_mul] at hs
      exact (two_square _ _).trans (add_le_add (mul_le_mul_of_nonneg_left hs (by norm_num)) le_rfl)
    _ = ENNReal.ofReal 2*(∫⁻ w : ℝ,ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (radiusSource g:H))‖^2))+
        ENNReal.ofReal 2*(∫⁻ w : ℝ,ENNReal.ofReal (‖relativeTail m ell (finiteResolvent F (line μ w) (inverseInput g:H))‖^2)) := by
      rw [lintegral_add_right _ hmy,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal 2*ENNReal.ofReal (ε/4)+ENNReal.ofReal 2*ENNReal.ofReal (ε/4) := by gcongr
    _ = ENNReal.ofReal ε := by
      rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
        ←ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- Formal adjoint parity of each original constant native coefficient, including the independent dual. -/
theorem original_constant_dagger_pair (sharp : Bool) (mu : Fin 8) (a : ScalarIndex) :
    GaussCoframeForm.Paired (constantCoefficient sharp mu (scalarBasis a)) (constantDagger sharp mu a) :=
  M8_pair sharp mu a

private theorem gamma_native_integral (m ell : ℕ) (F : Index) (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain)
    (η ξ ζ τ β : ℝ) (hβ : 0<β) :
    dualFieldBudget m ell F μ hμ g η ξ ζ τ ≤ gammaNativeBudget m ell F μ hμ g η ξ ζ τ β+
      ENNReal.ofReal (constantPrice/(16*β))*(∫⁻ w : ℝ,ENNReal.ofReal
        (‖embed (windowState m ell F (line μ w) (line_nonreal μ hμ w) g)‖^2)) := by
  have hC : 0 ≤ constantPrice/(16*β) := div_nonneg constant_price_nonnegative (by positivity)
  have hm := window_energy_measurable m ell F μ hμ g
  unfold dualFieldBudget gammaNativeBudget
  calc
    _ ≤ ∫⁻ w : ℝ,ENNReal.ofReal (gammaNativePrice m ell F (line μ w) (line_nonreal μ hμ w) g η ξ ζ τ β)+
        ENNReal.ofReal (constantPrice/(16*β))*ENNReal.ofReal
          (‖embed (windowState m ell F (line μ w) (line_nonreal μ hμ w) g)‖^2) := by
      apply lintegral_mono
      intro w
      exact (ENNReal.ofReal_le_ofReal (actual_joint_gamma_native_price m ell F (line μ w)
        (line_nonreal μ hμ w) g η ξ ζ τ β hβ)).trans
        (ENNReal.ofReal_add_le.trans (add_le_add le_rfl (le_of_eq (ENNReal.ofReal_mul hC))))
    _ = _ := by rw [lintegral_add_right _ (hm.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- Actual fixed-window L2 tails pay the bounded M half of gamma inside the whole sixteen-component price. -/
theorem actual_joint_gamma_native_payment (μ : ℝ) (hμ : 0<μ) (g : diagonal.domain) (η ξ ζ τ β : ℝ) (hβ : 0<β) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),
        dualFieldBudget m ell F μ hμ g η ξ ζ τ ≤ ENNReal.ofReal ε+gammaNativeBudget m ell F μ hμ g η ξ ζ τ β := by
  intro ε hε
  let C := constantPrice/(16*β)
  have hC : 0 ≤ C := div_nonneg constant_price_nonnegative (by positivity)
  let δ := ε/(C+1)
  have hδ : 0<δ := div_pos hε (by linarith only [hC])
  obtain ⟨N,hN⟩ := window_energy_common_tail μ hμ g δ hδ
  refine ⟨N,fun m hm ell hml => ?_⟩
  filter_upwards [hN m hm ell hml] with F hF
  have hb := gamma_native_integral m ell F μ hμ g η ξ ζ τ β hβ
  have hc : ENNReal.ofReal C*ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    have hd : δ*(C+1)=ε := by dsimp [δ];exact div_mul_cancel₀ ε (ne_of_gt (by linarith only [hC]))
    nlinarith only [hd,hδ]
  exact (hb.trans (add_le_add le_rfl ((mul_le_mul le_rfl hF zero_le zero_le).trans hc))).trans_eq (add_comm _ _)

/-- Original Gamma consumes the actual paid gamma current; the remaining native projection and full matter/defect word stay signed. -/
theorem actual_original_joint_gamma_native_budget (μ : ℝ) (hμ : 0<μ) (g k : diagonal.domain) (η ξ ζ τ β : ℝ)
    (hη : 0<η) (hξ : 0<ξ) (hζ : 0<ζ) (hτ : 0<τ) (hβ : 0<β) :
    ∀ ε : ℝ,0<ε → ∃ N : ℕ,∀ m,N ≤ m → ∀ ell,m ≤ ell →
      ∀ᶠ F in (sourceFilter : Filter Index),∀ sharp : Bool,
        ENNReal.ofReal (closedJointCost sharp m ell F μ (g:H) (k:H)) ≤
          ENNReal.ofReal ε+ENNReal.ofReal (3*SourceClockYukawaRadialGammaNativeBudget.sourceMuFactor μ k)*
            gammaNativeBudget m ell F μ hμ g η ξ ζ τ β := by
  intro ε hε
  let κ := 3*SourceClockYukawaRadialGammaNativeBudget.sourceMuFactor μ k
  have hκ : 0 ≤ κ := by dsimp [κ];unfold SourceClockYukawaRadialGammaNativeBudget.sourceMuFactor;positivity
  let δ := ε/(2*(κ+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨N₀,h₀⟩ := actual_original_joint_dual_field_budget μ hμ g k η ξ ζ τ hη hξ hζ hτ (ε/2) (by positivity)
  obtain ⟨N₁,h₁⟩ := actual_joint_gamma_native_payment μ hμ g η ξ ζ τ β hβ δ hδ
  refine ⟨max N₀ N₁,fun m hm ell hml => ?_⟩
  filter_upwards [h₀ m (by omega) ell hml,h₁ m (by omega) ell hml] with F hc hb sharp
  have hp : ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ ≤ ENNReal.ofReal ε := by
    rw [←ENNReal.ofReal_mul hκ,←ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hd : δ*(2*(κ+1))=ε := by dsimp [δ];field_simp
    nlinarith only [hd,hδ]
  calc
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*dualFieldBudget m ell F μ hμ g η ξ ζ τ := hc sharp
    _ ≤ ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*(ENNReal.ofReal δ+gammaNativeBudget m ell F μ hμ g η ξ ζ τ β) :=
      add_le_add le_rfl (mul_le_mul le_rfl hb zero_le zero_le)
    _ = (ENNReal.ofReal (ε/2)+ENNReal.ofReal κ*ENNReal.ofReal δ)+
        ENNReal.ofReal κ*gammaNativeBudget m ell F μ hμ g η ξ ζ τ β := by rw [mul_add,add_assoc]
    _ ≤ _ := add_le_add hp le_rfl

end LowEnergy.SourceClockYukawaJointGammaNativeBudget
