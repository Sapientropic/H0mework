import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceHamiltonianScaleJet
import H0mework.Versions.AE.Physics.LowEnergy.Quantum.SourceCornerForcing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
noncomputable section
namespace LowEnergy.SourceScaleJetFactor
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussNativeForm GaussNativeEnergy
open GaussHistoryHilbert GaussYukawaCoefficient GaussRadialDomain
open SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeVolumeCurrent SourcePhysicalKineticSquare SourceDilationRemainder
open SourceSignedRadiusBalance SourceCornerForcing SourceRelativePowerTail SourceEscapeSeedTail
open SourceHamiltonianScaleJet GaussDiagonalHistory FullYSourceCutoffVolterra
open scoped ContDiff Topology InnerProductSpace

def coefficient (z : SourceCoordinateSlice) : ℝ := radius z/(4*radius z^2-1)

private theorem denominator_pos (z : SourceCoordinateSlice) : 0<4*radius z^2-1 := by
  have h := one_le_radius z
  nlinarith [sq_nonneg (radius z-1)]

theorem coefficient_bounds (z : SourceCoordinateSlice) : 0≤coefficient z ∧ coefficient z≤1/3 := by
  have h := one_le_radius z
  have hd := denominator_pos z
  constructor
  · exact (div_pos (radius_pos z) hd).le
  · apply (div_le_iff₀ hd).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr h) (show 0≤4*radius z+1 by positivity)]

theorem coefficient_smooth : ContDiff ℝ ∞ coefficient :=
  radius_smooth.div ((contDiff_const.mul (radius_smooth.pow 2)).sub contDiff_const)
    (fun z => (denominator_pos z).ne')

def fiber (z : SourceCoordinateSlice) : FockFiber →L[ℂ] FockFiber :=
  (coefficient z : ℂ) • ContinuousLinearMap.id ℂ FockFiber

private theorem fiber_smooth : ContDiff ℝ ∞ fiber :=
  (Complex.ofRealCLM.contDiff.comp coefficient_smooth).smul contDiff_const

private theorem fiber_commutes (z : SourceCoordinateSlice) (w : ℕ → ℂ) :
    Commute (GaussFockWeights.weight w) (fiber z) :=
  (Commute.one_right _).smul_right _

private theorem fiber_bound (z : SourceCoordinateSlice) (f : FockFiber) :
    ‖fiber z f‖≤(1/3 : ℝ)*‖f‖ := by
  change ‖(coefficient z : ℂ) • f‖≤_
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (coefficient_bounds z).1]
  exact mul_le_mul_of_nonneg_right (coefficient_bounds z).2 (norm_nonneg f)

def normalizer : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension fiber (fun _ => fiber_smooth.contDiffAt)
    (fun z => fiber_commutes z) (1/3) (by norm_num) (fun z => fiber_bound z)

def normalizerAction : CoreEnd := multiply coefficient (fun _ => coefficient_smooth.contDiffAt)

theorem normalizer_core (f : QuantumTest) : normalizer (embed f)=embed (normalizerAction f) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ f

theorem normalizer_norm : ‖normalizer‖≤(1/3 : ℝ) :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

private theorem normalizer_pair (x y : H) : inner ℂ (normalizer x) y=inner ℂ x (normalizer y) := by
  refine GaussBoundedMultiplier.core_dense.induction_on₂ (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro a b
  obtain ⟨f,rfl⟩ := coreEquiv.surjective a
  obtain ⟨g,rfl⟩ := coreEquiv.surjective b
  change inner ℂ (normalizer (embed f)) (embed g)=inner ℂ (embed f) (normalizer (embed g))
  rw [normalizer_core,normalizer_core]
  exact (multiply_pair _ _ f g).symm

theorem normalizer_inverse : Commute normalizer inverseRadius := by
  apply ContinuousLinearMap.ext
  intro x
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩ := coreEquiv.surjective a
  change normalizer (inverseRadius (embed f))=inverseRadius (normalizer (embed f))
  rw [inverse_core,normalizer_core,normalizer_core,inverse_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  exact smul_comm (coefficient z : ℂ) (reciprocal z : ℂ) (f z)

private theorem normalizer_bounded : Commute normalizer GaussYukawaOperator.bounded := by
  apply ContinuousLinearMap.ext
  intro x
  refine GaussBoundedMultiplier.core_dense.induction_on x (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro a
  obtain ⟨f,rfl⟩ := coreEquiv.surjective a
  change normalizer (GaussYukawaOperator.bounded (embed f))=
    GaussYukawaOperator.bounded (normalizer (embed f))
  rw [GaussYukawaOperator.bounded_core,normalizer_core,normalizer_core,GaussYukawaOperator.bounded_core]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  exact (map_smul (normalized z) (coefficient z : ℂ) (f z)).symm

theorem normalizer_vertex (sharp : Bool) : Commute normalizer (sourceVertex sharp) := by
  cases sharp
  · exact normalizer_bounded
  · have hs : IsSelfAdjoint normalizer :=
      (show normalizer.toLinearMap.IsSymmetric from normalizer_pair).isSelfAdjoint
    have h := congrArg star normalizer_bounded.eq
    change normalizer*GaussYukawaOperator.bounded.adjoint=
      GaussYukawaOperator.bounded.adjoint*normalizer
    simpa only [star_mul,hs.star_eq] using! h.symm

private theorem multiplier_increment {A : H →L[ℂ] H}
    (hS : Commute A inverseRadius) (hB : ∀ sharp, Commute A (sourceVertex sharp))
    (sharp : Bool) (m ell : ℕ) : Commute A (actualIncrement sharp m ell) := by
  have hc (n : ℕ) : Commute A (radiusCutoff n) := by
    exact Commute.sum_right _ _ _ (fun j _ => ((Commute.one_right A).sub_right hS).pow_right j)
  have he : actualIncrement sharp m ell=sourceVertex sharp*(radiusCutoff ell-radiusCutoff m) := by
    cases sharp
    · simp only [actualIncrement,Bool.false_eq_true,if_false,SourceRetardedIncrement.increment,
        sourceVertex,cutoff_radius_factor,mul_sub]
    · simp only [actualIncrement,if_true,sharpIncrement,
        sourceVertex,sharp_radius_factor,mul_sub]
  rw [he]
  exact (hB sharp).mul_right ((hc ell).sub_right (hc m))

theorem normalizer_increment (sharp : Bool) (m ell : ℕ) :
    Commute normalizer (actualIncrement sharp m ell) :=
  multiplier_increment normalizer_inverse normalizer_vertex sharp m ell

private theorem inverse_vertex (sharp : Bool) : Commute inverseRadius (sourceVertex sharp) := by
  cases sharp
  · exact bounded_inverse_commute.symm
  · have hs : IsSelfAdjoint inverseRadius :=
      (show inverseRadius.toLinearMap.IsSymmetric from inverse_pair).isSelfAdjoint
    have h := congrArg star bounded_inverse_commute.eq
    change inverseRadius*GaussYukawaOperator.bounded.adjoint=
      GaussYukawaOperator.bounded.adjoint*inverseRadius
    simpa only [star_mul,hs.star_eq] using! h

theorem inverse_increment (sharp : Bool) (m ell : ℕ) :
    Commute inverseRadius (actualIncrement sharp m ell) :=
  multiplier_increment (Commute.refl _) inverse_vertex sharp m ell

def factor (sharp : Bool) (m ell : ℕ) : H →L[ℂ] H :=
  ((sourceTime 0)⁻¹ : ℂ) • (normalizer*sourceVertex sharp*relativeTail m ell)

theorem factor_source (sharp : Bool) (m ell : ℕ) :
    factor sharp m ell=((sourceTime 0)⁻¹ : ℂ) •
      (normalizer*inverseRadius*actualIncrement sharp m ell) := by
  unfold factor
  rw [mul_assoc normalizer inverseRadius,actual_increment_factor,←mul_assoc]

private theorem source_time_pos : 0<sourceTime 0 := by
  rw [source_time_generated]
  exact SaturationMonoid.PhysicsCore.Stage9C.Material.SpinPair.lapse_pos

theorem factor_bound (sharp : Bool) (m ell : ℕ) (x : H) :
    ‖factor sharp m ell x‖≤(‖GaussYukawaOperator.bounded‖/(3*sourceTime 0))*‖relativeTail m ell x‖ := by
  have hb : ‖sourceVertex sharp‖=‖GaussYukawaOperator.bounded‖ := by
    cases sharp <;> simp [sourceVertex]
  change ‖((sourceTime 0)⁻¹ : ℂ) • normalizer (sourceVertex sharp (relativeTail m ell x))‖≤_
  rw [norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos source_time_pos]
  have hn := (normalizer.le_opNorm (sourceVertex sharp (relativeTail m ell x))).trans
    (mul_le_mul_of_nonneg_right normalizer_norm (norm_nonneg _))
  have hv := (sourceVertex sharp).le_opNorm (relativeTail m ell x)
  rw [hb] at hv
  calc
    _ ≤ (sourceTime 0)⁻¹*((1/3)*‖sourceVertex sharp (relativeTail m ell x)‖) :=
      mul_le_mul_of_nonneg_left hn (inv_nonneg.mpr source_time_pos.le)
    _ ≤ (sourceTime 0)⁻¹*((1/3)*(‖GaussYukawaOperator.bounded‖*‖relativeTail m ell x‖)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hv (by norm_num))
        (inv_nonneg.mpr source_time_pos.le)
    _ = _ := by ring

def radialAction : CoreEnd := inverseVolumeAction*localAction
def scaleJet : CoreEnd :=
  scaleDerivative (scaleDerivative (scaleDerivative diagonalAction))+
    (3 : ℂ) • scaleDerivative (scaleDerivative diagonalAction)-
    scaleDerivative diagonalAction-(3 : ℂ) • diagonalAction

theorem normalizer_radial_core (f : QuantumTest) :
    normalizer (inverseRadius (embed (radialAction f)))=(sourceTime 0 : ℂ) • embed f := by
  rw [inverse_core,normalizer_core,←map_smul]
  apply congrArg embed
  apply DFunLike.ext
  intro z
  change (coefficient z : ℂ) • ((reciprocal z : ℂ) •
    ((reciprocalVolume z : ℂ) • ((localPotential z : ℂ) • f z)))=(sourceTime 0 : ℂ) • f z
  by_cases hz : z∈physicalChart
  · rw [local_radius_source]
    simp only [coefficient,reciprocal,reciprocalVolume,smul_smul,←Complex.ofReal_mul]
    congr 1
    congr 1
    field_simp [(radius_pos z).ne',(volume_pos ⟨z,hz⟩).ne',(denominator_pos z).ne']
    have hd : radius z^2*4-1≠0 := by simpa only [mul_comm] using (denominator_pos z).ne'
    field_simp [hd]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (f.tsupport_subset h))]
    simp only [smul_zero]

set_option maxRecDepth 2048 in
theorem actual_core_factor (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    actualIncrement sharp m ell (embed f)=
      (1/48 : ℂ) • factor sharp m ell (embed (inverseVolumeAction (scaleJet f))) := by
  have hj : scaleJet=(48 : ℂ) • localAction := source_local_from_scale_jet
  have hc : Commute (normalizer*inverseRadius) (actualIncrement sharp m ell) :=
    (normalizer_increment sharp m ell).mul_left (inverse_increment sharp m ell)
  rw [hj,LinearMap.smul_apply,map_smul,map_smul,map_smul,smul_smul]
  norm_num
  rw [factor_source]
  change actualIncrement sharp m ell (embed f)=
    ((sourceTime 0)⁻¹ : ℂ) • ((normalizer*inverseRadius*actualIncrement sharp m ell) (embed (radialAction f)))
  rw [hc.eq]
  change _=((sourceTime 0)⁻¹ : ℂ) • actualIncrement sharp m ell
    (normalizer (inverseRadius (embed (radialAction f))))
  rw [normalizer_radial_core,map_smul,smul_smul]
  have hn : (sourceTime 0 : ℂ)≠0 := by exact_mod_cast source_time_pos.ne'
  rw [inv_mul_cancel₀ hn,one_smul]

private theorem increment_core (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    actualIncrement sharp m ell (embed f)∈Core := by
  cases sharp
  · exact (SourceRetardedIncrement.incrementCore m ell (coreEquiv f)).property
  · exact Core.sub_mem
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem ell (coreEquiv f))
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem m (coreEquiv f))

def incrementAction (sharp : Bool) (m ell : ℕ) (f : QuantumTest) : QuantumTest :=
  coreEquiv.symm ⟨actualIncrement sharp m ell (embed f),increment_core sharp m ell f⟩

theorem increment_action_embed (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    embed (incrementAction sharp m ell f)=actualIncrement sharp m ell (embed f) :=
  congrArg Subtype.val (coreEquiv.apply_symm_apply _)

theorem increment_adjoint (sharp : Bool) (m ell : ℕ) :
    (actualIncrement sharp m ell).adjoint=actualIncrement (!sharp) m ell := by
  cases sharp <;> simp [actualIncrement,sharpIncrement,SourceRetardedIncrement.increment]

def adjointFactorAction (sharp : Bool) (m ell : ℕ) (f : QuantumTest) : QuantumTest :=
  ((sourceTime 0)⁻¹ : ℂ) • incrementAction (!sharp) m ell (inverseAction (normalizerAction f))

theorem adjoint_factor_core (sharp : Bool) (m ell : ℕ) (f : QuantumTest) :
    (factor sharp m ell).adjoint (embed f)=embed (adjointFactorAction sharp m ell f) := by
  have hn : IsSelfAdjoint normalizer :=
    (show normalizer.toLinearMap.IsSymmetric from normalizer_pair).isSelfAdjoint
  have hs : IsSelfAdjoint inverseRadius :=
    (show inverseRadius.toLinearMap.IsSymmetric from inverse_pair).isSelfAdjoint
  rw [factor_source]
  change (star (((sourceTime 0)⁻¹ : ℂ) • (normalizer*inverseRadius*actualIncrement sharp m ell))) (embed f)=_
  rw [star_smul,star_mul,star_mul,hn.star_eq,hs.star_eq]
  have hc : star ((sourceTime 0)⁻¹ : ℂ)=((sourceTime 0)⁻¹ : ℂ) := by simp
  rw [hc]
  change ((sourceTime 0)⁻¹ : ℂ) • (actualIncrement sharp m ell).adjoint
    (inverseRadius (normalizer (embed f)))=_
  rw [increment_adjoint,normalizer_core,inverse_core]
  rw [←increment_action_embed]
  exact (map_smul embed _ _).symm

def leftTest (sharp : Bool) (m ell : ℕ) (f : QuantumTest) : QuantumTest :=
  inverseVolumeAction (adjointFactorAction sharp m ell f)

theorem full_pair_factor (sharp : Bool) (m ell : ℕ) (p q : QuantumTest) :
    inner ℂ (embed p) (actualIncrement sharp m ell (embed q))=
      (1/48 : ℂ)*sourcePair (leftTest sharp m ell p) (scaleJet q) := by
  rw [actual_core_factor,inner_smul_right,
    ←ContinuousLinearMap.adjoint_inner_left,adjoint_factor_core]
  congr 1
  change sourcePair (adjointFactorAction sharp m ell p) (inverseVolumeAction (scaleJet q))=_
  exact multiply_pair _ _ _ _

end LowEnergy.SourceScaleJetFactor
