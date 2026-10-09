import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiFullReverseScaleNoetherCurrent
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceInverseVolumeHamiltonianForceReduction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseBalancedForcePayer
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open GaussDiagonalHistory GaussUnitaryHistory GaussLiveMomentum GaussMatterCore
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceCoframeVolume SourceHamiltonianVolume SourceDilationRemainder
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarShiftedBulk SourceScalarEssentialBudget SourceScalarGaugeScale
open SourceScalarOscillatorAbsorption SourceScalarSpatialCurrent SourceScalarVolumePressure
open SourceNativeMatterCovarianceCancellation SourceUnmixedPotentialCancellation SourceMixedCurrentCancellation
open FirstCurrentDilationPrimitive SourceClockPhiOriginalGaussianH0KineticPrimitives ReverseNativeClock
open SourceInverseHamiltonianForceReduction
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev U:End:=inverseVolumeAction
private abbrev V:End:=volumeAction
private abbrev K:End:=scalarKinetic
private abbrev L:End:=localAction
private abbrev O:End:=offsetAction
private abbrev B:End:=scalarBulkComplete
private abbrev G:End:=SourceGaugeScaleTransport.generator
private abbrev H0:End:=diagonalAction
attribute [local irreducible] sourcePair embed diagonalAction scalarKinetic gaugeKinetic GaussMatterCore.matterAction
  scalarBulkComplete scalarBulk nativeDilationWord reverseScaleForce SourceGaugeScaleTransport.generator
private theorem end_sum_commute {R:Type*}[Ring R]{ι:Type*}[Fintype ι](A:ι→R)(B:R)
    (h:∀i,Commute (A i) B):Commute (∑i,A i) B:=by
  change (∑i,A i)*B=B*(∑i,A i)
  rw [Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _=>(h i).eq)
private theorem end_smul_commute {R:Type*}[Ring R][Module ℂ R][IsScalarTower ℂ R R][SMulCommClass ℂ R R]
    (c:ℂ)(A B:R)(h:Commute A B):Commute (c • A) B:=by
  change (c • A)*B=B*(c • A)
  rw [smul_mul_assoc,mul_smul_comm,h.eq]
private theorem end_mul_commute {R:Type*}[Ring R](A C E:R)(hA:Commute A E)(hC:Commute C E):
    Commute (A*C) E:=hA.mul_left hC
private theorem end_add_commute {R:Type*}[Ring R](A C E:R)(hA:Commute A E)(hC:Commute C E):
    Commute (A+C) E:=hA.add_left hC
private theorem real_commute (c d : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val)
    (hd : ∀ z : physicalChart,ContDiffAt ℝ ∞ d z.val) : Commute (multiply c hc) (multiply d hd) := by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact smul_comm (c z : ℂ) (d z : ℂ) (f z)

private theorem matter_real (c : SourceCoordinateSlice → ℝ)
    (hc : ∀ z : physicalChart,ContDiffAt ℝ ∞ c z.val) : Commute matterAction (multiply c hc) := by
  unfold matterAction
  apply end_sum_commute (R:=End)
  intro i
  apply end_sum_commute (R:=End)
  intro b
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  exact map_smul (GaussQuantumMultiplier.quantized (localMatrix i b z)) (c z : ℂ) (f z)


private theorem O_pair(f g:QuantumTest):sourcePair f (O g)=sourcePair (O f) g:=multiply_pair _ _ _ _
private theorem gauge_O:Commute gaugeKinetic O:=by
  have hp(i:Fin 3)(a:LieIndex):Commute (covariantMomentum (gaugeDirection i a)) O:=by
    apply sub_eq_zero.mp
    simpa only [gaugeDirection,inner_zero_left,Complex.ofReal_zero,mul_zero,zero_smul] using
      original_offset_momentum (gaugeDirection i a)
  have ha(i:Fin 3)(a:LieIndex):Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)) O:=by
    apply LinearMap.ext;intro g
    apply GaussCoreLabel.pair_separates;intro f
    change sourcePair f (GaussMomentumAdjoint.adjoint (gaugeDirection i a) (O g))=
      sourcePair f (O (GaussMomentumAdjoint.adjoint (gaugeDirection i a) g))
    have he:(covariantMomentum (gaugeDirection i a)) (O f)=O ((covariantMomentum (gaugeDirection i a)) f):=
      LinearMap.congr_fun (hp i a).eq f
    rw [adjoint_pair,O_pair,←he,←adjoint_pair,←O_pair]
  unfold gaugeKinetic
  apply end_smul_commute (R:=End)
  apply end_sum_commute (R:=End);intro a
  apply end_sum_commute (R:=End);intro i
  apply end_sum_commute (R:=End);intro j
  change Commute (GaussMomentumAdjoint.adjoint (gaugeDirection i a)*
    (multiply (fun z=>gaugeWeight z i j) (gaugeWeight_smooth i j)*covariantMomentum (gaugeDirection j a))) O
  exact end_mul_commute (R:=End) _ _ _ (ha i a) (end_mul_commute (R:=End) _ _ _ (real_commute _ _ _ _) (hp j a))
private theorem bulk_commute(T:End)(hU:Commute T U)(hK:Commute T K)(hL:Commute T L)(hO:Commute T O):
    Commute T B:=by
  unfold B scalarBulkComplete scalarBulk
  have h1:Commute (U*K) T:=end_mul_commute (R:=End) _ _ _ hU.symm hK.symm
  have h2:Commute (U*L) T:=end_mul_commute (R:=End) _ _ _ hU.symm hL.symm
  exact (end_add_commute (R:=End) _ _ _ (end_add_commute (R:=End) _ _ _
    (end_smul_commute (R:=End) (-8) _ _ h1) (end_smul_commute (R:=End) 8 _ _ h2))
    (end_smul_commute (R:=End) 8 _ _ hO.symm)).symm
private theorem gauge_B:Commute gaugeKinetic B:=
  bulk_commute _ gauge_kinetic_primitives.1.symm original_scalar_gauge_commute.symm original_gauge_local_commute gauge_O
private theorem matter_B:Commute GaussMatterCore.matterAction B:=by
  apply bulk_commute
  · exact matter_real _ _
  · exact original_scalar_matter_commute.symm
  · exact matter_real _ _
  · exact matter_real _ _
private theorem magnetic_B:Commute magneticAction B:=by
  apply bulk_commute
  · exact real_commute _ _ _ _
  · exact original_scalar_magnetic_commute.symm
  · exact real_commute _ _ _ _
  · exact real_commute _ _ _ _
private theorem spatial_split:spatialAction=scalarSpatialAction+magneticAction:=by
  apply LinearMap.ext;intro f;apply DFunLike.ext;intro z
  change (spatialPotential z:ℂ) • f z=
    ((-(sourceTime 0*volume z/2*∑i:Fin 3,∑j:Fin 3,inverseSpatial z i j*inner ℝ (scalarGradient z i) (scalarGradient z j)):ℝ):ℂ) • f z+
    (magneticPotential z:ℂ) • f z
  rw [←add_smul,←Complex.ofReal_add]
  congr 2
private theorem badd(A C E:End):bracket A (C+E)=bracket A C+bracket A E:=by unfold bracket;noncomm_ring
private theorem bsmul(A C:End)(c:ℂ):bracket A (c • C)=c • bracket A C:=by
  unfold bracket;simp only [mul_smul_comm,smul_mul_assoc,smul_sub]
private theorem bprod(A C E:End):bracket A (C*E)=bracket A C*E+C*bracket A E:=by unfold bracket;noncomm_ring
private theorem scalar_spatial_B:bracket scalarSpatialAction B=(8:ℂ) • (U*scalarSpatialDivergence):=by
  have hS:Commute scalarSpatialAction U:=real_commute _ _ _ _
  have hL:Commute scalarSpatialAction L:=real_commute _ _ _ _
  have hO:Commute scalarSpatialAction O:=real_commute _ _ _ _
  have hK:bracket scalarSpatialAction K= -scalarSpatialDivergence:=by
    have h:=original_scalar_spatial_current
    unfold bracket
    linear_combination (norm:=module) -h
  unfold B scalarBulkComplete scalarBulk
  rw [badd,badd,bsmul,bsmul,bsmul,bprod,bprod,
    show bracket scalarSpatialAction U=0 from sub_eq_zero.mpr hS.eq,
    show bracket scalarSpatialAction L=0 from sub_eq_zero.mpr hL.eq,
    show bracket scalarSpatialAction O=0 from sub_eq_zero.mpr hO.eq,hK]
  simp only [zero_mul,mul_zero,add_zero,zero_add,smul_zero,mul_neg,smul_neg,neg_smul,neg_neg]

/-- The full original gauge force keeps its signed spatial sector. The coframe has zero gauge derivative by its actual source law. -/
theorem actual_gauge_hamiltonian_departments:
    bracket G H0=(-2:ℂ) • gaugeKinetic+matterAction+(2:ℂ) • scalarSpatialAction+(4:ℂ) • magneticAction:=by
  have h:=SourceGaugeScaleTransport.generator_commutator H0
  rw [original_hamiltonian_gauge_source] at h
  exact h

/-- Gauge removal has a literal scalar-spatial current; its nonzero contribution must be retained with the original full compression defect. -/
theorem actual_gauge_hamiltonian_scalar_current:
    bracket (bracket G H0) B=(16:ℂ) • (U*scalarSpatialDivergence):=by
  have hk:bracket gaugeKinetic B=0:=sub_eq_zero.mpr gauge_B.eq
  have hm:bracket matterAction B=0:=sub_eq_zero.mpr matter_B.eq
  have hg:bracket magneticAction B=0:=sub_eq_zero.mpr magnetic_B.eq
  rw [actual_gauge_hamiltonian_departments]
  unfold bracket at hk hm hg ⊢
  have hs:=scalar_spatial_B
  unfold bracket at hs
  linear_combination (norm:=(noncomm_ring;module)) (-2:ℂ) • hk+hm+(2:ℂ) • hs+(4:ℂ) • hg

def gaugeBalancedNativeForce:End:=reverseScaleForce-(9:ℂ) • bracket G H0

/-- In the same nine-gauge Ward subtraction, the complete native gauge-kinetic force cancels exactly, leaving the actual signed scalar, matter, magnetic and local departments. -/
theorem actual_balanced_native_departments:
    gaugeBalancedNativeForce=(-6:ℂ) • scalarKinetic-(24:ℂ) • matterAction+
      (6:ℂ) • centeredAction-(6:ℂ) • vacuumLinearAction-(72:ℂ) • magneticAction-
      (36:ℂ) • localAction-(42:ℂ) • scalarSpatialAction:=by
  unfold gaugeBalancedNativeForce
  rw [actual_reverse_scale_departments,actual_gauge_hamiltonian_departments,spatial_split]
  module

/-- The compensated native force meets the same B-current: the spatial coefficient changes from 192 to 336, with no gauge-kinetic or coframe norm charge. -/
theorem actual_balanced_native_scalar_current:
    bracket gaugeBalancedNativeForce B=(-18:ℂ) • SourceScalarOscillatorAbsorption.scalarCurrent-
      (336:ℂ) • (U*scalarSpatialDivergence):=by
  have h:=actual_reverse_force_scalar_current
  have hg:=actual_gauge_hamiltonian_scalar_current
  unfold gaugeBalancedNativeForce bracket at *
  linear_combination (norm:=(noncomm_ring;module)) h-(9:ℂ) • hg
end LowEnergy.ReverseBalancedForcePayer
