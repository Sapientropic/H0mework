import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiHeatNativeHamiltonianWork
import H0mework.Versions.R9c73a630.Physics.LowEnergy.Quantum.SourceInverseVolumeNativeCoframeCompatibility
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 1200000
noncomputable section
namespace LowEnergy.FirstCurrentWholeVariance
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussLiveMomentum
open GaussNativeForm GaussNativeEnergy GaussNativePotential SourceQuantumConfigurationHilbert
open SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceNativeMomentumCurvature SourceNativeDensityTrace SourceNativeCoframeCompatibility
open SourceCoframeVolume SourceClockPhiCoframeForwardCore SourceClockPhiForwardGeneratorTransport
open SourceClockPhiHeatNativeHamiltonianWork
open scoped ContDiff Topology
private abbrev End := QuantumTest →ₗ[ℂ] QuantumTest
attribute [local irreducible] sourcePair embed
private theorem inverse_shift(c:Coframe)(z:SourceCoordinateSlice):inverseL (z+(c,0))=inverseL z:=by
  change inverseL (z.1+c,z.2+0)=inverseL z
  rw [add_zero]
  rfl
private theorem direction_shift(v:Ambient)(c:Coframe)(z:SourceCoordinateSlice):
    direction v (z+(c,0))=direction v z:=by rw [direction,inverse_shift];rfl
private theorem gamma_shift(c:Coframe)(z:SourceCoordinateSlice):gammaLog (z+(c,0))=gammaLog z:=by
  unfold gammaLog gammaField
  simp only[Prod.snd_add,add_zero]
private theorem gamma_density_shift(v:Ambient)(c:Coframe)(z:SourceCoordinateSlice):
    gammaDensity v (z+(c,0))=gammaDensity v z:=by
  have he:(fun x=>gammaLog (x+(c,0)))=gammaLog:=funext (gamma_shift c)
  have hd:fderiv ℝ gammaLog (z+(c,0))=fderiv ℝ gammaLog z:=by
    rw [←fderiv_comp_add_right,he]
  rw [gammaDensity,gammaDensity,hd,direction_shift]
private theorem density_correction_shift(v:Ambient)(c:Coframe)(z:SourceCoordinateSlice):
    nativeDensityCorrection v (z+(c,0))=nativeDensityCorrection v z:=by
  unfold nativeDensityCorrection intrinsicDensity sourceLieResponse inverseLie
  rw [inverse_shift,gamma_density_shift]
private theorem density_forward(v:Ambient)(t:ℝ)(z:SourceCoordinateSlice):
    nativeDensityCorrection v (forwardPoint t z)=nativeDensityCorrection v z:=by
  have he:forwardPoint t z=z+((forwardPoint t z).1-z.1,0):=by
    apply Prod.ext
    · simp
    · simp only[forwardPoint,SourceCoframeVolume.scale,Prod.snd_add,add_zero]
  rw [he,density_correction_shift]

private theorem forward_multiplier_fixed(t:ℝ)(ht:0≤t)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)
    (hi:∀z,b (forwardPoint t z)=b z):
    multiply b hb*sourceForwardCore t ht=sourceForwardCore t ht*multiply b hb:=by
  rw [actual_forward_multiplier_transport]
  congr 1
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  change ((b (forwardPoint t z):ℝ):ℂ) • f z=(b z:ℂ) • f z
  rw [hi]
private theorem forward_divergence(t:ℝ)(ht:0≤t)(v:Ambient):
    divergenceAction v*sourceForwardCore t ht=sourceForwardCore t ht*divergenceAction v:=by
  rw [original_native_density_multiplier]
  exact forward_multiplier_fixed t ht _ _ (density_forward v t)

/-- The independent native transpose is returned through the actual one-sided forward clock.
The density correction is transported from the original source; no inverse of J is introduced. -/
theorem actual_forward_native_adjoint(t:ℝ)(ht:0≤t)(v:Ambient):
    GaussMomentumAdjoint.adjoint v*sourceForwardCore t ht=
      sourceForwardCore t ht*GaussMomentumAdjoint.adjoint v:=by
  rw [original_adjoint_divergence]
  simp only[sub_mul,mul_sub,smul_mul_assoc,mul_smul_comm]
  rw [actual_forward_native_momentum,forward_divergence]

/-- Every native P†cP term has an actual returned second-order action with its coefficient
kept between the original independent transpose and momentum. -/
theorem actual_forward_native_sandwich(t:ℝ)(ht:0≤t)(v w:Ambient)(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    sandwich v w b hb*sourceForwardCore t ht=
      sourceForwardCore t ht*(GaussMomentumAdjoint.adjoint v*
        multiply (fun z=>b (forwardPoint t z))
          (fun z=>(hb ⟨_,forward_chart t ht z⟩).comp z.val (forward_smooth t ht z))*
        covariantMomentum w):=by
  change (GaussMomentumAdjoint.adjoint v*multiply b hb*covariantMomentum w)*sourceForwardCore t ht=_
  calc
    _=GaussMomentumAdjoint.adjoint v*(multiply b hb*(covariantMomentum w*sourceForwardCore t ht)):=by noncomm_ring
    _=GaussMomentumAdjoint.adjoint v*(multiply b hb*sourceForwardCore t ht)*covariantMomentum w:=by
      rw [actual_forward_native_momentum];noncomm_ring
    _=(GaussMomentumAdjoint.adjoint v*sourceForwardCore t ht)*
        multiply (fun z=>b (forwardPoint t z))
          (fun z=>(hb ⟨_,forward_chart t ht z⟩).comp z.val (forward_smooth t ht z))*covariantMomentum w:=by
      rw [actual_forward_multiplier_transport];noncomm_ring
    _=_:=by rw [actual_forward_native_adjoint];noncomm_ring
end LowEnergy.FirstCurrentWholeVariance
