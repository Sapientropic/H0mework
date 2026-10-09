import H0mework.Versions.AB.Physics.LowEnergy.Quantum.SourceCoframeVolume
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceCoframeCovariantAction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ClockPhiHeatRadialCovariancePair
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourceCoframeVolume SourceCoframeCovariantAction
open scoped ContDiff Topology InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest

def radialColumn(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(i:Fin 6):End:=
  Complex.I • (multiply b hb*gradientAction i)
def radialPrice(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):End:=
  multiply (fun z=>(3*sourceTime 0/4)*volume z*b z^2)
    (fun z=>(contDiffAt_const.mul volume_smooth.contDiffAt).mul ((hb z).pow 2))
private theorem volume_radial(z:SourceCoordinateSlice):
    (∑i:Fin 6,volumeGradient z i*z.1 i)=3*volume z:=by
  simp [volumeGradient,volume,Fin.sum_univ_succ]
  ring
private theorem radial_coefficient(z:physicalChart)(b:ℝ):
    (∑i:Fin 6,∑j:Fin 6,volumeGradient z.val i*b*GaussCoframeKinetic.coefficient i j z.val*b*volumeGradient z.val j)=
      (3*sourceTime 0/4)*volume z.val*b^2:=by
  calc
    _=b^2*(∑i:Fin 6,volumeGradient z.val i*(∑j:Fin 6,GaussCoframeKinetic.coefficient i j z.val*volumeGradient z.val j)):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _=b^2*(∑i:Fin 6,volumeGradient z.val i*((sourceTime 0/4)*z.val.1 i)):=by
      simp_rw [coefficient_volume z]
    _=b^2*((sourceTime 0/4)*(∑i:Fin 6,volumeGradient z.val i*z.val.1 i)):=by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=_:=by rw [volume_radial];ring
private theorem radial_operator(b:SourceCoordinateSlice→ℝ)(hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val):
    (∑i:Fin 6,∑j:Fin 6,gradientAction i*multiply b hb*metricAction i j*multiply b hb*gradientAction j)=radialPrice b hb:=by
  apply LinearMap.ext
  intro f
  apply DFunLike.ext
  intro z
  by_cases hz:z∈physicalChart
  · apply PiLp.ext
    intro word
    simp only [LinearMap.sum_apply,Module.End.mul_apply]
    change (∑i:Fin 6,∑j:Fin 6,(volumeGradient z i:ℂ)*((b z:ℂ)*((GaussCoframeKinetic.coefficient i j z:ℂ)*((b z:ℂ)*((volumeGradient z j:ℂ)*f z word)))))=
      (((3*sourceTime 0/4)*volume z*b z^2:ℝ):ℂ)*f z word
    have he:(∑i:Fin 6,∑j:Fin 6,((volumeGradient z i:ℂ)*(b z:ℂ)*(GaussCoframeKinetic.coefficient i j z:ℂ)*(b z:ℂ)*(volumeGradient z j:ℂ)))=
        (((3*sourceTime 0/4)*volume z*b z^2:ℝ):ℂ):=by
      exact_mod_cast radial_coefficient ⟨z,hz⟩ (b z)
    calc
      _=(∑i:Fin 6,∑j:Fin 6,((volumeGradient z i:ℂ)*(b z:ℂ)*(GaussCoframeKinetic.coefficient i j z:ℂ)*(b z:ℂ)*(volumeGradient z j:ℂ)))*f z word:=by
        simp only [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _=_:=by rw [he]
  · have h0(q:QuantumTest):q z=0:=image_eq_zero_of_notMem_tsupport (fun h=>hz (q.tsupport_subset h))
    exact (h0 _).trans (h0 _).symm

theorem actual_radial_covariance_pair(b:SourceCoordinateSlice→ℝ)
    (hb:∀z:physicalChart,ContDiffAt ℝ ∞ b z.val)(f g:QuantumTest):
    (∑i:Fin 6,∑j:Fin 6,sourcePair (radialColumn b hb i f) (metricAction i j (radialColumn b hb j g)))=
      sourcePair f (radialPrice b hb g):=by
  have he(i j:Fin 6):sourcePair (radialColumn b hb i f) (metricAction i j (radialColumn b hb j g))=
      sourcePair f ((gradientAction i*multiply b hb*metricAction i j*multiply b hb*gradientAction j) g):=by
    simp only [radialColumn,LinearMap.smul_apply,Module.End.mul_apply,map_smul,
      sourcePair,inner_smul_left,inner_smul_right,Complex.conj_I]
    have hs(p q:QuantumTest):Complex.I*((-Complex.I)*sourcePair p q)=sourcePair p q:=by
      rw [←mul_assoc,mul_neg,Complex.I_mul_I,neg_neg,one_mul]
    change Complex.I*((-Complex.I)*sourcePair (multiply b hb (gradientAction i f))
      (metricAction i j (multiply b hb (gradientAction j g))))=sourcePair f _
    rw [hs]
    rw [←multiply_pair]
    exact (multiply_pair _ _ f _).symm
  simp_rw [he]
  have h:=congrArg (fun T:End=>sourcePair f (T g)) (radial_operator b hb)
  simpa only [LinearMap.sum_apply,sourcePair,map_sum,inner_sum] using h
end LowEnergy.ClockPhiHeatRadialCovariancePair
