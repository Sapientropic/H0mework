import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiReverseClockProfilePayment
import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceClockPhiProfileNativeReturn
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.ReverseNativeClock
open GaussCoreHilbert GaussCoreDifferential GaussFockPair GaussHistoryHilbert GaussNativeForm GaussNativeEnergy GaussNativePotential
open SourceQuantumConfigurationHilbert SourceQuantumScalarChart SourceQuantumGaugeSliceCoordinates SourceQuantumFockGauge
open SourcePhysicalKineticSquare SourceClockPhiCombinedScalePressure SourceClockPhiNativeMatchedSource
open SourceClockPhiForwardNativeReturn SourceClockPhiCorrectedWeightTransport SourceClockPhiCorrectedGaussianPair
open SourceClockPhiProfileNativeReturn SourceClockPhiProfileLocalNativeReturn SourceClockPhiHeatLocalNativeGaussian
open SourceScalarDoubleCurrent SourceScalarVirialBulk SourceScalarEssentialBudget SourceScalarShiftedBulk
open SourceScalarPositiveBulkWard SourceHamiltonianVolume SourceInverseNoetherEnergy
open ClockPhiHeatCorrectedCovarianceSource MeasureTheory
open scoped ContDiff InnerProductSpace
private abbrev End:=QuantumTest→ₗ[ℂ]QuantumTest
private abbrev K(t:ℝ)(ht:0<t)(x:ℝ×ℝ):End:=correctedCompleteCore t ht x.1 x.2
private abbrev W(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ):End:=correctedProfileWeight t ht p q x.1 x.2
private abbrev U:End:=inverseVolumeAction
private abbrev D:End:=combinedGenerator
private abbrev M:End:=matchedTester
private abbrev B:End:=scalarBulkComplete
private abbrev Z:End:=reverseNativeClock
private abbrev γ:=ProbabilityTheory.gaussianReal 0 1
attribute [local irreducible] sourcePair embed scalarKinetic centeredAction vacuumLinearAction vacuumConstantAction scalarBulkComplete

private def scalarClockAtom:Fin 4→End:=![scalarKinetic,centeredAction,vacuumLinearAction,vacuumConstantAction]
private def scalarClockPower:Fin 4→ℝ:=![-2/3,4/3,4/3,4/3]
private def scalarClockDegree:Fin 4→ℝ:=![2,-2,-1,0]
private def scalarClockCoefficient:Fin 4→ℂ:=![-8,8,-8,2]
def scalarReverseClockSlope(t:ℝ)(ht:0<t)(f g:QuantumTest):ℂ:=
  ∑i:Fin 4,scalarClockCoefficient i*((-54:ℂ)*sourcePair (M f)
    (gaussianProfileWeight t ht (scalarClockPower i+scalarClockDegree i*(scalarClockDegree i-3)/18)
      (forwardUAction t ht.le (scalarClockAtom i g)))+
    (18*scalarClockDegree i:ℂ)*sourcePair (D f)
      (U (gaussianProfileWeight t ht (scalarClockPower i+scalarClockDegree i*(scalarClockDegree i-3)/18)
        (forwardUAction t ht.le (scalarClockAtom i g)))))
private theorem coeff_first(t ξ η:ℝ):∀x y:SourceCoordinateSlice,x.1=y.1→
    correctedCoefficient t ξ η x=correctedCoefficient t ξ η y:=by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  cases h
  rfl
private theorem scalar_bulk_atoms:B=(-8:ℂ) • (U*scalarKinetic)+(8:ℂ) • (U*centeredAction)-
    (8:ℂ) • (U*vacuumLinearAction)+(2:ℂ) • (U*vacuumConstantAction):=by
  have h:=original_bulk_complete_split
  rw [bulkAction,positiveBulk,original_filtered_bulk] at h
  simp only [mul_add,mul_sub,mul_smul_comm] at h
  linear_combination (norm:=module) -h
private theorem atom_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(i:Fin 4)(f g:QuantumTest):
    sourcePair (K t ht x f) (scalarClockAtom i (K t ht x g))=
      sourcePair f (W t ht (scalarClockPower i) (scalarClockDegree i) x (scalarClockAtom i g)):=by
  have h0:=actual_complete_profile_scalar_source t ht (correctedCoefficient t x.1 x.2)
    (coefficient_smooth t ht x.1 x.2) (coeff_first t x.1 x.2) f g
  have h1:=actual_profile_complete_centered_pair t ht (correctedCoefficient t x.1 x.2)
    (coefficient_smooth t ht x.1 x.2) (coeff_first t x.1 x.2) f g
  have h2:=actual_profile_complete_vacuum_linear_pair t ht (correctedCoefficient t x.1 x.2)
    (coefficient_smooth t ht x.1 x.2) (coeff_first t x.1 x.2) f g
  have h3:=actual_profile_complete_vacuum_constant_pair t ht (correctedCoefficient t x.1 x.2)
    (coefficient_smooth t ht x.1 x.2) (coeff_first t x.1 x.2) f g
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
private theorem inverse_profile(t:ℝ)(ht:0<t)(p q:ℝ)(x:ℝ×ℝ)(f:QuantumTest):
    forwardUAction t ht.le (W t ht p q x f)=W t ht p q x (forwardUAction t ht.le f):=by
  apply DFunLike.ext;intro z
  change (forwardU t z:ℂ) • ((((SourceClockPhiCoframeForwardCore.forwardRatio t z)^p*
    Real.exp (q*correctedCoefficient t x.1 x.2 z):ℝ):ℂ) • f z)=_
  exact smul_comm _ _ _
private theorem inverse_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(i:Fin 4)(f g:QuantumTest):
    sourcePair (K t ht x f) (U (scalarClockAtom i (K t ht x g)))=
      sourcePair f (W t ht (scalarClockPower i) (scalarClockDegree i) x
        (forwardUAction t ht.le (scalarClockAtom i g))):=by
  have hu:sourcePair (K t ht x f) (U (scalarClockAtom i (K t ht x g)))=
      sourcePair (U (K t ht x f)) (scalarClockAtom i (K t ht x g)):=multiply_pair _ _ _ _
  rw [hu]
  have h:=LinearMap.congr_fun (actual_corrected_complete_inverse_volume t ht x.1 x.2) f
  change U (K t ht x f)=K t ht x (forwardUAction t ht.le f) at h
  rw [h,atom_pair]
  have hp:=multiply_pair (forwardU t) (forwardU_smooth t ht.le) f
    (W t ht (scalarClockPower i) (scalarClockDegree i) x (scalarClockAtom i g))
  change sourcePair f (forwardUAction t ht.le (W t ht (scalarClockPower i) (scalarClockDegree i) x (scalarClockAtom i g)))=
    sourcePair (forwardUAction t ht.le f) (W t ht (scalarClockPower i) (scalarClockDegree i) x (scalarClockAtom i g)) at hp
  rw [←hp,inverse_profile]
private theorem scalar_pair(t:ℝ)(ht:0<t)(x:ℝ×ℝ)(f g:QuantumTest):
    sourcePair (bracket Z (K t ht x) f) (B (K t ht x g))=
      ∑i:Fin 4,scalarClockCoefficient i*sourcePair (reverseClockReturn t ht x.1 x.2 f)
        (W t ht (scalarClockPower i) (scalarClockDegree i) x (forwardUAction t ht.le (scalarClockAtom i g))):=by
  rw [actual_complete_reverse_clock_return,scalar_bulk_atoms]
  change sourcePair (K t ht x (reverseClockReturn t ht x.1 x.2 f)) _=_
  have hp(a b c:QuantumTest):sourcePair a (b+c)=sourcePair a b+sourcePair a c:=by simp only [sourcePair,map_add,inner_add_right]
  have hm(a b c:QuantumTest):sourcePair a (b-c)=sourcePair a b-sourcePair a c:=by simp only [sourcePair,map_sub,inner_sub_right]
  have hs(a b:QuantumTest)(c:ℂ):sourcePair a (c • b)=c*sourcePair a b:=by simp only [sourcePair,map_smul,inner_smul_right]
  simp only [LinearMap.add_apply,LinearMap.sub_apply,LinearMap.smul_apply,Module.End.mul_apply,hp,hm,hs]
  have hi:=inverse_pair t ht x
  have h0:=hi 0 (reverseClockReturn t ht x.1 x.2 f) g
  have h1:=hi 1 (reverseClockReturn t ht x.1 x.2 f) g
  have h2:=hi 2 (reverseClockReturn t ht x.1 x.2 f) g
  have h3:=hi 3 (reverseClockReturn t ht x.1 x.2 f) g
  norm_num [scalarClockAtom,scalarClockPower,scalarClockDegree,Matrix.cons_val] at h0 h1 h2 h3
  change sourcePair (K t ht x (reverseClockReturn t ht x.1 x.2 f)) (U (vacuumLinearAction (K t ht x g)))=
    sourcePair (reverseClockReturn t ht x.1 x.2 f) (W t ht (4/3) (-1) x (forwardUAction t ht.le (vacuumLinearAction g))) at h2
  change sourcePair (K t ht x (reverseClockReturn t ht x.1 x.2 f)) (U (vacuumConstantAction (K t ht x g)))=
    sourcePair (reverseClockReturn t ht x.1 x.2 f) (W t ht (4/3) 0 x (forwardUAction t ht.le (vacuumConstantAction g))) at h3
  rw [h0,h1,h2,h3]
  norm_num [scalarClockCoefficient,scalarClockAtom,scalarClockPower,scalarClockDegree,Fin.sum_univ_succ]
  ring

/-- The actual scalar Noether clock commutator has a source-generated Gaussian L1 price with an explicit factor t. All four scalar/vacuum sectors and both original noises are consumed. -/
theorem actual_reverse_scalar_clock_payment(t:ℝ)(ht:0<t)(f g:QuantumTest):
    Integrable (fun x:ℝ×ℝ=>sourcePair (bracket Z (K t ht x) f) (B (K t ht x g))) (γ.prod γ) ∧
    (∫x:ℝ×ℝ,sourcePair (bracket Z (K t ht x) f) (B (K t ht x g)) ∂γ.prod γ)=
      (t:ℂ)*scalarReverseClockSlope t ht f g:=by
  have h(i:Fin 4):=actual_reverse_clock_profile_payment t ht (scalarClockPower i) (scalarClockDegree i)
    f (forwardUAction t ht.le (scalarClockAtom i g))
  have hi(i:Fin 4):Integrable (fun x:ℝ×ℝ=>scalarClockCoefficient i*
      sourcePair (reverseClockReturn t ht x.1 x.2 f)
        (W t ht (scalarClockPower i) (scalarClockDegree i) x (forwardUAction t ht.le (scalarClockAtom i g)))) (γ.prod γ):=
    (h i).1.const_mul _
  simp_rw [scalar_pair]
  refine ⟨integrable_finsetSum Finset.univ (fun i _=>hi i),?_⟩
  rw [integral_finsetSum _ (fun i _=>hi i)]
  simp_rw [integral_const_mul,(h _).2]
  unfold scalarReverseClockSlope
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl;intro i _
  ring
end LowEnergy.ReverseNativeClock
