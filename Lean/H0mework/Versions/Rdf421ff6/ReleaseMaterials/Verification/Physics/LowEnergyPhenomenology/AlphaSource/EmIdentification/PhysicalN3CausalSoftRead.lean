import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalN3CausalResponseWindow

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.PhysicalN3CausalWindow
open GaussCoreHilbert CanonicalGradedSpatialSource ActualCompositeFieldCurrent
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift PreparationVacuumPhysicalFeedback
open PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumNoetherChart PreparationVacuumGaugeSourceInjection
open PreparationVacuumFieldPerturbation.Blocks PreparationVacuumFullPoleContinuation
open ActualEMJointCurrentMomentum ActualElectronPhysicalJointInverse ActualElectronWholeChargeSoft
open ActualElectronWholeNoetherObserver ActualDressedFullCoulomb ActualDressedNoether
open ActualElectronFullNoetherMixedSoft
open PreparationVacuumSourcePreparedResponse GaussComposite.SourceGraph
open SourcePropagationCommonMomentum SourcePropagationTimeDependentFeedback
open SourceFamilyHilbert SourceFamilyOperator Filter
open scoped Topology InnerProductSpace Matrix.Norms.Elementwise
open intervalIntegral
local instance softRationalOperators : NormedAlgebra ℚ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℚ ℂ _
local instance softRealOperators : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _
local instance softOperatorNorm : NormedAddCommGroup (H→L[ℂ]H):=ContinuousLinearMap.toNormedAddCommGroup
local instance softOperatorRealSpace : NormedSpace ℝ (H→L[ℂ]H):=softRealOperators.toNormedSpace
attribute [local irreducible] actualFullNoetherVariation jointResolvent jointCurrent jointGenerator jointHessian
  physicalTime noetherReader noetherReaderContact rawReaderContact timeSlope mixedVertex
  actualPhysicalEulerObserver actualElectronPhysicalState actualNoetherBackground
  physicalN3ResponseWindowOperator physicalN3ResponseWindow physicalN3FrameRead

private theorem laplace_weight_joint :
    Continuous (fun lt : ℂ×ℝ=>laplaceWeight lt.1 lt.2):=by
  unfold laplaceWeight
  fun_prop

/-- The window integrand is jointly continuous in transfer, Laplace coordinate and age. -/
theorem physical_n3_integrand_joint (event : DressedEvent) (reader force : Field289) :
    Continuous (fun p : (PhysicalMomentum× ℂ)×ℝ=>
      (laplaceWeight p.1.2 p.2)•actualFullNoetherVariation event (-p.1.1) reader force p.2):=by
  have weightpair : Continuous (fun p : (PhysicalMomentum× ℂ)×ℝ=>(p.1.2,p.2)):=by fun_prop
  have weight :=laplace_weight_joint.comp weightpair
  have fieldpair : Continuous (fun p : (PhysicalMomentum× ℂ)×ℝ=>(p.1.1,p.2)):=by fun_prop
  have field :=(physical_n3_variation_joint event reader force).comp fieldpair
  exact weight.smul field

/-- The finite window operator is jointly continuous in transfer and Laplace coordinate. -/
theorem physical_n3_window_operator_joint (event : DressedEvent) (T : ℝ) (reader force : Field289) :
    Continuous (fun kz : PhysicalMomentum× ℂ=>
      physicalN3ResponseWindowOperator event kz.1 kz.2 T reader force):=by
  unfold physicalN3ResponseWindowOperator
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (physical_n3_integrand_joint event reader force) 0 T

/-- The actual N3 scalar window is jointly continuous in transfer and Laplace coordinate. -/
theorem physical_n3_window_joint (event : DressedEvent) (leg : CompositeLeg) (T : ℝ)
    (reader force : Field289) :
    Continuous (fun kz : PhysicalMomentum× ℂ=>
      physicalN3ResponseWindow event leg kz.1 kz.2 T reader force):=by
  simpa only [physicalN3ResponseWindow,Function.comp_def] using
    (actualPhysicalEulerObserver event leg).continuous.comp
      (physical_n3_window_operator_joint event T reader force)

/-- The complete `289*289` window matrix is jointly continuous; no direction is sampled away. -/
theorem physical_n3_window_matrix_joint (event : DressedEvent) (leg : CompositeLeg) (T : ℝ) :
    Continuous (fun kz : PhysicalMomentum× ℂ=>
      physicalN3ResponseWindowMatrix event leg kz.1 kz.2 T):=by
  unfold physicalN3ResponseWindowMatrix
  exact continuous_pi fun i=>continuous_pi fun j=>
    physical_n3_window_joint event leg T (fieldUnit i) (fieldUnit j)

/-- Source continuity at `(0,0)` generates a positive radius covering the whole matrix at once.
This is an existence radius from continuity, not a computed numerical modulus. -/
theorem physical_n3_soft_radius (event : DressedEvent) (leg : CompositeLeg) (T : ℝ) (delta : ℝ)
    (positive : 0<delta) :
    ∃radius : ℝ,0<radius ∧ ∀kz : PhysicalMomentum× ℂ,‖kz‖<radius→
      ‖physicalN3ResponseWindowMatrix event leg kz.1 kz.2 T-
        physicalN3ResponseWindowMatrix event leg 0 0 T‖≤delta := by
  classical
  have joint :=(physical_n3_window_matrix_joint event leg T).continuousAt (x:=(0,0))
  have entryclose : ∀ij : Fin 289×Fin 289,∀ᶠ kz in 𝓝 (0,0),
      dist (physicalN3ResponseWindowMatrix event leg kz.1 kz.2 T ij.1 ij.2)
        (physicalN3ResponseWindowMatrix event leg 0 0 T ij.1 ij.2)<delta := by
    intro ij
    have tend : Tendsto
        (fun kz : PhysicalMomentum× ℂ=>
          physicalN3ResponseWindowMatrix event leg kz.1 kz.2 T ij.1 ij.2)
        (𝓝 (0,0))
        (𝓝 (physicalN3ResponseWindowMatrix event leg 0 0 T ij.1 ij.2)):=
      tendsto_pi_nhds.mp (tendsto_pi_nhds.mp joint ij.1) ij.2
    exact (Metric.tendsto_nhds.mp tend) delta positive
  have allclose :=(Filter.eventually_all (ι:=Fin 289×Fin 289)).mpr entryclose
  rw [nhds_prod_eq] at allclose
  obtain ⟨U,hU,V,hV,hUV⟩:=Filter.mem_prod_iff.mp allclose
  obtain ⟨ru,pru,hru⟩:=Metric.mem_nhds_iff.mp hU
  obtain ⟨rv,prv,hrv⟩:=Metric.mem_nhds_iff.mp hV
  refine ⟨min ru rv,lt_min pru prv,fun kz small=>?_⟩
  refine (Matrix.norm_le_iff positive.le).mpr fun i j=> ?_
  have inside :=hUV ⟨hru (mem_ball_zero_iff.mpr
      ((norm_fst_le kz).trans_lt (small.trans_le (min_le_left ru rv)))),
    hrv (mem_ball_zero_iff.mpr
      ((norm_snd_le kz).trans_lt (small.trans_le (min_le_right ru rv))))⟩ (i,j)
  rw [dist_eq_norm] at inside
  simpa only [Pi.sub_apply,Matrix.sub_apply] using inside.le

/-- The joint physical ray `k=eps^2•n`, `lambda=-i*eps^2*s` tends to the zero-transfer,
zero-Laplace endpoint; `n` and `s` are arbitrary, no unit or nonzero witness is needed. -/
theorem physical_n3_soft_ray (event : DressedEvent) (leg : CompositeLeg) (T : ℝ)
    (n : PhysicalMomentum) (s : ℝ) :
    Tendsto (fun eps : ℝ=>physicalN3ResponseWindowMatrix event leg ((eps^2)•n)
      (-Complex.I*((eps^2*s:ℝ):ℂ)) T) (𝓝 0)
      (𝓝 (physicalN3ResponseWindowMatrix event leg 0 0 T)) := by
  have curve : Continuous (fun eps : ℝ=>
      ((eps^2)•n,(-Complex.I)*((eps^2*s:ℝ):ℂ))):=by
    apply Continuous.prodMk
    · exact (continuous_pow 2).smul continuous_const
    · exact (Complex.continuous_ofReal.comp
        ((continuous_pow 2).mul (continuous_const (y:=s)))).const_mul (-Complex.I)
  have origin : Tendsto (fun eps : ℝ=>((eps^2)•n,(-Complex.I)*((eps^2*s:ℝ):ℂ))) (𝓝 0)
      (𝓝 ((0,0):PhysicalMomentum× ℂ)):=by
    have h : (fun eps : ℝ=>((eps^2)•n,(-Complex.I)*((eps^2*s:ℝ):ℂ))) 0=(0,0):=by simp
    simpa only [h] using curve.tendsto 0
  exact (physical_n3_window_matrix_joint event leg T).continuousAt.tendsto.comp origin

/-- Along the nonzero branch the quadratic transfer stays nonzero. -/
theorem physical_n3_ray_nonzero (n : PhysicalMomentum) (nonzero : n≠0) (eps : ℝ) (off : eps≠0) :
    (eps^2)•n≠0:=smul_ne_zero (pow_ne_zero 2 off) nonzero

end LowEnergy.GaussComposite.PhysicalN3CausalWindow
