import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualSoftFiniteResponse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteObservationSoftReturn
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedEnergyVariation
open PreparationPhysicalChargedEnergyPoleReturn PreparationPhysicalChargedPacketQuantumReturn
open PreparationPhysicalChargedPacketVoltage PreparationVacuumVoltageGaussGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumActionFieldLift
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open PreparationVacuumOriginalGreenFeedback PreparationVacuumPhysicalChargedFieldFactor
open PreparationVacuumChargedLongRangeRead PreparationVacuumCausalPoleResponse
open PreparationVacuumChargedSpatialResponse PreparationVacuumNativeSlowCoupling
open PreparationVacuumFullSlowFieldResponse PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedPacketGreen
open PreparationVacuumPhysicalQuantumLockedCharge PreparationVacuumElectromagneticIdentity
open CanonicalGradedSpatialSource FullQuantum.CoframeResponse FullQuantum.StateGreen
open GaussHistoryHilbert PreparationVacuumStaticVoltageSource
open MeasureTheory Filter
open scoped BigOperators Matrix Topology InnerProductSpace
local instance finiteObservationPriceIndex : DecidableEq Quantum.Index:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open Stage10 DiracCliffordRepresentation DiracExteriorMatterAction YangMills.FullPairing
open PreparationPhysicalEnergyWeightsReturn PreparationPhysicalFilteredChargeVoltage
open PreparationPhysicalVoltageEnergyIdentity

open PreparationPhysicalEnergyPoleChargeReturn
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource StageNineHolonomicField
open FullQuantum.Triangular

open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationVacuumMixedFieldReturn GaussComposite.PhysicalFullFieldScattering
open Electromagnetic.CanonicalCoframe

open PreparationPhysicalChargedHamiltonianRead PreparationPhysicalChargedScatteringPoleReturn

open PreparationPhysicalChargedVertexDomainReturn PreparationPhysicalChargedScatteringFourierReturn

open PreparationPhysicalChargedScatteringDomainPrice

open PreparationVacuumSoftPoleSelection PreparationVacuumNativePoleTensor PreparationVacuumSharedPoleCarrier
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic PreparationVacuumWholeOrigin

open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalScatteringFrequencyWard

open Stage10.CanonicalMatter StageNineCurrentCoframeMatterTemporalPrincipal
open PreparationVacuumGaugeSourceInjection GaussNativeMatter SourceQuantumFockGauge
open SourceQuantumGaugeSliceCoordinates SU7MotherLieAlgebra


open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace YangMills.FullPairing Stage9C.Material.SpinPair
open PreparationPhysicalNativeOriginPhaseWard PreparationPhysicalNativePoleChargeReturn
open PreparationPhysicalEnergyCurrentWardReturn PreparationPhysicalChargedSoftObservable
open PreparationPhysicalChargedPacketQuantumReturn PreparationPhysicalChargedSoftScatteringReturn
open PreparationPhysicalNormalizedFullField PreparationVacuumOriginalGreenFeedback
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open Electromagnetic.CanonicalCoframe FullQuantum.Triangular
open MeasureTheory Filter
open scoped Topology InnerProductSpace

open PreparationPhysicalNativeSoftWardBoundary
open Set

open PreparationPhysicalFinitePoleVertices PreparationPhysicalFiniteOriginCovariance
open PreparationPhysicalNativePhotonFluxReturn PreparationPhysicalNativeWardFiniteObservation
open PreparationPhysicalNativePolarizationEmitter


private def readerPair (x : SourceFieldParameters) : TransferPair:=originalTransferPair x.1.1.1 x.1.1.2
private def forcePair (x : SourceFieldParameters) : TransferPair:=originalTransferPair x.1.2.1 x.1.2.2

def sourceParameterPair (sideL edgeL sideR edgeR : Fin 2) (x : SourceFieldParameters) (time age : ℝ) : ℂ × ℂ :=
  sourcePreparedScatteringPair sideL edgeL sideR edgeR (readerPair x) (forcePair x) x.2 time age

/-- The baseline price retains the complete source coefficients, physical transfer and original direct contact. -/
def sourceParameterPrice (sideL edgeL sideR edgeR : Fin 2) (x : SourceFieldParameters) : ℝ × ℝ :=
  sourceScatteringPairDomainPrice sideL edgeL sideR edgeR (readerPair x) (forcePair x) x.2 0 0

private theorem density_continuous : Continuous (fun v : Fin 289→ℂ=>complexCoefficients (originalComplexDirection v)) := by
  apply continuous_pi
  intro i
  have identity (v : Fin 289→ℂ) : complexCoefficients (originalComplexDirection v) i=
      realDensityCoefficients i (fun j=>(v j).re)+Complex.I • realDensityCoefficients i (fun j=>(v j).im) := by
    simp only [complexCoefficients,originalComplexDirection,realDensityCoefficients_source]
  simp_rw [identity]
  exact ((LinearMap.continuous_of_finiteDimensional (realDensityCoefficients i)).comp
    (continuous_pi fun j=>Complex.continuous_re.comp (continuous_apply j))).add
    (((LinearMap.continuous_of_finiteDimensional (realDensityCoefficients i)).comp
      (continuous_pi fun j=>Complex.continuous_im.comp (continuous_apply j))).const_smul Complex.I)

private theorem frequency_continuous : Continuous (fun v : Fin 289→ℂ=>complexFrequencyCoefficients (originalComplexDirection v)) := by
  apply continuous_pi
  intro k
  simp_rw [sourceScatteringFrequency_complex]
  exact continuous_finsetSum _ fun j _=>(continuous_apply j).smul continuous_const

private theorem shifted_continuous :
    Continuous (fun x : (Fin 4→FiberOperators) × PhysicalMomentum=>shiftCoefficients x.1 x.2) := by
  apply continuous_pi
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [shiftCoefficients,Fin.cases_zero]
    exact ((continuous_apply 0).comp continuous_fst).add
      (continuous_finsetSum _ fun j _=>
        (Complex.continuous_ofReal.comp ((continuous_apply j).comp continuous_snd)).smul
          ((continuous_apply j.succ).comp continuous_fst))
  | succ j =>
    simp only [shiftCoefficients,Fin.cases_succ]
    exact (continuous_apply _).comp continuous_fst

private theorem adjoint_continuous : Continuous (fun A : Fin 4→FiberOperators=>adjointCoefficients A) :=
  continuous_pi fun i=>ContinuousLinearMap.adjoint.continuous.comp (continuous_apply i)

private theorem reader_continuous : Continuous (fun x : SourceFieldParameters=>realReaderCoefficients (readerPair x) x.2) := by
  have identity : (fun x : SourceFieldParameters=>realReaderCoefficients (readerPair x) x.2)=
      fun x=>(2:ℂ)⁻¹ • (complexCoefficients (originalComplexDirection x.1.1.2)+
        adjointCoefficients (shiftCoefficients (complexCoefficients (originalComplexDirection x.1.1.1)) (-x.2))) := by
    funext x i
    simp only [readerPair,realReaderCoefficients,originalTransferPair,Pi.smul_apply,Pi.add_apply]
  rw [identity]
  exact ((density_continuous.comp continuous_fst.fst.snd).add
    (adjoint_continuous.comp (shifted_continuous.comp
      ((density_continuous.comp continuous_fst.fst.fst).prodMk continuous_snd.neg)))).const_smul ((2:ℂ)⁻¹)

private theorem backward_continuous : Continuous (fun x : SourceFieldParameters=>
    shiftCoefficients (adjointCoefficients (complexFrequencyCoefficients (forcePair x).negative)) x.2) :=
  shifted_continuous.comp ((adjoint_continuous.comp
    (frequency_continuous.comp continuous_fst.snd.snd)).prodMk continuous_snd)

/-- The baseline is a continuous scalar of the actual four full fields and their common physical transfer. -/
theorem sourceParameterPrice_continuous (sideL edgeL sideR edgeR : Fin 2) :
    Continuous (sourceParameterPrice sideL edgeL sideR edgeR) := by
  have firstShift:=shifted_continuous.comp (backward_continuous.prodMk continuous_snd.neg)
  have secondShift:=shifted_continuous.comp (reader_continuous.prodMk continuous_snd)
  have frequency:=frequency_continuous.comp (continuous_fst.snd.fst : Continuous (fun x : SourceFieldParameters=>x.1.2.1))
  have mixed (j : Fin 4) : Continuous (fun x : SourceFieldParameters=>realMixedCoefficients (readerPair x) (forcePair x) j) :=
    (realMixedCoefficients_joint_cts j).comp continuous_fst
  unfold sourceParameterPrice sourceScatteringPairDomainPrice sourceOrderedSumPrice sourceOrderedCARPrice
    sourceOrderedInteriorPrice sourceContactDomainPrice sourceContactInteriorPrice
  simp only [sourceScatteringGrowth,abs_zero,sub_self,zero_mul,add_zero,one_mul,mul_one]
  apply Continuous.prodMk
  · apply Continuous.add
    · apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact ((((continuous_apply i).comp firstShift).norm.mul
        (((continuous_apply j).comp reader_continuous).norm)).mul_const
          (sourceScatteringLegPrice sideR edgeR j)).const_mul (sourceScatteringLegPrice sideL edgeL i)
    · apply continuous_finsetSum
      intro i _
      apply continuous_finsetSum
      intro j _
      exact ((((continuous_apply i).comp secondShift).norm.mul
        (((continuous_apply j).comp frequency).norm)).mul_const
          (sourceScatteringLegPrice sideR edgeR j)).const_mul (sourceScatteringLegPrice sideL edgeL i)
  · apply continuous_finsetSum
    intro j _
    exact ((mixed j).norm).mul_const (sourceScatteringLegPrice sideR edgeR j)

private theorem growth_bound (T r : ℝ) (future : 0 ≤ T) (bound : |r| ≤ T) :
    sourceScatteringGrowth r ≤ sourceScatteringGrowth T := by
  simp only [sourceScatteringGrowth,sourceRate,abs_of_nonneg future]
  have scaled:=_root_.mul_le_mul_of_nonneg_right bound (norm_nonneg (operator (interaction actual 0)))
  linarith

private theorem ordered_bound (sideL edgeL sideR edgeR : Fin 2)
    (A B : Fin 4→FiberOperators) (shift : PhysicalMomentum) (T t a : ℝ) (i j : Fin 4)
    (future : 0 ≤ T) (ht : |t| ≤ T) (ha : |a| ≤ T) (hd : |t-a| ≤ T) :
    sourceOrderedCARPrice sideL edgeL sideR edgeR A B shift t a i j ≤
      (sourceScatteringGrowth T)^3*sourceOrderedCARPrice sideL edgeL sideR edgeR A B shift 0 0 i j := by
  have left:=sourceScatteringLegPrice_nonnegative sideL edgeL i
  have right:=sourceScatteringLegPrice_nonnegative sideR edgeR j
  have gt:=growth_bound T t future ht
  have ga:=growth_bound T a future ha
  have gd:=growth_bound T (t-a) future hd
  have positive : 0 ≤ sourceScatteringGrowth T:=by unfold sourceScatteringGrowth sourceRate; positivity
  calc
    _ ≤ sourceScatteringLegPrice sideL edgeL i*
      (sourceScatteringGrowth T*‖shiftCoefficients A shift i‖*sourceScatteringGrowth T*‖B j‖*
        sourceScatteringGrowth T*sourceScatteringLegPrice sideR edgeR j) := by
      unfold sourceOrderedCARPrice sourceOrderedInteriorPrice
      gcongr <;> unfold sourceScatteringGrowth sourceRate <;> positivity
    _=_ := by
      simp only [sourceOrderedCARPrice,sourceOrderedInteriorPrice,sourceScatteringGrowth,abs_zero,
        sub_self,zero_mul,add_zero,one_mul,mul_one]
      ring

/-- Both ordered terms and the independent contact retain the original complete source price on the compact age window. -/
theorem sourceParameterPair_window_bound (sideL edgeL sideR edgeR : Fin 2)
    (x : SourceFieldParameters) (T age : ℝ) (future : 0 ≤ T) (window : age∈Icc 0 T) :
    ‖(sourceParameterPair sideL edgeL sideR edgeR x T age).1‖ ≤
      (sourceScatteringGrowth T)^3*(sourceParameterPrice sideL edgeL sideR edgeR x).1 ∧
    ‖(sourceParameterPair sideL edgeL sideR edgeR x T age).2‖ ≤
      (sourceScatteringGrowth T)^2*(sourceParameterPrice sideL edgeL sideR edgeR x).2 := by
  have actual:=sourcePreparedScatteringPair_domain_bound sideL edgeL sideR edgeR (readerPair x) (forcePair x) x.2 T age
  constructor
  · refine actual.1.trans ?_
    have ht : |T| ≤ T:=by rw [abs_of_nonneg future]
    have ha : |age| ≤ T:=by rw [abs_of_nonneg window.1]; exact window.2
    have hd : |T-age| ≤ T:=by rw [abs_of_nonneg (sub_nonneg.mpr window.2)]; linarith [window.1]
    have hd' : |age-T| ≤ T:=by simpa only [abs_sub_comm] using hd
    unfold sourceParameterPrice sourceScatteringPairDomainPrice sourceOrderedSumPrice
    simp only [mul_add,Finset.mul_sum]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _=>ordered_bound sideL edgeL sideR edgeR _ _ _ T age T i j future ha ht hd'
    · apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum fun j _=>ordered_bound sideL edgeL sideR edgeR _ _ _ T T age i j future ht ha hd
  · refine actual.2.trans_eq ?_
    simp only [sourceParameterPrice,sourceScatteringPairDomainPrice,sourceContactDomainPrice,
      sourceContactInteriorPrice,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [sourceScatteringGrowth,abs_zero,zero_mul,add_zero,one_mul,mul_one]
    ring

/-- The generated limit coefficient price fixes the eventual envelope; no uniform bound is supplied. -/
def sourceUniformObservationPrice (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (T : ℝ) : ℝ × ℝ :=
  ((sourceScatteringGrowth T)^3*((sourceParameterPrice sideL edgeL sideR edgeR (sourceActualSoftParametersLimit legs branch)).1+1),
   (sourceScatteringGrowth T)^2*((sourceParameterPrice sideL edgeL sideR edgeR (sourceActualSoftParametersLimit legs branch)).2+1))

theorem sourceActualUniformObservation_bound (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (T : ℝ) (future : 0 ≤ T) (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    ∀ᶠ e in scaleApproach,∀age∈Icc 0 T,
      ‖(sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1‖ ≤
        (sourceUniformObservationPrice sideL edgeL sideR edgeR legs branch T).1 ∧
      ‖(sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).2‖ ≤
        (sourceUniformObservationPrice sideL edgeL sideR edgeR legs branch T).2 := by
  have generated:=(sourceParameterPrice_continuous sideL edgeL sideR edgeR).tendsto
    (sourceActualSoftParametersLimit legs branch) |>.comp (sourceActualSoftParameters_tendsto legs branch n unit nonrealL nonrealR)
  have first:=((continuous_fst.tendsto _).comp generated).eventually (eventually_lt_nhds (lt_add_one
    (sourceParameterPrice sideL edgeL sideR edgeR (sourceActualSoftParametersLimit legs branch)).1))
  have second:=((continuous_snd.tendsto _).comp generated).eventually (eventually_lt_nhds (lt_add_one
    (sourceParameterPrice sideL edgeL sideR edgeR (sourceActualSoftParametersLimit legs branch)).2))
  have positive : 0 ≤ sourceScatteringGrowth T:=by unfold sourceScatteringGrowth sourceRate; positivity
  filter_upwards [first,second] with e firstBound secondBound
  intro age window
  have price:=sourceParameterPair_window_bound sideL edgeL sideR edgeR
    (sourceActualSoftParameters legs branch n unit e) T age future window
  exact ⟨price.1.trans (mul_le_mul_of_nonneg_left firstBound.le (pow_nonneg positive 3)),
    price.2.trans (mul_le_mul_of_nonneg_left secondBound.le (pow_nonneg positive 2))⟩

end LowEnergy.PreparationPhysicalFiniteObservationSoftReturn
