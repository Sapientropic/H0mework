import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeWardL2

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNativeSoftWardBoundary
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
local instance chargedSoftObservableQuantumIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

private theorem shifted_zero (time : ℝ) : shiftFlow 0 time=spatialFlow 0 time := by
  apply ContinuousLinearMap.ext
  intro v
  apply fourier.injective
  apply Lp.ext
  filter_upwards [shiftFlow_fourier 0 time v,spatialFlow_fourier_ae 0 time v] with k shifted original
  simp only [Pi.zero_apply,add_zero] at shifted
  exact shifted.trans original.symm

private theorem flow_group (t s : ℝ) : spatialFlow 0 t*spatialFlow 0 s=spatialFlow 0 (t+s) := by
  apply ContinuousLinearMap.ext
  intro v
  exact (spatialFlow_add 0 t s v).symm

private theorem compLp_smul (c : ℂ) (A : FiberOperators) :
    (c • A).compLpL 2 (volume:Measure Position)=c • A.compLpL 2 (volume:Measure Position) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [(c • A).coeFn_compLpL v,A.coeFn_compLpL v,Lp.coeFn_smul c (A.compLpL 2 (volume:Measure Position) v)] with k lhs rhs scaled
  simp only [smul_apply,lhs,scaled,rhs,Pi.smul_apply]

private theorem compLp_add (A B : FiberOperators) :
    (A+B).compLpL 2 (volume:Measure Position)=A.compLpL 2 (volume:Measure Position)+B.compLpL 2 (volume:Measure Position) := by
  apply ContinuousLinearMap.ext
  intro v
  apply Lp.ext
  filter_upwards [(A+B).coeFn_compLpL v,A.coeFn_compLpL v,B.coeFn_compLpL v,
    Lp.coeFn_add (A.compLpL 2 (volume:Measure Position) v) (B.compLpL 2 (volume:Measure Position) v)] with k lhs first second both
  simp only [add_apply,lhs,both,first,second,Pi.add_apply]

private def conjugate (A : FiberOperators) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  spatialFlow 0 (-time)*A.compLpL 2 (volume:Measure Position)*spatialFlow 0 time

private theorem conjugate_smul (c : ℂ) (A : FiberOperators) (time : ℝ) :
    conjugate (c • A) time=c • conjugate A time := by
  simp only [conjugate,compLp_smul,mul_smul_comm,smul_mul_assoc]

private theorem conjugate_add (A B : FiberOperators) (time : ℝ) :
    conjugate (A+B) time=conjugate A time+conjugate B time := by
  simp only [conjugate,compLp_add,mul_add,add_mul]

private theorem ordered_conjugate (A B : FiberOperators) (time age : ℝ) :
    sourceSoftOrderedOperator A B time age=conjugate A time*conjugate B age := by
  unfold sourceSoftOrderedOperator conjugate
  rw [shifted_zero,sub_eq_add_neg,←flow_group]
  simp only [mul_assoc]

/-- The actual Yukawa correction under the same complete propagation. -/
def sourceWardDefect (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2:=conjugate sourceWardDualDefect time

/-- The density reader keeps both signed, independent complex amplitudes. -/
def sourceWardReader (positive negative : ℂ) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2:=
  conjugate (sourceSoftNoetherReader 0 positive negative) time

private theorem dual_current (time : ℝ) :
    conjugate (sourceNativeOriginCanonicalFiber 0).adjoint time=
      sourceWardCurrent true time+sourceWardDefect time := by
  have split : (sourceNativeOriginCanonicalFiber 0).adjoint=sourceWardInsertion true+sourceWardDualDefect:=by
    simp only [sourceWardInsertion,ite_true,sub_add_cancel]
  rw [split]
  simp only [conjugate,sourceWardCurrent,sourceWardDefect,compLp_add,mul_add,add_mul]

/-- The time reader is generated by actual preparation derivatives, with its original full-Y remainder. -/
theorem sourceWardReader_preparation (ap an : ℂ) (time : ℝ) (v : FullMatterL2) :
    sourceWardReader ap an time v=
      (-Complex.I/2) • (an • deriv (fun t=>sourceWardSpatial false t v) time+
        star ap • deriv (fun t=>sourceWardSpatial true t v) time)+
      (star ap/2) • sourceWardDefect time v := by
  rw [(sourceWardSpatial_derivative false v time).deriv,(sourceWardSpatial_derivative true v time).deriv]
  have read : sourceWardReader ap an time v=
      (2:ℂ)⁻¹ • (an • sourceWardCurrent false time v+
        star ap • (sourceWardCurrent true time v+sourceWardDefect time v)) := by
    unfold sourceWardReader sourceSoftNoetherReader
    rw [conjugate_smul,conjugate_add,conjugate_smul,conjugate_smul,dual_current]
    rfl
  rw [read]
  have cancel (c : ℂ) : (-Complex.I/2)*(c*Complex.I)=(2:ℂ)⁻¹*c := by
    calc
      _= -(Complex.I*Complex.I)*(c/2):=by ring
      _=_:=by rw [Complex.I_mul_I]; ring
  simp only [smul_add,smul_smul,cancel]
  module

/-- Initial and final source preparations, plus the complete negative-frequency defect integral. -/
def sourceSoftExternalBoundary (u v : FullMatterL2) (ap an bp bn : ℂ) (time age : ℝ) : ℂ :=
  -star bn*inner ℂ u ((sourceWardSpatial true age-sourceWardSpatial true 0) (sourceWardReader ap an time v))+
  bp*inner ℂ u (sourceWardReader ap an time ((sourceWardSpatial false age-sourceWardSpatial false 0) v))-
  (Complex.I*star bn)*(∫s in (0:ℝ)..age,inner ℂ u (sourceWardDefect s (sourceWardReader ap an time v)))

private theorem defect_continuous (v : FullMatterL2) : Continuous (fun t=>sourceWardDefect t v) := by
  exact sourceWardConjugate_continuous sourceWardDualDefect v

private theorem soft_current (ap an bp bn : ℂ) (time age : ℝ) :
    sourceSoftNoetherOperator 0 ap an bp bn time age=
      Complex.I • ((-star bn) • ((sourceWardCurrent true age+sourceWardDefect age)*sourceWardReader ap an time)+
        bp • (sourceWardReader ap an time*sourceWardCurrent false age)) := by
  rw [sourceSoftNoetherOperator,ordered_conjugate,ordered_conjugate]
  simp only [map_smulₛₗ,conjugate_smul,dual_current,smul_mul_assoc,mul_smul_comm]
  change Complex.I • ((-star bn) • ((sourceWardCurrent true age+sourceWardDefect age)*sourceWardReader ap an time)-
    (-bp) • (sourceWardReader ap an time*sourceWardCurrent false age))=_
  rw [neg_smul bp,sub_neg_eq_add]

/-- The two original ordered vertices are exactly the age derivative of actual preparation boundaries. -/
theorem sourceSoftExternalBoundary_derivative (u v : FullMatterL2) (ap an bp bn : ℂ) (time age : ℝ) :
    HasDerivAt (sourceSoftExternalBoundary u v ap an bp bn time)
      (inner ℂ u (sourceSoftNoetherOperator 0 ap an bp bn time age v)) age := by
  let R:=sourceWardReader ap an time
  have left:=((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age
    ((sourceWardSpatial_derivative true (R v) age).sub_const (sourceWardSpatial true 0 (R v)))
  have right:=(((innerSL ℂ u).comp R).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt age
    ((sourceWardSpatial_derivative false v age).sub_const (sourceWardSpatial false 0 v))
  have continuous:Continuous (fun s=>inner ℂ u (sourceWardDefect s (R v))):=
    continuous_const.inner (defect_continuous (R v))
  have correction:=intervalIntegral.integral_hasDerivAt_right
    (continuous.intervalIntegrable (0:ℝ) age)
    continuous.aestronglyMeasurable.stronglyMeasurableAtFilter continuous.continuousAt
  have generated:=((left.const_mul (-star bn)).add (right.const_mul bp)).sub
    (correction.const_mul (Complex.I*star bn))
  convert! generated using 1
  change inner ℂ u (sourceSoftNoetherOperator 0 ap an bp bn time age v)=
    (-star bn)*inner ℂ u (Complex.I • sourceWardCurrent true age (R v))+
    bp*inner ℂ u (R (Complex.I • sourceWardCurrent false age v))-
    (Complex.I*star bn)*inner ℂ u (sourceWardDefect age (R v))
  rw [soft_current]
  simp only [smul_apply,mul_apply_eq_comp,add_apply,inner_smul_right,inner_add_right,map_smul,R]
  ring

/-- The original ordered age integral returns the actual endpoint preparations and the full defect integral. -/
theorem sourceSoftExternalBoundary_integral (u v : FullMatterL2) (ap an bp bn : ℂ) (time age : ℝ) :
    (∫s in (0:ℝ)..age,inner ℂ u (sourceSoftNoetherOperator 0 ap an bp bn time s v))=
      sourceSoftExternalBoundary u v ap an bp bn time age := by
  have continuous : Continuous (fun s=>inner ℂ u (sourceSoftNoetherOperator 0 ap an bp bn time s v)) := by
    have first:=((continuous_const (y:=u)).inner ((sourceWardCurrent_continuous true
      (sourceWardReader ap an time v)).add (defect_continuous (sourceWardReader ap an time v)))).const_mul (-star bn)
    have second:=((continuous_const (y:=u)).inner ((sourceWardReader ap an time).continuous.comp
      (sourceWardCurrent_continuous false v))).const_mul bp
    simpa only [soft_current,Pi.add_apply,Function.comp_apply,smul_apply,add_apply,mul_apply_eq_comp,inner_smul_right,inner_add_right] using
      (first.add second).const_mul Complex.I
  have generated:=intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _=>sourceSoftExternalBoundary_derivative u v ap an bp bn time s)
    (continuous.intervalIntegrable (0:ℝ) age)
  simpa only [sourceSoftExternalBoundary,sub_self,zero_apply,map_zero,inner_zero_right,mul_zero,
    intervalIntegral.integral_same,add_zero,sub_zero] using generated

private theorem zero_compLp : (0:FiberOperators).compLpL 2 (volume:Measure Position)=(0:FullMatterL2→L[ℂ]FullMatterL2) := by
  apply norm_eq_zero.mp
  exact le_antisymm (by simpa only [norm_zero] using ((0:FiberOperators).norm_compLpL_le (p:=2) (μ:=volume)))
    (norm_nonneg _)

private theorem zero_scalar (A : FiberOperators) : (0:ℂ) • A=0 := by
  apply ContinuousLinearMap.ext
  intro v
  exact _root_.zero_smul ℂ (A v)

private theorem scalar_zero (c : ℂ) : c • (0:FiberOperators)=0 :=
  @_root_.smul_zero ℂ FiberOperators _ _ c

private theorem soft_zero (branch : Fin 2) (time age : ℝ) :
    sourceSoftNoetherOperator branch 0 0 0 0 time age=0 := by
  simp only [sourceSoftNoetherOperator,sourceSoftNoetherReader,neg_zero,zero_scalar,scalar_zero,_root_.star_zero,map_zero,
    add_zero,sourceSoftOrderedOperator,zero_compLp,mul_zero,zero_mul,sub_zero]
  exact @_root_.smul_zero ℂ (FullMatterL2→L[ℂ]FullMatterL2) _ _ Complex.I

/-- Both source branches keep their actual signed Gauss amplitudes. -/
def sourcePhysicalSoftBoundary (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (time age : ℝ) : ℂ :=
  if branch=0 then sourceSoftExternalBoundary (sourceChargedFilteredPacket sideL edgeL)
    (sourceChargedFilteredPacket sideR edgeR)
    (sourceSoftGaussAmplitude (legs 0) branch) (sourceSoftGaussAmplitude (legs 1) branch)
    (sourceSoftGaussAmplitude (legs 2) branch) (sourceSoftGaussAmplitude (legs 3) branch) time age else 0

theorem sourcePhysicalSoftBoundary_derivative (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (time age : ℝ) :
    HasDerivAt (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch time)
      (sourceChargedQuantumRead sideL edgeL sideR edgeR
        (sourceSoftNoetherOperator branch (sourceSoftGaussAmplitude (legs 0) branch)
          (sourceSoftGaussAmplitude (legs 1) branch) (sourceSoftGaussAmplitude (legs 2) branch)
          (sourceSoftGaussAmplitude (legs 3) branch) time age)) age := by
  by_cases first : branch=0
  · subst branch
    unfold sourcePhysicalSoftBoundary
    simpa only [ite_true,sourceChargedQuantumRead_generated] using
      sourceSoftExternalBoundary_derivative (sourceChargedFilteredPacket sideL edgeL)
        (sourceChargedFilteredPacket sideR edgeR)
        (sourceSoftGaussAmplitude (legs 0) 0) (sourceSoftGaussAmplitude (legs 1) 0)
        (sourceSoftGaussAmplitude (legs 2) 0) (sourceSoftGaussAmplitude (legs 3) 0) time age
  · unfold sourcePhysicalSoftBoundary
    simpa only [if_neg first,sourceSoftGaussAmplitude,
      soft_zero,sourceChargedQuantumRead_generated,zero_apply,inner_zero_right] using
      hasDerivAt_const age (0:ℂ)

/-- The original normalized physical residue pair returns the actual source preparation boundary derivative. -/
theorem sourcePhysicalNativeSoftWard_tendsto (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : Fin 3→ℝ)
    (unit : spatialSquare n=1) (time age : ℝ)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (fun e : scaleDomain=>(2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))^2 •
      sourceChargedPhysicalResidueScattering sideL edgeL sideR edgeR legs branch n unit time age e) scaleApproach
      (𝓝 (deriv (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch time) age,0)) := by
  rw [(sourcePhysicalSoftBoundary_derivative sideL edgeL sideR edgeR legs branch time age).deriv]
  exact sourceChargedSoftObservable_tendsto sideL edgeL sideR edgeR legs branch n unit time age nonrealL nonrealR

end LowEnergy.PreparationPhysicalNativeSoftWardBoundary
