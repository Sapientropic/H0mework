import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceScalarCoframeMaster

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalTriangularSeedReturn
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
local instance LorentzProjectionIndex : DecidableEq Quantum.Index:=Classical.decEq _
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

open PreparationVacuumFullPoleContinuation PreparationVacuumPhysicalPoleHalfResponse
open PreparationVacuumMovingPoleGaussReturn PreparationVacuumPhysicalCurrentLaplaceReturn
open PreparationPhysicalFiniteObservationSoftReturn PreparationVacuumSoftPoleSelection

open PreparationVacuumStaticPoleResponse PreparationVacuumFullOriginResponse

open PreparationVacuumStaticSpatialSource PreparationVacuumStaticSimpleCoupling

open PreparationPhysicalCommonCurrentStaticRead PreparationPhysicalActualRetardedWard

open PreparationPhysicalCommonObservableUnits PreparationVacuumPhysicalPinnedVelocity
open PreparationVacuumGaugeSlowFrequency PreparationVacuumQuantumSlowResidue
open PreparationVacuumPhysicalSlowBlock PreparationVacuumSharedPoleCarrier
open PreparationVacuumObservedPoleTensor
open PreparationVacuumActualSpatialPacket
open scoped Matrix.Norms.Operator SchwartzMap

open PreparationPhysicalCommonSpatialGreen PreparationPhysicalActualGaussChargeCurrent
open PreparationPhysicalActualNoetherVertexReturn PreparationPhysicalActualPhaseChargeReturn

open Set GaussianFourier


open PreparationPhysicalChannelGreen


open PreparationPhysicalChannelRadialJet PreparationVacuumObservedStaticResidue


open GaussCoreHilbert SourceJointResidualEnergy PreparationVacuumQuantumSlowResponse
open PreparationPhysicalJointRadialForcing

open PreparationVacuumPhysicalHalfAxis CanonicalGradedCurrent GaussUnitaryHistory
open PreparationPhysicalRetainerResolventSquare PreparationVacuumStaticSpatialSource
open PreparationPhysicalCausalSpatialDilation
open PreparationPhysicalMasterCorrectionReturn PreparationPhysicalPhaseGaugeRealization
open PreparationPhysicalGaugeSeedNull PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets
open PreparationPhysicalActionSeedReduction PreparationVacuumLowerClassical PreparationVacuumJointFieldResponse
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumFockGrade56
open GaussCoreDifferential GaussCoreLabel NativeHistoryGrade GaussFockLabel GaussYukawaGrade
open PreparationVacuumPropagationPencil PreparationVacuumRawJointFeedback
open PreparationVacuumPhysicalNumberOneRead PreparationVacuumPhysicalPoleLegDynamics PreparationVacuumPhysicalGradeZeroRead
open PreparationPhysicalLorentzSeedReturn
open PreparationVacuumYukawaTransport SourceQuantumScalarChart StageNineDiracDualYukawaSpinJurisdiction
open StageNineDynamicBreakingVacuum

/-- The original six-sector order, on the original primal matrix coordinates. -/
def sourcePrimalNonlower (A : SourceMatrix) : Prop :=
  ∀ i j, ¬isSix i → isSix j → A i j=0

private theorem nonlower_preserves (A : SourceMatrix) (paid : (paidLorentzGrade% primalPreserves) A) :
    sourcePrimalNonlower A := by
  intro i j hi hj
  have h:=paid i j
  simpa only [if_neg hi,if_pos hj,zero_sub,neg_mul,one_mul,neg_eq_zero] using h

private theorem nonlower_zero : sourcePrimalNonlower 0 := by
  intro i j _ _
  rfl
private theorem nonlower_add {A B : SourceMatrix} (a : sourcePrimalNonlower A) (b : sourcePrimalNonlower B) :
    sourcePrimalNonlower (A+B) := by
  intro i j hi hj
  change A i j+B i j=0
  rw [a i j hi hj,b i j hi hj,add_zero]
private theorem nonlower_neg {A : SourceMatrix} (a : sourcePrimalNonlower A) :
    sourcePrimalNonlower (-A) := by
  intro i j hi hj
  change -(A i j)=0
  rw [a i j hi hj,neg_zero]
private theorem nonlower_sub {A B : SourceMatrix} (a : sourcePrimalNonlower A) (b : sourcePrimalNonlower B) :
    sourcePrimalNonlower (A-B) := by
  rw [sub_eq_add_neg]
  exact nonlower_add a (nonlower_neg b)
private theorem nonlower_smul {A : SourceMatrix} (a : sourcePrimalNonlower A) (c : ℂ) :
    sourcePrimalNonlower (c • A) := by
  intro i j hi hj
  change c*A i j=0
  rw [a i j hi hj,mul_zero]
private theorem nonlower_real_smul {A : SourceMatrix} (a : sourcePrimalNonlower A) (c : ℝ) :
    sourcePrimalNonlower (c • A) := nonlower_smul a (c:ℂ)
private theorem nonlower_sum {ι : Type*} [Fintype ι] (A : ι→SourceMatrix)
    (paid : ∀ i,sourcePrimalNonlower (A i)) : sourcePrimalNonlower (∑i,A i) := by
  intro i j hi hj
  simp only [Matrix.sum_apply]
  exact Finset.sum_eq_zero (fun k _=>paid k i j hi hj)
private theorem nonlower_mul {A B : SourceMatrix} (a : sourcePrimalNonlower A) (b : sourcePrimalNonlower B) :
    sourcePrimalNonlower (A*B) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases middle : isSix k
  · rw [a i k hi middle,zero_mul]
  · rw [b k j middle hj,mul_zero]

private theorem preserves_inverse (A : SourceMatrix) (paid : (paidLorentzGrade% primalPreserves) A) :
    (paidLorentzGrade% primalPreserves) (Ring.inverse A) := by
  let D : SourceMatrix:=Matrix.diagonal (fun i=>if isSix i then (1:ℂ) else 0)
  have commute : Commute D A := by
    ext i j
    have h:=paid i j
    simp only [D,Matrix.diagonal_mul,Matrix.mul_diagonal]
    linear_combination h
  by_cases unit : IsUnit A
  · have h:=(inverse_commuting D A unit commute).eq
    intro i j
    have entry:=congrFun (congrFun h i) j
    simp only [D,Matrix.diagonal_mul,Matrix.mul_diagonal] at entry
    linear_combination entry
  · rw [Ring.inverse_non_unit A unit]
    intro i j
    simp only [Matrix.zero_apply,mul_zero]

private theorem scalar_nonlower (s : Scalar) : sourcePrimalNonlower (PreparationVacuumGaugeSourceInjection.scalarLinear s) := by
  intro i j hi hj
  have law : MixedSymbol.degreeSix*diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm s)=
      diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm s)*MixedSymbol.degreeSix+
        (1:ℂ) • diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm s) := by
    rw [Module.End.mul_eq_comp,Module.End.mul_eq_comp,MixedSymbol.yukawa_output,
      MixedSymbol.yukawa_degreeSix,one_smul,zero_add]
  have h:=matrix_grade (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm s)) 1
    (by simpa only [Nat.cast_one] using law) i j
  have hzero : (-2:ℂ)*PreparationVacuumGaugeSourceInjection.scalarLinear s i j=0 := by
    simp only [if_neg hi,if_pos hj,Nat.cast_one] at h
    change (-2:ℂ)*Quantum.operatorMatrix (diracDualRightChiralYukawaAction (scalarCoordinateEquiv.symm s)) i j=0
    linear_combination h
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)


private theorem spin_nonlower (mu : Fin 4) (v : StageNineLorentzConnectionVariation.LorentzBivectorOneForm) :
    sourcePrimalNonlower (spinLinear mu v) := by
  apply nonlower_preserves
  unfold spinLinear
  exact (paidLorentzGrade% primal_mother) _ (MixedSymbol.degreeSix_spin _)

private theorem native_nonlower (v : SourceQuantumScalarChart.NativeLie) :
    sourcePrimalNonlower (nativePrimal v) := by
  apply nonlower_preserves
  exact (paidLorentzGrade% primal_mother) _ (MixedSymbol.degreeSix_gauge _)

private theorem source_connection_nonlower (z : SourceCoordinateSlice) (mu : Fin 4) :
    sourcePrimalNonlower ((sourceState z).2.1 mu) := by
  change sourcePrimalNonlower (familyConnection z mu)
  apply nonlower_preserves
  exact (paidLorentzGrade% primal_mother) _ (FullQuantum.Triangular.grade_connection 0 (emitter z) 0 mu)

private theorem source_scalar_nonlower (z : SourceCoordinateSlice) :
    sourcePrimalNonlower (sourceState z).2.2 := by
  change sourcePrimalNonlower (PreparationVacuumGaugeSourceInjection.scalarLinear (GaussNativePotential.scalarField z))
  exact scalar_nonlower _

private theorem direction_connection_nonlower (f : Field289) (mu : Fin 4) :
    sourcePrimalNonlower ((fieldDirection f).2.1 mu) := by
  rw [←stateDirection_source]
  change sourcePrimalNonlower (spinLinear mu (fieldLorentz f)+nativePrimal (fieldGauge f mu))
  exact nonlower_add (spin_nonlower _ _) (native_nonlower _)

private theorem direction_scalar_nonlower (f : Field289) : sourcePrimalNonlower (fieldDirection f).2.2 := by
  rw [←stateDirection_source]
  change sourcePrimalNonlower (PreparationVacuumGaugeSourceInjection.scalarLinear (fieldScalar f))
  exact scalar_nonlower _

private theorem lower_nonlower (s : ActionState) (connection : ∀mu,sourcePrimalNonlower (s.2.1 mu))
    (scalar : sourcePrimalNonlower s.2.2) : sourcePrimalNonlower (stateLower s) :=
  nonlower_add (nonlower_sum _ (fun mu=>nonlower_mul
    (nonlower_preserves _ ((paidLorentzGrade% primal_coefficient) mu s.1)) (connection mu))) scalar

private theorem principal_nonlower (s : ActionState) (mu : Fin 4) : sourcePrimalNonlower (statePrincipal mu s) :=
  nonlower_smul (nonlower_preserves _ ((paidLorentzGrade% primal_coefficient) mu s.1)) (stateVolume s)

private theorem hamiltonian_nonlower (s : ActionState) (connection : ∀mu,sourcePrimalNonlower (s.2.1 mu))
    (scalar : sourcePrimalNonlower s.2.2) (i : Fin 4) : sourcePrimalNonlower (stateHamiltonian s i) := by
  have inverse : sourcePrimalNonlower (Ring.inverse (CoframeResponse.principalMatrix s.1)) := by
    rw [principalMatrix_coefficient]
    exact nonlower_preserves _ (preserves_inverse _ ((paidLorentzGrade% primal_coefficient) 0 s.1))
  refine Fin.cases ?_ (fun j=>?_) i
  · exact nonlower_smul (nonlower_mul inverse (lower_nonlower s connection scalar)) (-Complex.I)
  · exact nonlower_mul inverse (nonlower_preserves _ ((paidLorentzGrade% primal_coefficient) j.succ s.1))

private theorem held_nonlower (base candidate : ActionState)
    (baseConnection : ∀mu,sourcePrimalNonlower (base.2.1 mu)) (baseScalar : sourcePrimalNonlower base.2.2)
    (connection : ∀mu,sourcePrimalNonlower (candidate.2.1 mu)) (scalar : sourcePrimalNonlower candidate.2.2)
    (i : Fin 4) : sourcePrimalNonlower (heldDensityCoefficient base candidate i) := by
  apply nonlower_sub
  · refine Fin.cases ?_ (fun j=>?_) i
    · exact nonlower_smul (lower_nonlower candidate connection scalar) (stateVolume candidate)
    · exact nonlower_smul (principal_nonlower candidate j.succ) Complex.I
  · exact nonlower_smul (nonlower_mul (principal_nonlower candidate 0)
      (hamiltonian_nonlower base baseConnection baseScalar i)) Complex.I

local instance : FiniteDimensional ℂ SourceMatrix:=Matrix.finiteDimensional
local instance : FiniteDimensional ℝ SourceMatrix:=FiniteDimensional.trans ℝ ℂ SourceMatrix

private def matrixEntryRead (i j : Quantum.Index) : SourceMatrix→L[ℝ]ℂ :=
  LinearMap.toContinuousLinearMap
    {toFun:=fun A=>A i j
     map_add':=fun _ _=>rfl
     map_smul':=fun _ _=>rfl}

/-- The original source state and every original field direction have no downward raw density entry; the derivative is taken on the actual held-density path. -/
theorem sourceDensityVariation_nonlower (f : Field289) (z : physicalChart) (i : Fin 4) :
    sourcePrimalNonlower (densityVariation f (sourceState z.val) i) := by
  intro a b ha hb
  have paid:=densityVariation_generated f (sourceState z.val) (coframe_nondegenerate z) i
  have entry:=(matrixEntryRead a b).hasFDerivAt.comp_hasDerivAt 0 paid
  have zero : (fun t : ℝ=>matrixEntryRead a b
      (heldDensityCoefficient (sourceState z.val) (sourceState z.val+t • fieldDirection f) i))=fun _=>0 := by
    funext t
    apply held_nonlower (sourceState z.val) (sourceState z.val+t • fieldDirection f)
      (source_connection_nonlower z.val) (source_scalar_nonlower z.val) _ _ i a b ha hb
    · intro mu
      exact nonlower_add (source_connection_nonlower z.val mu)
        (nonlower_real_smul (direction_connection_nonlower f mu) t)
    · exact nonlower_add (source_scalar_nonlower z.val)
        (nonlower_real_smul (direction_scalar_nonlower f) t)
  simp only [Function.comp_def] at entry
  rw [zero] at entry
  exact entry.unique (hasDerivAt_const (0:ℝ) (0:ℂ))

/-- Both original independent branches use the same occupation-grade order. -/
def sourceFullNonlower (A : FullMatrix) : Prop :=
  ∀ i j, i∉target → j∈target → A i j=0

private theorem full_nonlower_mul {A B : FullMatrix} (a : sourceFullNonlower A) (b : sourceFullNonlower B) :
    sourceFullNonlower (A*B) := by
  intro i j hi hj
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases middle : k∈target
  · rw [a i k hi middle,zero_mul]
  · rw [b k j middle hj,mul_zero]

private theorem full_nonlower_preserves (A : FullMatrix) (paid : Preserves A) : sourceFullNonlower A := by
  intro i j hi hj
  have h:=paid i j
  simpa only [charge,if_neg hi,if_pos hj,zero_sub,neg_mul,one_mul,neg_eq_zero] using h

private theorem affine_nonlower (A : Fin 4→SourceMatrix) (paid : ∀i,sourcePrimalNonlower (A i))
    (p : PhysicalMomentum) : sourcePrimalNonlower (affineMatrix A p) :=
  nonlower_add (paid 0) (nonlower_sum _ (fun j=>nonlower_smul (paid j.succ) (p j:ℂ)))

private theorem fourier_nonlower (A : Fin 4→SourceMatrix) (paid : ∀i,sourcePrimalNonlower (A i))
    (p : PhysicalMomentum) : sourceFullNonlower (realFourierMatrix A p) := by
  intro i j hi hj
  cases i with
  | inl i=>cases j with
    | inl j=>exact affine_nonlower A paid p i j (by simpa only [mem_target_left] using hi) (by simpa only [mem_target_left] using hj)
    | inr j=>rfl
  | inr i=>cases j with
    | inl j=>rfl
    | inr j=>
      change -(star (affineMatrix A (-p) i j))=0
      rw [affine_nonlower A paid (-p) i j (by simpa only [mem_target_right] using hi)
        (by simpa only [mem_target_right] using hj),star_zero,neg_zero]

/-- Complete original density normalization, momentum coefficients and independent dual branches generate the no-lowering full504 raw symbol. -/
theorem sourceRawActionSymbol_nonlower (f : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    sourceFullNonlower (rawActionSymbol f p (sourceState z.val)) := by
  change sourceFullNonlower (oppositeDual*realFourierMatrix
    (fun i=>densityActionMatrix*densityVariation f (sourceState z.val) i) p)
  apply full_nonlower_mul (full_nonlower_preserves _ (paidLorentzGrade% opposite_preserves))
  exact fourier_nonlower _ (fun i=>nonlower_mul
    (nonlower_preserves _ (paidLorentzGrade% primal_densityAction)) (sourceDensityVariation_nonlower f z i)) p

end LowEnergy.PreparationPhysicalTriangularSeedReturn
