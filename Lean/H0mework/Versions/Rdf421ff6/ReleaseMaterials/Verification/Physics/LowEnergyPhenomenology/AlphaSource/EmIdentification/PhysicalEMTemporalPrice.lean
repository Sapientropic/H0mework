import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.PhysicalEMTemporalGerm
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedLeftFreeJet

/-! The source EM temporal price: the original weighted Noether scalar curve differentiates
along the force ray to the EM temporal jet, the observer germ transports the derivative to
the free kernel, and the four free slopes cost a linear-in-age operator price. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMTemporal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open Stage10
open StageNineHolonomicField FullQuantum.StateGreen
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier GaussHistoryHilbert
open PreparationVacuumMixedFieldReturn CanonicalGradedSpatialSource
open PreparationVacuumSourceFieldFamily PreparationVacuumNonlinearFieldCurve
open PreparationVacuumGaugeSourceInjection PreparationVacuumActionFieldLift PreparationVacuumActualFieldQuantization
open PreparationVacuumOriginalDensity PreparationVacuumJointFieldResponse PreparationVacuumRawJointFeedback
open PreparationVacuumFullFieldRiesz PreparationVacuumSourceActionJets PreparationVacuumPhysicalFeedback
open PreparationVacuumNoetherChart PreparationPhysicalGaugeMomentumCoupling
open PreparationPhysicalPhaseGaugeRealization PreparationVacuumPhysicalGradeZeroRead
open Filter Set MeasureTheory
open scoped Topology ContDiff BigOperators Matrix Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
local instance : Fintype NativeHistoryGrade.Label:=Fintype.ofFinite _
local instance emOperatorReal : NormedAlgebra ℝ (H→L[ℂ]H):=NormedAlgebra.restrictScalars ℝ ℂ _

open PreparationVacuumNativeLocalWard PreparationVacuumNativeSourceRestriction PreparationVacuumHalfDensityFiber
open PreparationCoordinates
open ActualDressedFullCoulomb ActualDressedNoether ActualDressedConstraintRead
open ActualDressedNumberZero ActualDressedNumberField ActualDressedLeftFreeJet
open ActualDressedSourcePreparation
open LowEnergy.GaussComposite.SourceGraph LowEnergy.PreparationVacuumSourcePreparedResponse
attribute [local irreducible] noetherReader noetherReaderContact jointResolvent
  jointCResolvent physicalTime gradeZeroProjection freeCompressionCurrent
  emTemporalReader sourcePhaseGaugeField jointCompression SourceFiniteUnitary.time
  freeTimeSlope

/-- The source EM row's observed jet is the original weighted reader contraction. -/
def emTemporalJet (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289)
    (age : ℝ) : ℂ :=
  ∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*
    (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value

/-- The explicit source price: both free compression currents, both compression resolvents,
the resting EM row, and the unchanged prepared background. -/
def emTemporalPrice (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289) : ℝ :=
  ((‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖+
    ‖freeCompressionCurrent event.momentum event.frame force‖)*
    ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
    ‖emTemporalReader event.momentum event.frame‖*
    ‖jointCResolvent event.momentum event.frame event.energy 0‖+
  ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
    ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖*
    ‖emTemporalReader event.momentum event.frame‖*
    ‖jointCResolvent event.momentum event.frame event.energy 0‖+
  ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
    ‖emTemporalReader event.momentum event.frame‖*
    ‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
    ‖freeCompressionCurrent event.momentum event.frame force‖)*
    (1+‖prepared (sourceProfile event.epsilon event.precision)‖^2)

/-- The free slope: the four driven words with the resting EM reader, in the same
derivative order produced by the five-factor product rule. -/
def emFreeSlope (event : DressedEvent) (transfer : PhysicalMomentum) (force : Field289)
    (age : ℝ) : H→L[ℂ]H :=
  freeTimeSlope (event.momentum-transfer) event.frame force (-age)*
    jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
    emTemporalReader event.momentum event.frame*
    jointCResolvent event.momentum event.frame event.energy 0*
    SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age+
  SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame 0) (-age)*
    (-(jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
      freeCompressionCurrent (event.momentum-transfer) event.frame force*
      jointCResolvent (event.momentum-transfer) event.frame event.energy 0))*
    emTemporalReader event.momentum event.frame*
    jointCResolvent event.momentum event.frame event.energy 0*
    SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age+
  SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame 0) (-age)*
    jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
    emTemporalReader event.momentum event.frame*
    (-(jointCResolvent event.momentum event.frame event.energy 0*
      freeCompressionCurrent event.momentum event.frame force*
      jointCResolvent event.momentum event.frame event.energy 0))*
    SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age+
  SourceFiniteUnitary.time (jointCompression (event.momentum-transfer) event.frame 0) (-age)*
    jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
    emTemporalReader event.momentum event.frame*
    jointCResolvent event.momentum event.frame event.energy 0*
    freeTimeSlope event.momentum event.frame force age

/-- The free kernel admits a genuine scalar derivative along the original force ray,
paid by the two public free-leg directions with the same J0. -/
private theorem em_free_kernel_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>emTemporalFreeKernel event transfer age (r • force))
      (emFreeSlope event transfer force age) 0 := by
  unfold emTemporalFreeKernel emFreeSlope
  have first:=free_time_direction (event.momentum-transfer) event.frame force (-age)
  have second:=free_green_direction (event.momentum-transfer) event.frame event.energy
    event.nonreal force
  have third : HasDerivAt (fun _r : ℝ=>emTemporalReader event.momentum event.frame) 0 0 :=
    hasDerivAt_const _ _
  have fourth:=free_green_direction event.momentum event.frame event.energy
    event.nonreal force
  have fifth:=free_time_direction event.momentum event.frame force age
  have whole:=((((first.mul second).mul third).mul fourth).mul fifth)
  convert whole using 1
  all_goals first | rfl |
    (simp only [Pi.mul_apply,zero_smul,mul_zero,zero_mul,add_zero,zero_add];
      noncomm_ring)

/-- The middle J factor reads through the original linear combination of unit readers. -/
private theorem em_kernel_expand (event : DressedEvent) (transfer : PhysicalMomentum)
    (age : ℝ) (h : Field289)
    (flat : noetherReader (sourcePhaseGaugeField 0) event.momentum event.frame h=
      ∑k : Fin 289,((sourcePhaseGaugeField 0) k:ℂ)•noetherReader (fieldUnit k)
        event.momentum event.frame h) :
    dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age h=
      ∑k : Fin 289,((sourcePhaseGaugeField 0) k:ℂ)•
        dressedNoetherKernel event transfer (fieldUnit k) age h := by
  unfold dressedNoetherKernel
  rw [flat]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  noncomm_ring

/-- The scalar EM curve admits the weighted jet derivative along the force ray. -/
private theorem em_scalar_curve_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>dressedEulerObserver event
        (dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age (r • force)))
      (emTemporalJet event transfer force age) 0 := by
  have germ : ∀ᶠr : ℝ in 𝓝 0,noetherReader (sourcePhaseGaugeField 0)
      event.momentum event.frame (r • force)=
      ∑k : Fin 289,((sourcePhaseGaugeField 0) k:ℂ)•noetherReader (fieldUnit k)
        event.momentum event.frame (r • force) :=
    (source_reader_germ (sourcePhaseGaugeField 0) event.momentum event.frame).comp_tendsto
      (by simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto)
  have each (i : Fin 289) : HasDerivAt
      (fun r : ℝ=>((sourcePhaseGaugeField 0) i:ℂ)*dressedEulerObserver event
        (dressedNoetherKernel event transfer (fieldUnit i) age (r • force)))
      (((sourcePhaseGaugeField 0) i:ℂ)*
        (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value) 0 :=
    (dressed_noether_action_derivative event transfer force age i).const_mul
      ((sourcePhaseGaugeField 0) i:ℂ)
  have expand : ∀ᶠr : ℝ in 𝓝 0,dressedEulerObserver event
      (dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age (r • force))=
      ∑k : Fin 289,((sourcePhaseGaugeField 0) k:ℂ)*dressedEulerObserver event
        (dressedNoetherKernel event transfer (fieldUnit k) age (r • force)) := by
    filter_upwards [germ] with r flat
    calc dressedEulerObserver event
          (dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age
            (r • force))=
        dressedEulerObserver event
          (∑k : Fin 289,((sourcePhaseGaugeField 0) k:ℂ)•
            dressedNoetherKernel event transfer (fieldUnit k) age (r • force)) :=
        congrArg (dressedEulerObserver event)
          (em_kernel_expand event transfer age (r • force) flat)
      _ =∑k : Fin 289,((sourcePhaseGaugeField 0) k:ℂ)*dressedEulerObserver event
          (dressedNoetherKernel event transfer (fieldUnit k) age (r • force)) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul,smul_eq_mul]
  have whole:=HasDerivAt.fun_sum (u:=Finset.univ) (fun i _=>each i)
  show HasDerivAt (fun r : ℝ=>dressedEulerObserver event
      (dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age (r • force)))
    (∑i : Fin 289,((sourcePhaseGaugeField 0) i:ℂ)*
      (dressedNoetherJet event transfer (fun _=>⟨force,0,0⟩) age i).value) 0
  exact whole.congr_of_eventuallyEq expand

/-- The germ transports the original scalar derivative to the free scalar curve. -/
private theorem em_scalar_free_derivative (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    HasDerivAt (fun r : ℝ=>dressedEulerObserver event
        (emTemporalFreeKernel event transfer age (r • force)))
      (dressedEulerObserver event (emFreeSlope event transfer force age)) 0 := by
  have fder:=em_free_kernel_derivative event transfer force age
  exact ((dressedEulerObserver event).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    0 fder

/-- The original EM temporal jet is the free slope's Euler read: the observer germ forces
the two scalar derivatives to agree. -/
theorem actual_em_temporal_jet_free (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    emTemporalJet event transfer force age=
      dressedEulerObserver event (emFreeSlope event transfer force age) := by
  have ray : Tendsto (fun r : ℝ=>r • force) (𝓝 0) (𝓝 (0:Field289)) := by
    simpa only [zero_smul] using (fieldRay_derivative force 0).continuousAt.tendsto
  have germ_eq : ∀ᶠr : ℝ in 𝓝 0,dressedEulerObserver event
      (dressedNoetherKernel event transfer (sourcePhaseGaugeField 0) age (r • force))=
      dressedEulerObserver event (emTemporalFreeKernel event transfer age (r • force)) :=
    (ray.eventually (actual_em_temporal_observer_germ event transfer)).mono (fun _ h=>h age)
  have via_kernel : HasDerivAt (fun r : ℝ=>dressedEulerObserver event
      (emTemporalFreeKernel event transfer age (r • force)))
      (emTemporalJet event transfer force age) 0 :=
    (em_scalar_curve_derivative event transfer force age).congr_of_eventuallyEq
      (germ_eq.mono (fun _ h=>h.symm))
  exact via_kernel.unique (em_scalar_free_derivative event transfer force age)

private theorem time_le_one (C : H→L[ℂ]H) (symmetric : IsSelfAdjoint C) (t : ℝ) :
    ‖SourceFiniteUnitary.time C t‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  rw [SourceFiniteUnitary.time_norm C symmetric t,one_mul]

private theorem compression_selfAdjoint_zero (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    IsSelfAdjoint (jointCompression p F 0) := by
  rw [free_compression_base]
  exact CanonicalPhysicalSpatial.compression_selfAdjoint p F

private theorem norm_mul_five (x1 x2 x3 x4 x5 : H→L[ℂ]H) :
    ‖x1*x2*x3*x4*x5‖≤‖x1‖*‖x2‖*‖x3‖*‖x4‖*‖x5‖ := by
  have step (a b : H→L[ℂ]H) : ‖a*b‖≤‖a‖*‖b‖ := norm_mul_le _ _
  calc ‖x1*x2*x3*x4*x5‖
      ≤‖x1*x2*x3*x4‖*‖x5‖ := step _ _
    _ ≤(‖x1*x2*x3‖*‖x4‖)*‖x5‖ :=
        mul_le_mul_of_nonneg_right (step _ _) (norm_nonneg _)
    _ ≤((‖x1*x2‖*‖x3‖)*‖x4‖)*‖x5‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (step _ _) (norm_nonneg _))
          (norm_nonneg _)
    _ ≤((‖x1‖*‖x2‖*‖x3‖)*‖x4‖)*‖x5‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (step _ _) (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)
    _ =‖x1‖*‖x2‖*‖x3‖*‖x4‖*‖x5‖ := by ring

private theorem norm_five_bound {x1 x2 x3 x4 x5 : H→L[ℂ]H} {X1 X2 X3 X4 X5 : ℝ}
    (h1 : ‖x1‖≤X1) (h2 : ‖x2‖≤X2) (h3 : ‖x3‖≤X3) (h4 : ‖x4‖≤X4) (h5 : ‖x5‖≤X5) :
    ‖x1*x2*x3*x4*x5‖≤X1*X2*X3*X4*X5 := by
  have g1 : 0≤X1 := (norm_nonneg _).trans h1
  have g2 : 0≤X2 := (norm_nonneg _).trans h2
  have g3 : 0≤X3 := (norm_nonneg _).trans h3
  have g4 : 0≤X4 := (norm_nonneg _).trans h4
  have g5 : 0≤X5 := (norm_nonneg _).trans h5
  have m12:=mul_le_mul h1 h2 (norm_nonneg _) g1
  have m123:=mul_le_mul m12 h3 (norm_nonneg _) (mul_nonneg g1 g2)
  have m1234:=mul_le_mul m123 h4 (norm_nonneg _) (mul_nonneg (mul_nonneg g1 g2) g3)
  have m12345:=mul_le_mul m1234 h5 (norm_nonneg _)
    (mul_nonneg (mul_nonneg (mul_nonneg g1 g2) g3) g4)
  exact (norm_mul_five _ _ _ _ _).trans m12345

/-- The Euler pair against the grade-zero fixed states costs at most the operator norm
times the unchanged unit-plus-background factor. -/
private theorem euler_norm_bound (event : DressedEvent) (A : H→L[ℂ]H) :
    ‖dressedEulerObserver event A‖≤
      ‖A‖*(1+‖prepared (sourceProfile event.epsilon event.precision)‖^2) := by
  rw [dressed_euler_observer_original]
  have un : ‖sourceDressedUnit event.epsilon event.precision‖=1 :=
    source_dressed_unit_norm _ _
  calc ‖-inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (A (sourceDressedUnit event.epsilon event.precision))+
      inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (A (prepared (sourceProfile event.epsilon event.precision)))‖
      ≤‖inner ℂ (sourceDressedUnit event.epsilon event.precision)
          (A (sourceDressedUnit event.epsilon event.precision))‖+
        ‖inner ℂ (prepared (sourceProfile event.epsilon event.precision))
          (A (prepared (sourceProfile event.epsilon event.precision)))‖ :=
        (norm_add_le _ _).trans (add_le_add (le_of_eq (norm_neg _)) le_rfl)
    _ ≤‖sourceDressedUnit event.epsilon event.precision‖*
          ‖A (sourceDressedUnit event.epsilon event.precision)‖+
        ‖prepared (sourceProfile event.epsilon event.precision)‖*
          ‖A (prepared (sourceProfile event.epsilon event.precision))‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤‖sourceDressedUnit event.epsilon event.precision‖*‖A‖*
          ‖sourceDressedUnit event.epsilon event.precision‖+
        ‖prepared (sourceProfile event.epsilon event.precision)‖*‖A‖*
          ‖prepared (sourceProfile event.epsilon event.precision)‖ := by
        exact add_le_add
          ((mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)).trans
            (by rw [←mul_assoc]))
          ((mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)).trans
            (by rw [←mul_assoc]))
    _ =‖A‖*(‖sourceDressedUnit event.epsilon event.precision‖^2+
        ‖prepared (sourceProfile event.epsilon event.precision)‖^2) := by ring
    _ =‖A‖*(1+‖prepared (sourceProfile event.epsilon event.precision)‖^2) := by
        rw [un];norm_num

/-- The original EM temporal jet carries a linear-in-age price: the free time slopes
supply the `|age|` factors and both free Green slopes are bounded. -/
theorem actual_em_temporal_jet_linear_price (event : DressedEvent) (transfer : PhysicalMomentum)
    (force : Field289) (age : ℝ) :
    ‖emTemporalJet event transfer force age‖≤emTemporalPrice event transfer force*(1+|age|) := by
  rw [actual_em_temporal_jet_free]
  refine (euler_norm_bound event _).trans ?_
  have tbL : ‖SourceFiniteUnitary.time
      (jointCompression (event.momentum-transfer) event.frame 0) (-age)‖≤1 :=
    time_le_one _ (compression_selfAdjoint_zero _ _) _
  have tbR : ‖SourceFiniteUnitary.time
      (jointCompression event.momentum event.frame 0) age‖≤1 :=
    time_le_one _ (compression_selfAdjoint_zero _ _) _
  have tsL : ‖freeTimeSlope (event.momentum-transfer) event.frame force (-age)‖≤
      |age| *‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖ := by
    have:=free_time_slope_price (event.momentum-transfer) event.frame force (-age)
    rwa [abs_neg] at this
  have tsR : ‖freeTimeSlope event.momentum event.frame force age‖≤
      |age| *‖freeCompressionCurrent event.momentum event.frame force‖ :=
    free_time_slope_price event.momentum event.frame force age
  have gsL : ‖-(jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
      freeCompressionCurrent (event.momentum-transfer) event.frame force*
      jointCResolvent (event.momentum-transfer) event.frame event.energy 0)‖≤
      ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖ :=
    free_green_slope_price _ _ _ _
  have gsR : ‖-(jointCResolvent event.momentum event.frame event.energy 0*
      freeCompressionCurrent event.momentum event.frame force*
      jointCResolvent event.momentum event.frame event.energy 0)‖≤
      ‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent event.momentum event.frame force‖ :=
    free_green_slope_price _ _ _ _
  have term1 : ‖freeTimeSlope (event.momentum-transfer) event.frame force (-age)*
      jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
      emTemporalReader event.momentum event.frame*
      jointCResolvent event.momentum event.frame event.energy 0*
      SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age‖≤
      (|age| *‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖)*
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖*1 :=
    norm_five_bound tsL le_rfl le_rfl le_rfl tbR
  have term2 : ‖SourceFiniteUnitary.time
      (jointCompression (event.momentum-transfer) event.frame 0) (-age)*
      (-(jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
        freeCompressionCurrent (event.momentum-transfer) event.frame force*
        jointCResolvent (event.momentum-transfer) event.frame event.energy 0))*
      emTemporalReader event.momentum event.frame*
      jointCResolvent event.momentum event.frame event.energy 0*
      SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age‖≤
      1*(‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖)*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖*1 :=
    norm_five_bound tbL gsL le_rfl le_rfl tbR
  have term3 : ‖SourceFiniteUnitary.time
      (jointCompression (event.momentum-transfer) event.frame 0) (-age)*
      jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
      emTemporalReader event.momentum event.frame*
      (-(jointCResolvent event.momentum event.frame event.energy 0*
        freeCompressionCurrent event.momentum event.frame force*
        jointCResolvent event.momentum event.frame event.energy 0))*
      SourceFiniteUnitary.time (jointCompression event.momentum event.frame 0) age‖≤
      1*‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        (‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent event.momentum event.frame force‖)*1 :=
    norm_five_bound tbL le_rfl le_rfl gsR tbR
  have term4 : ‖SourceFiniteUnitary.time
      (jointCompression (event.momentum-transfer) event.frame 0) (-age)*
      jointCResolvent (event.momentum-transfer) event.frame event.energy 0*
      emTemporalReader event.momentum event.frame*
      jointCResolvent event.momentum event.frame event.energy 0*
      freeTimeSlope event.momentum event.frame force age‖≤
      1*‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖*
        (|age| *‖freeCompressionCurrent event.momentum event.frame force‖) :=
    norm_five_bound tbL le_rfl le_rfl le_rfl tsR
  have total : ‖emFreeSlope event transfer force age‖≤
      ((‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖+
        ‖freeCompressionCurrent event.momentum event.frame force‖)*
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖+
      ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖+
      ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent event.momentum event.frame force‖)*(1+|age|) := by
    unfold emFreeSlope
    have piece : |age| *‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖*
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖*1+
      1*(‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖)*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖*1+
      1*‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        (‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent event.momentum event.frame force‖)*1+
      1*‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖*
        (|age| *‖freeCompressionCurrent event.momentum event.frame force‖)≤
      ((‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖+
        ‖freeCompressionCurrent event.momentum event.frame force‖)*
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖+
      ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖+
      ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent event.momentum event.frame force‖)*(1+|age|) := by
      have nA : 0≤(‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖+
        ‖freeCompressionCurrent event.momentum event.frame force‖)*
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖ := by positivity
      have nB : 0≤‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖ := by positivity
      have nC : 0≤‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent event.momentum event.frame force‖ := by positivity
      nlinarith [abs_nonneg age]
    exact ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add ((norm_add_le _ _).trans (add_le_add term1 term2)) term3)) term4)).trans piece
  calc ‖emFreeSlope event transfer force age‖*
      (1+‖prepared (sourceProfile event.epsilon event.precision)‖^2)
      ≤(((‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖+
        ‖freeCompressionCurrent event.momentum event.frame force‖)*
        ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖+
      ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent (event.momentum-transfer) event.frame force‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖+
      ‖jointCResolvent (event.momentum-transfer) event.frame event.energy 0‖*
        ‖emTemporalReader event.momentum event.frame‖*
        ‖jointCResolvent event.momentum event.frame event.energy 0‖^2*
        ‖freeCompressionCurrent event.momentum event.frame force‖)*(1+|age|))*
        (1+‖prepared (sourceProfile event.epsilon event.precision)‖^2) :=
        mul_le_mul_of_nonneg_right total (by positivity)
    _ =emTemporalPrice event transfer force*(1+|age|) := by
        unfold emTemporalPrice
        ring

end LowEnergy.GaussComposite.ActualDressedEMTemporal
