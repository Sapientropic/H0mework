import H0mework.Versions.R9c73a630.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedLeftRetained

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCofinal
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open FullQuantum FullQuantum.CoframeResponse FullQuantum.StateGreen
open PreparationVacuumSourceFieldFamily PreparationVacuumMixedFieldReturn
open PreparationVacuumGaugeSourceInjection PreparationVacuumOriginalDensity
open PreparationVacuumActualFieldQuantization PreparationVacuumNonlinearFieldCurve
open SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates SourceQuantumConfigurationHilbert
open GaussHistoryHilbert GaussQuantumMultiplier GaussCoreDifferential CanonicalGradedSpatialSource
open scoped Matrix BigOperators
local instance : DecidableEq Quantum.Index:=Classical.decEq _
local instance : DecidableEq Mode:=Classical.decEq _
attribute [local instance] SourceRealScalarFock.branchOrder

open GaussCoreHilbert PreparationVacuumPhysicalFeedback PreparationVacuumJointFieldResponse
open GaussNativeMatter CanonicalGradedCharge PreparationPhysicalPhaseGaugeRealization GaussComposite.PhysicalEMPoleWard
open PreparationVacuumActionFieldLift GaussComposite.PhysicalEMGaugeRealization
open PreparationPhysicalActionUnits GaussComposite.PhysicalEMVoltage PreparationPhysicalNormalizedFullField GaussComposite.ActualDressedSourcePreparation GaussComposite.ActualDressedSourceResponse PreparationVacuumFullElectricWard


open ActualDressedActionPhase PreparationVacuumTemporalCharge PreparationVacuumLowerClassical


open ActualDressedTemporalNormalization GaussFockPair PreparationVacuumSourceActionJets
open MeasureTheory Filter Set


open ActualDressedTemporalForm ActualDressedJointTemporal ActualDressedJointOrbitCurrent
open ActualDressedFullCoulomb PreparationVacuumWeightedChargeActionWard
open PreparationVacuumSourceChargeWard PreparationVacuumNoetherOrdinaryWard
open PreparationVacuumFullFieldRiesz PreparationVacuumNoetherChart
open scoped Topology InnerProductSpace
open PreparationVacuumFieldConstraintResponse CanonicalPhysicalYResolvent PreparationVacuumSourcePreparedResponse
open CanonicalPreparationCore.Completed CanonicalScalarPreparation GaussComposite.SourceGraph
attribute [local irreducible] sourceDressedUnit sourceDressedExcitation sourceProfile finiteFull sourceDressedResponse chargeReader


open PreparationVacuumFieldCovector PreparationVacuumRawJointFeedback PreparationVacuumCausalFieldResponse
open PreparationVacuumActionDecomposition PreparationVacuumGradedTransport
open ActualDressedTemporalCurrent


open ActualDressedReaderComponents ActualDressedCutReturn ActualDressedNoether
open CanonicalPhysicalYResolvent
attribute [local irreducible] currentVertex currentRestriction temporalReaderCompensation noetherReader
  jointResolvent dressedEulerObserver


open ActualDressedReaderMatching PreparationVacuumYukawaTransport PreparationVacuumUncutYukawa
open CanonicalPhysicalSpatial FullYSourceCutoffVolterra
attribute [local irreducible] retainer cutoff uncutOperator


open ActualDressedRetainer
attribute [local irreducible] jointGenerator


open ActualDressedLeftRetained

private theorem inverse_return {A : Type*} [Ring A] (C U L R D : A)
    (left : L*C=1) (right : U*R=1) (tail : U=C+D) : L=R+L*D*R := by
  have generated : L*D*R=L-R := by
    have delta : D=U-C := by rw [tail];abel
    rw [delta,mul_sub,sub_mul,mul_assoc,right,mul_one,left,one_mul]
  rw [generated]
  abel

private theorem retained_denominator {A : Type*} [Ring A] (C P Y Z : A) :
    C+P*Y-Z=(C+Y-Z)+(P-1)*Y := by
  simp only [sub_mul,one_mul]
  abel

/-- Global cut and the original retained-cut inverse are related by the genuine localization leak alone. -/
theorem retained_cut_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ)
    (z : ℂ) (nonreal : z.im≠0) :
    finiteFull p F cut z=sourceResolvent 0 p F (some cut) z 0+
      finiteFull p F cut z*cutRetainerLeak p F cut*sourceResolvent 0 p F (some cut) z 0 := by
  have diagonal:=(movingDiagonal_units (0:Field289) p F z nonreal).self_of_nhds
  have jet : jetOperator 0 cut 0 (finiteRetainer p F) 0=retainer p F*cutoff cut :=
    (jetOperator_cutoff (0:Field289) cut p F (0:ℝ)).trans
      (congrArg (fun X : H→L[ℂ]H=>retainer p F*X) (fieldCutoff_zero (0:Field289) cut))
  apply inverse_return (compression p F+cutoff cut-z • 1) (sourceGenerator 0 p F (some cut) z 0)
    (finiteFull p F cut z) (sourceResolvent 0 p F (some cut) z 0) (cutRetainerLeak p F cut)
    (finiteFull_left p F cut z nonreal)
  · unfold sourceResolvent
    exact Ring.mul_inverse_cancel (sourceGenerator 0 p F (some cut) z 0)
      (sourceUnit 0 p F (some cut) z 0 diagonal).isUnit
  · change transportedCompression 0 p F 0+jetOperator 0 cut 0 (finiteRetainer p F) 0-z • 1=_
    have generated:=congrArg (fun C : H→L[ℂ]H=>C+jetOperator 0 cut 0 (finiteRetainer p F) 0-z • 1)
      (transportedCompression_zero (0:Field289) p F)
    exact generated.trans ((congrArg (fun Y : H→L[ℂ]H=>compression p F+Y-z • 1) jet).trans
      (retained_denominator (compression p F) (retainer p F) (cutoff cut) (z • 1)))

private theorem retained_right_exact (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) (x : H) (support : x∈retainedSpace p F) :
    finiteFull p F cut z x=sourceResolvent 0 p F (some cut) z 0 x := by
  have diagonal:=(movingDiagonal_units (0:Field289) p F z nonreal).self_of_nhds
  have paid:=sourceResolvent_cut 0 p F cut z (by intro h;apply nonreal;rw [h];rfl) 0 diagonal x support
  simpa only [trueResolvent_zero (0:Field289) p F cut z nonreal] using paid.symm

/-- The original independent left functionals agree with the retained-cut operator on every input, on both unchanged external states. -/
theorem dressed_retained_left_exact (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (y : H) :
    inner ℂ (sourceDressedUnit event.epsilon event.precision) (finiteFull p F cut event.energy y)=
      inner ℂ (sourceDressedUnit event.epsilon event.precision) (sourceResolvent 0 p F (some cut) event.energy 0 y) ∧
    inner ℂ (prepared (sourceProfile event.epsilon event.precision)) (finiteFull p F cut event.energy y)=
      inner ℂ (prepared (sourceProfile event.epsilon event.precision)) (sourceResolvent 0 p F (some cut) event.energy 0 y) := by
  have returned:=congrArg (fun A : H→L[ℂ]H=>A y) (retained_cut_return p F cut event.energy event.nonreal)
  change finiteFull p F cut event.energy y=sourceResolvent 0 p F (some cut) event.energy 0 y+
    finiteFull p F cut event.energy (cutRetainerLeak p F cut (sourceResolvent 0 p F (some cut) event.energy 0 y)) at returned
  have leak:=dressed_left_leak_zero event p F cut (sourceResolvent 0 p F (some cut) event.energy 0 y)
  constructor
  · have paid:=congrArg (fun x : H=>inner ℂ (sourceDressedUnit event.epsilon event.precision) x) returned
    simpa only [inner_add_right,leak.1,add_zero] using paid
  · have paid:=congrArg (fun x : H=>inner ℂ (prepared (sourceProfile event.epsilon event.precision)) x) returned
    simpa only [inner_add_right,leak.2.2.1,add_zero] using paid

private theorem apply_limit (R : ℕ→H→L[ℂ]H) (S : H→L[ℂ]H) (limit : Tendsto R atTop (𝓝 S)) (x : H) :
    Tendsto (fun n=>R n x) atTop (𝓝 (S x)) := by
  exact (ContinuousLinearMap.apply ℂ H x).continuous.tendsto S |>.comp limit

private theorem adjoint_apply_limit (R : ℕ→H→L[ℂ]H) (S : H→L[ℂ]H)
    (limit : Tendsto R atTop (𝓝 S)) (x : H) :
    Tendsto (fun n=>(R n).adjoint x) atTop (𝓝 (S.adjoint x)) := by
  exact apply_limit (fun n=>(R n).adjoint) S.adjoint
    ((ContinuousLinearMap.adjoint : (H→L[ℂ]H)≃ₗᵢ⋆[ℂ](H→L[ℂ]H)).continuous.tendsto S |>.comp limit) x

/-- Fixed-F cofinal cutoff uses the original retained source coefficient convergence. -/
theorem dressed_two_response_limits (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) :
    Tendsto (fun cut=>finiteFull p F cut event.energy (sourceDressedUnit event.epsilon event.precision)) atTop
      (𝓝 (jointResolvent p F event.energy 0 (sourceDressedUnit event.epsilon event.precision))) ∧
    Tendsto (fun cut=>(finiteFull p F cut event.energy).adjoint (sourceDressedUnit event.epsilon event.precision)) atTop
      (𝓝 ((jointResolvent p F event.energy 0).adjoint (sourceDressedUnit event.epsilon event.precision))) ∧
    Tendsto (fun cut=>finiteFull p F cut event.energy (prepared (sourceProfile event.epsilon event.precision))) atTop
      (𝓝 (jointResolvent p F event.energy 0 (prepared (sourceProfile event.epsilon event.precision)))) ∧
    Tendsto (fun cut=>(finiteFull p F cut event.energy).adjoint (prepared (sourceProfile event.epsilon event.precision))) atTop
      (𝓝 ((jointResolvent p F event.energy 0).adjoint (prepared (sourceProfile event.epsilon event.precision)))) := by
  have support:=dressed_original_retained event p F
  have diagonal:=(movingDiagonal_units (0:Field289) p F event.energy event.nonreal).self_of_nhds
  have limit : Tendsto (fun cut=>sourceResolvent 0 p F (some cut) event.energy 0) atTop
      (𝓝 (jointResolvent p F event.energy 0)) := by
    rw [jointResolvent_zero (0:Field289) p F event.energy]
    exact sourceResolvent_limit 0 p F event.energy 0 diagonal
  have left (cut : ℕ) :
      (finiteFull p F cut event.energy).adjoint (sourceDressedUnit event.epsilon event.precision)=
        (sourceResolvent 0 p F (some cut) event.energy 0).adjoint (sourceDressedUnit event.epsilon event.precision) ∧
      (finiteFull p F cut event.energy).adjoint (prepared (sourceProfile event.epsilon event.precision))=
        (sourceResolvent 0 p F (some cut) event.energy 0).adjoint (prepared (sourceProfile event.epsilon event.precision)) := by
    constructor <;> apply ext_inner_right ℂ <;> intro y <;> simp only [ContinuousLinearMap.adjoint_inner_left]
    · exact (dressed_retained_left_exact event p F cut y).1
    · exact (dressed_retained_left_exact event p F cut y).2
  constructor
  · simpa only [retained_right_exact p F _ event.energy event.nonreal _ support.1] using
      apply_limit (fun cut=>sourceResolvent 0 p F (some cut) event.energy 0) (jointResolvent p F event.energy 0) limit
        (sourceDressedUnit event.epsilon event.precision)
  constructor
  · simpa only [(left _).1] using
      adjoint_apply_limit (fun cut=>sourceResolvent 0 p F (some cut) event.energy 0) (jointResolvent p F event.energy 0) limit
        (sourceDressedUnit event.epsilon event.precision)
  constructor
  · simpa only [retained_right_exact p F _ event.energy event.nonreal _ support.2] using
      apply_limit (fun cut=>sourceResolvent 0 p F (some cut) event.energy 0) (jointResolvent p F event.energy 0) limit
        (prepared (sourceProfile event.epsilon event.precision))
  · simpa only [(left _).2] using
      adjoint_apply_limit (fun cut=>sourceResolvent 0 p F (some cut) event.energy 0) (jointResolvent p F event.energy 0) limit
        (prepared (sourceProfile event.epsilon event.precision))

private theorem pair_limit (J : H→L[ℂ]H) (L R : ℕ→H) (l r : H)
    (left : Tendsto L atTop (𝓝 l)) (right : Tendsto R atTop (𝓝 r)) :
    Tendsto (fun cut=>inner ℂ (L cut) (J (R cut))) atTop (𝓝 (inner ℂ l (J r))) := by
  have applied : Tendsto (fun cut=>J (R cut)) atTop (𝓝 (J r)) := J.continuous.tendsto r |>.comp right
  exact left.inner applied

private theorem euler_cut_same (event : DressedEvent) (cut : ℕ) :
    dressedEulerObserver {event with cut:=cut}=dressedEulerObserver event := by
  unfold dressedEulerObserver
  rfl

private theorem actual_current_euler (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) (cut : ℕ) :
    (∑i : Fin 289,(temporalField a i:ℂ)*sourceDressedConnectedCurrent event.epsilon event.precision event.momentum
      (-transfer) event.frame cut event.energy event.energy i)=
    -dressedEulerObserver event (currentVertex (temporalField a) event.momentum (-transfer) event.frame cut event.energy event.energy) := by
  have source:=dressed_temporal_coulomb_match {event with cut:=cut} transfer a
  have target:=dressed_temporal_cut_noether {event with cut:=cut} transfer a
  have paid : (∑i : Fin 289,(temporalField a i:ℂ)*dressedCurrent {event with cut:=cut} transfer i)=
      -dressedEulerObserver {event with cut:=cut}
        (currentVertex (temporalField a) event.momentum (-transfer) event.frame cut event.energy event.energy) := by
    linear_combination source+target
  simpa only [dressedCurrent,euler_cut_same] using paid

private theorem reader_algebra {A : Type*} [Ring A] (L J N C R : A)
    (reader : J= -N+C) : L*J*R= -(L*N*R)+L*C*R := by
  rw [reader]
  simp only [mul_add,add_mul,mul_neg,neg_mul]

private theorem observed_reader (T : (H→L[ℂ]H)→L[ℂ]ℂ) (L J N C R : H→L[ℂ]H)
    (reader : J= -N+C) : -T (L*J*R)=T (L*N*R)-T (L*C*R) := by
  have algebra:=reader_algebra L J N C R reader
  have paid:=congrArg T algebra
  simp only [map_add,map_neg] at paid
  linear_combination -paid

private theorem uncut_reader_observed (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) : -dressedEulerObserver event
      (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
        currentRestriction (temporalField a) event.momentum event.frame 0*
        jointResolvent event.momentum event.frame event.energy 0)=
      dressedEulerObserver event (dressedNoetherKernel event transfer (temporalField a) 0 0)-
        dressedEulerObserver event
          (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
            temporalReaderCompensation a event.momentum event.frame*
            jointResolvent event.momentum event.frame event.energy 0) := by
  have paid:=observed_reader (dressedEulerObserver event)
    (jointResolvent (event.momentum-transfer) event.frame event.energy 0)
    (currentRestriction (temporalField a) event.momentum event.frame 0)
    (noetherReader (temporalField a) event.momentum event.frame 0)
    (temporalReaderCompensation a event.momentum event.frame)
    (jointResolvent event.momentum event.frame event.energy 0)
    (temporal_reader_generated a event.momentum event.frame)
  simpa only [dressedNoetherKernel,neg_zero,physicalTime_initial,one_mul,mul_one] using paid

private theorem cut_euler_current_limit (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) : Tendsto (fun cut=> -dressedEulerObserver event
      (currentVertex (temporalField a) event.momentum (-transfer) event.frame cut event.energy event.energy)) atTop
      (𝓝 (-dressedEulerObserver event
        (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
          currentRestriction (temporalField a) event.momentum event.frame 0*
          jointResolvent event.momentum event.frame event.energy 0))) := by
  have left:=dressed_two_response_limits event (event.momentum-transfer) event.frame
  have right:=dressed_two_response_limits event event.momentum event.frame
  have unit:=pair_limit (currentRestriction (temporalField a) event.momentum event.frame 0)
    (fun cut=>(finiteFull (event.momentum-transfer) event.frame cut event.energy).adjoint
      (sourceDressedUnit event.epsilon event.precision))
    (fun cut=>finiteFull event.momentum event.frame cut event.energy (sourceDressedUnit event.epsilon event.precision))
    ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint (sourceDressedUnit event.epsilon event.precision))
    (jointResolvent event.momentum event.frame event.energy 0 (sourceDressedUnit event.epsilon event.precision)) left.2.1 right.1
  have background:=pair_limit (currentRestriction (temporalField a) event.momentum event.frame 0)
    (fun cut=>(finiteFull (event.momentum-transfer) event.frame cut event.energy).adjoint
      (prepared (sourceProfile event.epsilon event.precision)))
    (fun cut=>finiteFull event.momentum event.frame cut event.energy (prepared (sourceProfile event.epsilon event.precision)))
    ((jointResolvent (event.momentum-transfer) event.frame event.energy 0).adjoint (prepared (sourceProfile event.epsilon event.precision)))
    (jointResolvent event.momentum event.frame event.energy 0 (prepared (sourceProfile event.epsilon event.precision))) left.2.2.2 right.2.2.1
  have pair:=unit.sub background
  simpa only [currentVertex,dressed_euler_observer_original,mul_apply_eq_comp,ContinuousLinearMap.adjoint_inner_left,
    neg_add,neg_neg,sub_eq_add_neg] using pair

private theorem current_limit_transport (f g : ℕ→ℂ) (v w : ℂ) (same : f=g) (value : v=w)
    (paid : Tendsto g atTop (𝓝 v)) : Tendsto f atTop (𝓝 w) := by
  rw [same,←value]
  exact paid

/-- Both complete actual external legs share one fixed-F cutoff limit; every original reader sector remains in the uncut return. -/
theorem dressed_temporal_common_cut_limit (event : DressedEvent) (transfer : PhysicalMomentum) (a : Fin 12) :
    Tendsto (fun cut=>∑i : Fin 289,(temporalField a i:ℂ)*sourceDressedConnectedCurrent event.epsilon event.precision
      event.momentum (-transfer) event.frame cut event.energy event.energy i) atTop
      (𝓝 (dressedEulerObserver event (dressedNoetherKernel event transfer (temporalField a) 0 0)-
        dressedEulerObserver event
          (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
            temporalReaderCompensation a event.momentum event.frame*
            jointResolvent event.momentum event.frame event.energy 0))) := by
  exact current_limit_transport
    (fun cut=>∑i : Fin 289,(temporalField a i:ℂ)*sourceDressedConnectedCurrent event.epsilon event.precision
      event.momentum (-transfer) event.frame cut event.energy event.energy i)
    (fun cut=> -dressedEulerObserver event
      (currentVertex (temporalField a) event.momentum (-transfer) event.frame cut event.energy event.energy))
    (-dressedEulerObserver event
      (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
        currentRestriction (temporalField a) event.momentum event.frame 0*
        jointResolvent event.momentum event.frame event.energy 0))
    (dressedEulerObserver event (dressedNoetherKernel event transfer (temporalField a) 0 0)-
      dressedEulerObserver event
        (jointResolvent (event.momentum-transfer) event.frame event.energy 0*
          temporalReaderCompensation a event.momentum event.frame*
          jointResolvent event.momentum event.frame event.energy 0))
    (funext (actual_current_euler event transfer a)) (uncut_reader_observed event transfer a)
    (cut_euler_current_limit event transfer a)

private theorem product_apply_price (L D : H→L[ℂ]H) (y : H) (ell delta : ℝ)
    (left : ‖L‖≤ell) (middle : ‖D‖≤delta) : ‖L (D y)‖≤ell*delta*‖y‖ := by
  have product : ‖L*D‖≤ell*delta :=
    (norm_mul_le L D).trans (mul_le_mul left middle (norm_nonneg D) ((norm_nonneg L).trans left))
  exact ((L*D).le_opNorm y).trans (mul_le_mul_of_nonneg_right product (norm_nonneg y))

private theorem right_price (L U D E : H→L[ℂ]H) (x : H) (ell delta : ℝ)
    (returned : L=U+L*(D+E)*U) (leak : E (U x)=0) (left : ‖L‖≤ell) (middle : ‖D‖≤delta) :
    ‖L x-U x‖≤ell*delta*‖U x‖ := by
  have value:=congrArg (fun A : H→L[ℂ]H=>A x) returned
  simp only [add_apply,mul_apply_eq_comp,leak,add_zero] at value
  rw [value,add_sub_cancel_left]
  exact product_apply_price L D (U x) ell delta left middle

private theorem left_price (L U D E : H→L[ℂ]H) (x y : H) (delta : ℝ)
    (returned : L=U+L*(D+E)*U) (leak : inner ℂ x (L (E (U y)))=0) (middle : ‖D‖≤delta) :
    ‖inner ℂ x (L y-U y)‖≤‖L.adjoint x‖*delta*‖U y‖ := by
  have value:=congrArg (fun A : H→L[ℂ]H=>inner ℂ x (A y)) returned
  simp only [add_apply,mul_apply_eq_comp,map_add,inner_add_right,leak,add_zero] at value
  have read : inner ℂ x (L y-U y)=inner ℂ x (L (D (U y))) := by
    rw [inner_sub_right]
    linear_combination value
  rw [read,←L.adjoint_inner_left]
  have applied : ‖D (U y)‖≤delta*‖U y‖ :=
    (D.le_opNorm (U y)).trans (mul_le_mul_of_nonneg_right middle (norm_nonneg (U y)))
  have bound:=(norm_inner_le_norm (𝕜:=ℂ) (L.adjoint x) (D (U y))).trans
    (mul_le_mul_of_nonneg_left applied (norm_nonneg (L.adjoint x)))
  simpa only [mul_assoc] using bound

/-- Actual right-response prices contain the original jet error and no localization-leak budget. -/
theorem dressed_right_cut_error_price (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (n : ℕ) :
    ‖finiteFull p F (n+1) event.energy (sourceDressedUnit event.epsilon event.precision)-
        jointResolvent p F event.energy 0 (sourceDressedUnit event.epsilon event.precision)‖≤
      normBound (n+1) event.energy*errorBound 0 (finiteRetainer p F) 0 n 0*
        ‖jointResolvent p F event.energy 0 (sourceDressedUnit event.epsilon event.precision)‖ ∧
    ‖finiteFull p F (n+1) event.energy (prepared (sourceProfile event.epsilon event.precision))-
        jointResolvent p F event.energy 0 (prepared (sourceProfile event.epsilon event.precision))‖≤
      normBound (n+1) event.energy*errorBound 0 (finiteRetainer p F) 0 n 0*
        ‖jointResolvent p F event.energy 0 (prepared (sourceProfile event.epsilon event.precision))‖ := by
  have returned:=cut_resolvent_return p F (n+1) event.energy event.nonreal
  have leak:=dressed_original_right_leak event p F (n+1)
  exact ⟨right_price (finiteFull p F (n+1) event.energy) (jointResolvent p F event.energy 0)
      (cutJetError p F (n+1)) (cutRetainerLeak p F (n+1)) (sourceDressedUnit event.epsilon event.precision)
      (normBound (n+1) event.energy) (errorBound 0 (finiteRetainer p F) 0 n 0) returned leak.1
      (finiteFull_bound p F (n+1) event.energy event.nonreal) (cut_jet_error_price p F n),
    right_price (finiteFull p F (n+1) event.energy) (jointResolvent p F event.energy 0)
      (cutJetError p F (n+1)) (cutRetainerLeak p F (n+1)) (prepared (sourceProfile event.epsilon event.precision))
      (normBound (n+1) event.energy) (errorBound 0 (finiteRetainer p F) 0 n 0) returned leak.2
      (finiteFull_bound p F (n+1) event.energy event.nonreal) (cut_jet_error_price p F n)⟩

/-- The actual independent left functional has its original weighted Riesz norm and the same source-generated jet error. -/
theorem dressed_left_cut_error_price (event : DressedEvent) (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (y : H) :
    ‖inner ℂ (sourceDressedUnit event.epsilon event.precision)
        (finiteFull p F (n+1) event.energy y-jointResolvent p F event.energy 0 y)‖≤
      ‖(finiteFull p F (n+1) event.energy).adjoint (sourceDressedUnit event.epsilon event.precision)‖*
        errorBound 0 (finiteRetainer p F) 0 n 0*‖jointResolvent p F event.energy 0 y‖ ∧
    ‖inner ℂ (prepared (sourceProfile event.epsilon event.precision))
        (finiteFull p F (n+1) event.energy y-jointResolvent p F event.energy 0 y)‖≤
      ‖(finiteFull p F (n+1) event.energy).adjoint (prepared (sourceProfile event.epsilon event.precision))‖*
        errorBound 0 (finiteRetainer p F) 0 n 0*‖jointResolvent p F event.energy 0 y‖ := by
  have returned:=cut_resolvent_return p F (n+1) event.energy event.nonreal
  have leak:=dressed_left_leak_zero event p F (n+1) (jointResolvent p F event.energy 0 y)
  exact ⟨left_price (finiteFull p F (n+1) event.energy) (jointResolvent p F event.energy 0)
      (cutJetError p F (n+1)) (cutRetainerLeak p F (n+1)) (sourceDressedUnit event.epsilon event.precision) y
      (errorBound 0 (finiteRetainer p F) 0 n 0) returned leak.1 (cut_jet_error_price p F n),
    left_price (finiteFull p F (n+1) event.energy) (jointResolvent p F event.energy 0)
      (cutJetError p F (n+1)) (cutRetainerLeak p F (n+1)) (prepared (sourceProfile event.epsilon event.precision)) y
      (errorBound 0 (finiteRetainer p F) 0 n 0) returned leak.2.2.1 (cut_jet_error_price p F n)⟩

end LowEnergy.GaussComposite.ActualDressedCofinal
