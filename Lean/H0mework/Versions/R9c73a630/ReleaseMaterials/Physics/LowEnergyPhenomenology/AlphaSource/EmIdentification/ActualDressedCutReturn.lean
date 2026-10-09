import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedTemporalCurrent

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedCutReturn
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


open CanonicalPhysicalSpatial CanonicalPhysicalYResolvent FullYSourceCutoffVolterra
open PreparationVacuumUncutYukawa PreparationVacuumYukawaTransport
attribute [local irreducible] cutoff uncutOperator jetOperator jointResolvent jointGenerator retainer fieldCutoff

/-- Original finite-retainer jet truncation, before any retainer support claim. -/
def cutJetError (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) : H→L[ℂ]H :=
  uncutOperator 0 (finiteRetainer p F) 0-jetOperator 0 cut 0 (finiteRetainer p F) 0

/-- The original full-H cutoff and the finite-retainer operator differ by this concrete localization term. -/
def cutRetainerLeak (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) : H→L[ℂ]H :=
  (retainer p F-1)*cutoff cut

theorem cut_tail_generated (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (cut : ℕ) :
    uncutOperator 0 (finiteRetainer p F) 0-cutoff cut=cutJetError p F cut+cutRetainerLeak p F cut := by
  have jet : jetOperator 0 cut 0 (finiteRetainer p F) 0=retainer p F*cutoff cut :=
    (jetOperator_cutoff (0:Field289) cut p F (0:ℝ)).trans
      (congrArg (fun X : H→L[ℂ]H=>retainer p F*X) (fieldCutoff_zero (0:Field289) cut))
  change uncutOperator 0 (finiteRetainer p F) 0-cutoff cut=
    uncutOperator 0 (finiteRetainer p F) 0-jetOperator 0 cut 0 (finiteRetainer p F) 0+(retainer p F-1)*cutoff cut
  rw [jet]
  simp only [sub_mul,one_mul]
  abel

theorem cut_jet_error_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (n : ℕ) :
    ‖cutJetError p F (n+1)‖≤errorBound 0 (finiteRetainer p F) 0 n 0 := by
  exact operator_error_bound 0 (finiteRetainer p F) 0 0 (by norm_num) n 0

theorem cut_retainer_leak_retained (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (x : H) (hx : x∈retainedSpace p F) : cutRetainerLeak p F cut x=0 := by
  have kept:=fieldCutoff_retained 0 cut p F 0 x hx
  rw [fieldCutoff_zero (0:Field289) cut] at kept
  change retainer p F (cutoff cut x)-cutoff cut x=0
  rw [(retainedSpace_iff p F (cutoff cut x)).mp kept,sub_self]

/-- The uncut denominator is the same compression and spectral shift plus the original uncut Yukawa coefficient. -/
theorem joint_generator_original (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index) (z : ℂ) :
    jointGenerator p F z 0=compression p F+uncutOperator 0 (finiteRetainer p F) 0-z • 1 := by
  have paid:=(jointGenerator_ray (0:Field289) p F z).self_of_nhds
  simp only [zero_smul] at paid
  rw [paid]
  change transportedCompression 0 p F 0+uncutOperator 0 (finiteRetainer p F) 0-z • 1=_
  exact congrArg (fun C : H→L[ℂ]H=>C+uncutOperator 0 (finiteRetainer p F) 0-z • 1)
    (transportedCompression_zero (0:Field289) p F)

private theorem inverse_return {A : Type*} [Ring A] (C U L R D : A)
    (left : L*C=1) (right : U*R=1) (tail : U=C+D) : L=R+L*D*R := by
  have generated : L*D*R=L-R := by
    have delta : D=U-C := by rw [tail];abel
    rw [delta,mul_sub,sub_mul,mul_assoc,right,mul_one,left,one_mul]
  rw [generated]
  abel

private theorem denominator_tail {A : Type*} [AddCommGroup A] (C U Y Z D : A)
    (tail : U-Y=D) : C+U-Z=(C+Y-Z)+D := by
  rw [←tail]
  abel

/-- Both resolvents remain the original operators; their exact correction is generated from the jet error and retainer leak. -/
theorem cut_resolvent_return (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (cut : ℕ) (z : ℂ) (nonreal : z.im≠0) :
    finiteFull p F cut z=jointResolvent p F z 0+
      finiteFull p F cut z*(cutJetError p F cut+cutRetainerLeak p F cut)*jointResolvent p F z 0 := by
  apply inverse_return (compression p F+cutoff cut-z • 1) (jointGenerator p F z 0)
    (finiteFull p F cut z) (jointResolvent p F z 0) (cutJetError p F cut+cutRetainerLeak p F cut)
    (finiteFull_left p F cut z nonreal)
    (by unfold jointResolvent;exact Ring.mul_inverse_cancel (jointGenerator p F z 0) (jointGenerator_unit p F z nonreal))
  exact (joint_generator_original p F z).trans
    (denominator_tail (compression p F) (uncutOperator 0 (finiteRetainer p F) 0) (cutoff cut) (z • 1)
      (cutJetError p F cut+cutRetainerLeak p F cut) (cut_tail_generated p F cut))

private theorem sum_price {A : Type*} [SeminormedAddCommGroup A] (D E : A) (d : ℝ)
    (price : ‖D‖≤d) : ‖D+E‖≤d+‖E‖ :=
  (norm_add_le D E).trans (add_le_add price (le_refl ‖E‖))

private theorem triple_price {A : Type*} [SeminormedRing A] (L D R : A) (l d : ℝ)
    (left : ‖L‖≤l) (middle : ‖D‖≤d) : ‖L*D*R‖≤l*d*‖R‖ :=
  (norm_mul_le (L*D) R).trans (mul_le_mul_of_nonneg_right
    ((norm_mul_le L D).trans (mul_le_mul left middle (norm_nonneg D) ((norm_nonneg L).trans left))) (norm_nonneg R))

/-- The source-provided jet remainder price is separate from the actual retainer mismatch. -/
theorem cut_resolvent_error_price (p : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (n : ℕ) (z : ℂ) (nonreal : z.im≠0) :
    ‖finiteFull p F (n+1) z-jointResolvent p F z 0‖≤
      normBound (n+1) z*(errorBound 0 (finiteRetainer p F) 0 n 0+‖cutRetainerLeak p F (n+1)‖)*
        ‖jointResolvent p F z 0‖ := by
  rw [cut_resolvent_return p F (n+1) z nonreal,add_sub_cancel_left]
  exact triple_price (finiteFull p F (n+1) z) (cutJetError p F (n+1)+cutRetainerLeak p F (n+1))
    (jointResolvent p F z 0) (normBound (n+1) z)
    (errorBound 0 (finiteRetainer p F) 0 n 0+‖cutRetainerLeak p F (n+1)‖)
    (finiteFull_bound p F (n+1) z nonreal)
    (sum_price (cutJetError p F (n+1)) (cutRetainerLeak p F (n+1))
      (errorBound 0 (finiteRetainer p F) 0 n 0) (cut_jet_error_price p F n))

end LowEnergy.GaussComposite.ActualDressedCutReturn
