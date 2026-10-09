import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualFullWardResponse
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteObservationSoftLimit

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalActualRetardedWard
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open FullQuantum FullSpace
open PreparationPhysicalFiniteTransferWard PreparationPhysicalFiniteObservationSoftReturn
open PreparationPhysicalNativeWardFiniteObservation PreparationPhysicalNativeSoftWardBoundary
open PreparationPhysicalChargedSoftScatteringReturn PreparationPhysicalJointGeneratorEnergyReturn
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalFiniteOriginCovariance
open PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet CanonicalGradedSpatialSource
open Electromagnetic.CanonicalCoframe MatterSpace.Response
open MeasureTheory Filter
open scoped Topology InnerProductSpace BigOperators
attribute [local irreducible] sourceChargedCoupledScattering sourceActualWardBoundary sourceActualWardRate
  sourceActualWardCorrection sourceActualFieldTail sourceActualFullContact sourcePhysicalResidueWindow

private theorem weight_continuous (energy damping T : ℝ) : Continuous (sourceWindowWeight energy damping T) :=
  (temporalWeight_continuous energy damping).comp (continuous_const.sub continuous_id)
private theorem weight_derivative (energy damping T age : ℝ) :
    HasDerivAt (sourceWindowWeight energy damping T)
      (-(sourceWindowWeight energy damping T age*sourceWindowExponent energy damping)) age := by
  have generated:=(Retarded.temporalWeight_derivative energy damping (T-age)).scomp age
    ((hasDerivAt_id age).const_sub T)
  convert! generated using 1
  simp only [sourceWindowWeight,sourceWindowExponent,_root_.neg_one_smul]

/-- The original lag T-age produces kappa=-damping+i*energy; neither observation parameter is fixed by a charge label. -/
theorem sourceActualWard_retarded (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (e : scaleDomain) (energy damping T : ℝ) :
    (∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
      sourceActualWardRate sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age)=
    sourceActualWardBoundary sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T T+
    sourceWindowExponent energy damping*(∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
      sourceActualWardBoundary sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age) := by
  have generated:=intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun age _=>weight_derivative energy damping T age)
    (fun age _=>sourceActualWard_derivative sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age)
    (((weight_continuous energy damping T).mul_const (sourceWindowExponent energy damping)).neg.intervalIntegrable (0:ℝ) T)
    ((sourceActualWardRate_continuous sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T).intervalIntegrable (0:ℝ) T)
  rw [generated]
  have integrand (age : ℝ) :
      -(sourceWindowWeight energy damping T age*sourceWindowExponent energy damping)*
        sourceActualWardBoundary sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age=
      -sourceWindowExponent energy damping*(sourceWindowWeight energy damping T age*
        sourceActualWardBoundary sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age) := by ring
  simp_rw [integrand]
  rw [intervalIntegral.integral_const_mul,sourceWindowWeight_final,sourceActualWardBoundary_initial]
  ring

/-- The entire same-source observation: actual finite boundary, kappa read, source momentum/Yukawa corrections, all other field crosses, and separate direct contact. -/
def sourceActualRetardedValue (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (e : scaleDomain) : ℂ × ℂ :=
  (sourceActualWardBoundary sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T T+
    sourceWindowExponent energy damping*(∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
      sourceActualWardBoundary sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age)+
    ∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
      (sourceActualWardCorrection sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age+
       sourceActualFieldTail sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age),
    sourceActualScatteringRead sideL edgeL sideR edgeR (contactWord
      (sourceActualFullContact (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e) T))

/-- The original normalized physical-frequency residue window is exactly this complete source Ward observation. -/
theorem sourceActualRetardedWard_return (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) :
    ∀ᶠ e in scaleApproach,
      (2*(sourceFrequency e.val (sourceSheet branch n unit e.val):ℂ))^2 •
        sourcePhysicalResidueWindow sideL edgeL sideR edgeR legs branch n unit energy damping T e=
      sourceActualRetardedValue sideL edgeL sideR edgeR legs branch n unit energy damping T e := by
  filter_upwards [sourceActualFullWard_return sideL edgeL sideR edgeR legs branch n unit] with e returned
  have remainder : Continuous (fun age=>
      sourceActualWardCorrection sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age+
      sourceActualFieldTail sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age) := by
    have same : (fun age=>
        sourceActualWardCorrection sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age+
        sourceActualFieldTail sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age)=
        (fun age=>(sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1-
          sourceActualWardRate sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age) := by
      funext age
      rw [returned T age]
      dsimp only [Prod.fst]
      ring
    rw [same]
    exact (sourceActualCoupled_age_continuous sideL edgeL sideR edgeR legs branch n unit T e).sub
      (sourceActualWardRate_continuous sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T)
  rw [←sourcePhysicalResidueWindow_normalization]
  unfold sourceCoupledCausalWindow sourceActualRetardedValue
  apply Prod.ext
  · dsimp only [Prod.fst]
    have integral :
        (∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
          (sourceChargedCoupledScattering sideL edgeL sideR edgeR legs branch n unit T age e).1)=
        ∫age in (0:ℝ)..T,
          (sourceWindowWeight energy damping T age*
            sourceActualWardRate sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age+
          sourceWindowWeight energy damping T age*
            (sourceActualWardCorrection sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age+
             sourceActualFieldTail sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T age)) := by
      apply intervalIntegral.integral_congr
      intro age _
      dsimp only []
      rw [returned T age]
      dsimp only [Prod.fst]
      ring
    have separated:=intervalIntegral.integral_add (μ:=volume)
      (((weight_continuous energy damping T).mul
        (sourceActualWardRate_continuous sideL edgeL sideR edgeR (legs 0) (legs 1) (legs 2) (legs 3) branch n unit e T)).intervalIntegrable (μ:=volume) (0:ℝ) T)
      (((weight_continuous energy damping T).mul remainder).intervalIntegrable (μ:=volume) (0:ℝ) T)
    simp only [Pi.mul_apply] at separated
    rw [integral,separated,sourceActualWard_retarded]
  · dsimp only [Prod.snd]
    have contact:=congrArg (fun pair : ℂ × ℂ=>pair.2) (returned T T)
    exact contact

/-- The already source-priced fixed-window DCT consumes this same finite Ward object; no separate correction/contact limit is assumed. -/
theorem sourceActualRetardedWard_soft (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (future : 0≤T) (positive : 0<damping)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (sourceActualRetardedValue sideL edgeL sideR edgeR legs branch n unit energy damping T) scaleApproach
      (𝓝 (sourceFiniteCausalPair sideL edgeL sideR edgeR legs branch energy damping T)) :=
  (sourcePhysicalResidueWindow_soft sideL edgeL sideR edgeR legs branch n unit energy damping T future positive nonrealL nonrealR).congr'
    (sourceActualRetardedWard_return sideL edgeL sideR edgeR legs branch n unit energy damping T)

/-- Both source branches, all four independent currents, and the original retarded preparation boundary are one actual observable. -/
theorem sourceActualRetardedWard_observation (sideL edgeL sideR edgeR : Fin 2)
    (legs : Fin 4→SourceChargedSoftLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (energy damping T : ℝ) (future : 0≤T) (positive : 0<damping)
    (nonrealL : ∀i,(legs i).q.z.im≠0) (nonrealR : ∀i,(legs i).q.w.im≠0) :
    Tendsto (sourceActualRetardedValue sideL edgeL sideR edgeR legs branch n unit energy damping T) scaleApproach
      (𝓝 (sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T T+
        sourceWindowExponent energy damping*(∫age in (0:ℝ)..T,sourceWindowWeight energy damping T age*
          sourcePhysicalSoftBoundary sideL edgeL sideR edgeR legs branch T age),0)) := by
  have generated:=sourceActualRetardedWard_soft sideL edgeL sideR edgeR legs branch n unit energy damping T future positive nonrealL nonrealR
  rw [sourceFiniteCausalPair_return sideL edgeL sideR edgeR legs branch energy damping T future] at generated
  exact generated

end LowEnergy.PreparationPhysicalActualRetardedWard
