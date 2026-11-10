import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedNoetherChargeReturn

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedNoetherCoulombUnit
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn PreparationVacuumPhysicalFeedback
open ActualCompositeFieldCurrent ActualEMCurrentSplit ActualEMResponseSplit ActualEMCarrierOwn
open ActualDressedFullCoulomb ActualDressedCorrectedGreen ActualDressedCorrectedElectronRead
open ActualDressedEMTensorClock ActualDressedOrderedStatic Filter Set
open scoped Matrix BigOperators Topology
attribute [local irreducible] correctedEMTensor correctedGreen ActualCompositeFieldCurrent.compositeCurrent

def noetherPairScale : ℂ := (4/3:ℂ)*(Stage10.ActionNormalization.phaseMomentum : ℂ)

def noetherTensorCoefficient (event : DressedEvent) (n : PhysicalMomentum) : Matrix (Fin 4) (Fin 4) ℂ :=
  noetherPairScale^2 • sourceOrderedEMCoefficient event n

def noetherPureRead (event : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (noetherEMCurrent pd dL dR)
    ((noetherPairScale^2 • correctedEMTensor event eps 0 sigma n)*ᵥnoetherEMCurrent ps sL sR)

def zeroNoetherPureRead (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (noetherEMCurrent pd dL dR)
    ((noetherPairScale^2 • zeroClockEMRead event eps n)*ᵥnoetherEMCurrent ps sL sR)

def noetherPureCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  dotProduct (noetherEMCurrent pd dL dR)
    (noetherTensorCoefficient event n*ᵥnoetherEMCurrent ps sL sR)

private theorem actual_unit_tensor_read (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (T : Matrix (Fin 4) (Fin 4) ℂ) :
    dotProduct (emCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent pd dL dR))
      (T*ᵥemCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent ps sL sR))=
    dotProduct (noetherEMCurrent pd dL dR) ((noetherPairScale^2 • T)*ᵥnoetherEMCurrent ps sL sR) := by
  rw [actual_coordinate_noether_unit,actual_coordinate_noether_unit]
  simp only [Matrix.mulVec_smul,Matrix.smul_mulVec,smul_dotProduct,dotProduct_smul,smul_eq_mul,noetherPairScale]
  ring

/-- The factor is the paid original action reader at both endpoints and its literal Gram, not a dimensional assignment. -/
theorem actual_noether_pure_read (event : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    noetherPureRead event eps sigma n pd ps dL dR sL sR=
      dotProduct (emCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent pd dL dR))
        (correctedEMTensor event eps 0 sigma n*ᵥemCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent ps sL sR)) :=
  (actual_unit_tensor_read pd ps dL dR sL sR _).symm

def actualNonPureRead (event : DressedEvent) (eps sigma : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  let G := correctedGreen event eps 0 sigma n
  let fd := ActualCompositeFieldCurrent.compositeCurrent pd dL dR
  let fs := ActualCompositeFieldCurrent.compositeCurrent ps sL sR
  emCurrentObservation G (emCurrentForce fd) (emCurrentResidual fs)+
    emCurrentObservation G (emCurrentResidual fd) (emCurrentForce fs)+
    emCurrentObservation G (emCurrentResidual fd) (emCurrentResidual fs)

theorem actual_noether_four_parts (event : DressedEvent) (eps sigma : ℝ)
    (n pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    correctedProbeRead event eps 0 sigma n pd ps dL dR sL sR=
      noetherPureRead event eps sigma n pd ps dL dR sL sR+actualNonPureRead event eps sigma n pd ps dL dR sL sR := by
  rw [actual_probe_tensor_four_parts,actual_noether_pure_read]
  dsimp only [actualNonPureRead]
  ring

def zeroNonPureRead (event : DressedEvent) (eps : ℝ) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  zeroClockProbeRead event eps n pd ps dL dR sL sR-zeroNoetherPureRead event eps n pd ps dL dR sL sR

def noetherNonPureCoefficient (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) : ℂ :=
  sourceOrderedProbeCoefficient event n pd ps dL dR sL sR-noetherPureCoefficient event n pd ps dL dR sL sR

private theorem pure_observation_continuous (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) :
    Continuous (fun T : Matrix (Fin 4) (Fin 4) ℂ =>
      dotProduct (noetherEMCurrent pd dL dR) ((noetherPairScale^2 • T)*ᵥnoetherEMCurrent ps sL sR)) := by
  unfold dotProduct Matrix.mulVec
  fun_prop

private theorem pure_observation_smul (pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg)
    (a : ℂ) (T : Matrix (Fin 4) (Fin 4) ℂ) :
    dotProduct (noetherEMCurrent pd dL dR) ((noetherPairScale^2 • (a • T))*ᵥnoetherEMCurrent ps sL sR)=
      a*dotProduct (noetherEMCurrent pd dL dR) ((noetherPairScale^2 • T)*ᵥnoetherEMCurrent ps sL sR) := by
  rw [smul_comm,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]

/-- The unchanged full response generates the Noether-unit tensor piece and the complete sum of all three non-pure pieces, in the physical limit order. -/
theorem actual_noether_coulomb_split_return (event : DressedEvent) (n pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) (nonzero : irClockDeterminant event n≠0)
    (clock : ClockFinite event n pd ps dL dR sL sR)
    (emBounded : ∀mu nu,LowEnergy.ActualDressedVisiblePole.poleOrder (zeroClockEMFraction event n mu nu) 0≤4)
    (probeBounded : LowEnergy.ActualDressedVisiblePole.poleOrder (zeroClockProbeFraction event n pd ps dL dR sL sR) 0≤4) :
    (∀ᶠ kappa : ℝ in nhdsWithin 0 (Ioi 0),
      Tendsto (fun sigma : ℝ => noetherPureRead event (Real.sqrt kappa) sigma n pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroNoetherPureRead event (Real.sqrt kappa) n pd ps dL dR sL sR)) ∧
      Tendsto (fun sigma : ℝ => actualNonPureRead event (Real.sqrt kappa) sigma n pd ps dL dR sL sR)
        (nhdsWithin 0 (Ioi 0)) (𝓝 (zeroNonPureRead event (Real.sqrt kappa) n pd ps dL dR sL sR))) ∧
    Tendsto (fun kappa : ℝ => -(kappa : ℂ)^2*zeroNoetherPureRead event (Real.sqrt kappa) n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (noetherPureCoefficient event n pd ps dL dR sL sR)) ∧
    Tendsto (fun kappa : ℝ => -(kappa : ℂ)^2*zeroNonPureRead event (Real.sqrt kappa) n pd ps dL dR sL sR)
      (nhdsWithin 0 (Ioi 0)) (𝓝 (noetherNonPureCoefficient event n pd ps dL dR sL sR)) := by
  have paid := actual_ordered_coulomb_return event n pd ps dL dR sL sR nonzero clock emBounded probeBounded
  have observer := pure_observation_continuous pd ps dL dR sL sR
  have spatialPure := observer.continuousAt.tendsto.comp paid.2.1
  simp only [Function.comp_def,pure_observation_smul] at spatialPure
  refine ⟨?_,spatialPure,?_⟩
  · filter_upwards [paid.1] with kappa limits
    have pure := observer.continuousAt.tendsto.comp limits.1
    simp only [Function.comp_def] at pure
    refine ⟨pure,?_⟩
    have remainder := limits.2.sub pure
    apply Tendsto.congr' _ remainder
    filter_upwards with sigma
    have split := actual_noether_four_parts event (Real.sqrt kappa) sigma n pd ps dL dR sL sR
    change correctedProbeRead event (Real.sqrt kappa) 0 sigma n pd ps dL dR sL sR-
      noetherPureRead event (Real.sqrt kappa) sigma n pd ps dL dR sL sR=
        actualNonPureRead event (Real.sqrt kappa) sigma n pd ps dL dR sL sR
    linear_combination split
  · have combined := paid.2.2.sub spatialPure
    simpa only [zeroNonPureRead,zeroNoetherPureRead,noetherNonPureCoefficient,noetherPureCoefficient,
      noetherTensorCoefficient,mul_sub] using combined

end LowEnergy.GaussComposite.ActualDressedNoetherCoulombUnit
