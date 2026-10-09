import H0mework.Versions.R9c73a630.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFinitePoleCoefficients

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFinitePoleVertices
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldCovector
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalScatteringFrequencyWard
open PreparationPhysicalNativePhotonScatteringSheetReturn PreparationPhysicalJointGeneratorEnergyReturn
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe
open FullQuantum FullSpace Filter
open scoped BigOperators Matrix Topology
attribute [local irreducible] complexCoefficients complexFrequencyCoefficients complexMixedCoefficients
  realReaderCoefficients realMixedCoefficients sourcePreparedScatteringPair sourceActualScatteringRead
  sourceFinitePoleDensity sourceFinitePoleFrequency sourceFinitePoleMixed sourcePhotonEmitter

/-- The amplitude is the actual current emitter, with its own source preparation and window. -/
def sourceFinitePhotonDensity (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    Fin 4→FiberOperators := sourcePhotonEmitter leg branch epsilon s n • sourceFinitePoleDensity branch epsilon s n

def sourceFinitePhotonFrequency (leg : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    Fin 4→FiberOperators := sourcePhotonEmitter leg branch epsilon s n • sourceFinitePoleFrequency branch epsilon s n

/-- The negative source and shifted adjoint positive source retain their original order. -/
def sourceFinitePhotonReader (Ap An : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    Fin 4→FiberOperators :=
  (2:ℂ)⁻¹ • (sourceFinitePhotonDensity An branch epsilon s n+
    adjointCoefficients (shiftCoefficients (sourceFinitePhotonDensity Ap branch epsilon s n) (-(epsilon^2 • n))))

/-- Both mixed source contacts retain all nine field crosses and the original complex adjoint. -/
def sourceFinitePhotonContact (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  (2:ℂ)⁻¹ • ((sourcePhotonEmitter An branch epsilon s n*sourcePhotonEmitter Bp branch epsilon s n) •
    sourceFinitePoleMixed branch epsilon s n+
    adjointCoefficients ((sourcePhotonEmitter Ap branch epsilon s n*sourcePhotonEmitter Bn branch epsilon s n) •
      sourceFinitePoleMixed branch epsilon s n))

theorem sourceFinitePhotonCoefficients_return (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀leg : SourcePhotonLeg,
      complexCoefficients (originalComplexDirection (sourcePhotonFrequencyResidue leg e.val
        (sourceSheet branch n unit e.val) n))=sourceFinitePhotonDensity leg branch e.val (sourceSheet branch n unit e.val) n ∧
      complexFrequencyCoefficients (originalComplexDirection (sourcePhotonFrequencyResidue leg e.val
        (sourceSheet branch n unit e.val) n))=sourceFinitePhotonFrequency leg branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourcePhotonFrequencyResidue_fluxFactor branch n unit] with e factor
  intro leg
  rw [factor leg]
  exact ⟨sourceFinitePoleDensity_actual _ _ _ _ _ e.property.1.ne',
    sourceFinitePoleFrequency_actual _ _ _ _ _ e.property.1.ne'⟩

theorem sourceFinitePhotonTransfer_return (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1) :
    ∀ᶠ e in scaleApproach,∀Ap An Bp Bn : SourcePhotonLeg,
      realReaderCoefficients (sourcePhotonFrequencyResidueTransfer Ap An e.val (sourceSheet branch n unit e.val) n)
        (e.val^2 • n)=sourceFinitePhotonReader Ap An branch e.val (sourceSheet branch n unit e.val) n ∧
      realMixedCoefficients (sourcePhotonFrequencyResidueTransfer Ap An e.val (sourceSheet branch n unit e.val) n)
        (sourcePhotonFrequencyResidueTransfer Bp Bn e.val (sourceSheet branch n unit e.val) n)=
          sourceFinitePhotonContact Ap An Bp Bn branch e.val (sourceSheet branch n unit e.val) n := by
  filter_upwards [sourceFinitePhotonCoefficients_return branch n unit,sourcePhotonFrequencyResidue_fluxFactor branch n unit]
    with e coefficients factor
  intro Ap An Bp Bn
  constructor
  · funext k
    simp only [realReaderCoefficients,sourcePhotonFrequencyResidueTransfer,originalTransferPair,
      (coefficients An).1,(coefficients Ap).1,sourceFinitePhotonReader,Pi.smul_apply,Pi.add_apply]
  · funext k
    simp only [realMixedCoefficients,sourcePhotonFrequencyResidueTransfer,originalTransferPair,
      factor Ap,factor An,factor Bp,factor Bn,sourceFinitePoleMixed_actual _ _ _ _ _ _ e.property.1.ne',
      sourceFinitePhotonContact,adjointCoefficients,Pi.smul_apply,Pi.add_apply]

/-- Exact finite-frequency response on the same actual normalized preparations; direct contact has no age integral. -/
def sourceFinitePoleResponse (sideL edgeL sideR edgeR : Fin 2) (Ap An Bp Bn : SourcePhotonLeg)
    (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (time age : ℝ) : ℂ × ℂ :=
  let J:=sourceFinitePhotonReader Ap An branch epsilon s n
  let Fp:=sourceFinitePhotonFrequency Bp branch epsilon s n
  let backward:=shiftCoefficients (adjointCoefficients (sourceFinitePhotonFrequency Bn branch epsilon s n)) (epsilon^2 • n)
  (sourceActualScatteringRead sideL edgeL sideR edgeR
    (Complex.I • (orderedWord backward J (-(epsilon^2 • n)) age time-orderedWord J Fp (epsilon^2 • n) time age)),
    sourceActualScatteringRead sideL edgeL sideR edgeR
      (contactWord (sourceFinitePhotonContact Ap An Bp Bn branch epsilon s n) time))

/-- All four actual physical-frequency residue legs enter the original prepared scattering consumer. -/
theorem sourcePhotonScatteringFrequencyResidue_finite (sideL edgeL sideR edgeR : Fin 2)
    (Ap An Bp Bn : SourcePhotonLeg) (branch : Fin 2) (n : PhysicalMomentum) (unit : spatialSquare n=1)
    (time age : ℝ) :
    ∀ᶠ e in scaleApproach,
      sourcePhotonScatteringFrequencyResidue sideL edgeL sideR edgeR Ap An Bp Bn e.val (sourceSheet branch n unit e.val) n time age=
        sourceFinitePoleResponse sideL edgeL sideR edgeR Ap An Bp Bn branch e.val (sourceSheet branch n unit e.val) n time age := by
  filter_upwards [sourceFinitePhotonTransfer_return branch n unit,sourceFinitePhotonCoefficients_return branch n unit]
    with e transfer coefficients
  simp only [sourcePhotonScatteringFrequencyResidue,sourcePreparedScatteringPair,fieldTwoTimeKernel,fieldMixedContact]
  rw [(transfer Ap An Bp Bn).1,(transfer Ap An Bp Bn).2]
  simp only [sourcePhotonFrequencyResidueTransfer,originalTransferPair,(coefficients Bn).2,(coefficients Bp).2,
    sourceFinitePoleResponse]

end LowEnergy.PreparationPhysicalFinitePoleVertices
