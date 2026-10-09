import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteOriginConfiguration
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeOriginEnergyWard
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourcePhaseChargeProjection
import H0mework.Versions.Rf13ed87d.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNativeSoftWardReturn

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteOriginCovariance
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativeOriginPhaseWard
open PreparationPhysicalNativePhaseChargeInventory PreparationPhysicalFinitePoleVertices
open PreparationVacuumMixedFieldReturn PreparationVacuumSoftPoleSelection
open PreparationPhysicalChargedSoftObservable PreparationPhysicalScatteringFrequencyWard
open PreparationPhysicalNormalizedFullField PreparationPhysicalChargedHamiltonianRead PreparationPhysicalEnergyCurrentWardReturn
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe
open FullQuantum FullSpace YangMills.FullPairing CanonicalGradedSpatialSource
open PreparationPhysicalNativeSoftWardBoundary PreparationPhysicalNativePhotonScatteringSheetReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalChargedPacketQuantumReturn
open MeasureTheory
open scoped Matrix BigOperators
attribute [local irreducible] sourcePoleOriginField sourcePoleLiteralJet sourcePoleFastJet sourcePoleFrameResidual
  nativeBranchVector sourceNativeOriginReal sourceNativeOriginGenerator sourceNativeOriginCanonicalFiber
  sourceFiniteOriginAmplitude complexCoefficients complexFrequencyCoefficients complexMixedCoefficients

/-- Only the original bosonic action reader is identified; the full field remainder survives in the nine-field configuration theorem. -/
theorem sourceFiniteOrigin_actionDirection (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) :
    originalComplexDirection (sourcePoleOriginField branch epsilon s n)=
      originalComplexDirection (sourceFiniteOriginAmplitude branch epsilon s n • nativeBranchVector 0) := by
  have scaled (imaginary : Bool) :
      (fun i=>sourceOriginPart imaginary ((sourceFiniteOriginAmplitude branch epsilon s n • nativeBranchVector 0) i))=
      sourceOriginPart imaginary (sourceFiniteOriginAmplitude branch epsilon s n) • sourceNativeOriginReal 0 := by
    funext i
    have real:=congrFun (sourceNativeOriginImag_zero 0) i
    change (nativeBranchVector 0 i).im=0 at real
    cases imaginary <;> simp [sourceOriginPart,Pi.smul_apply,smul_eq_mul,Complex.mul_re,Complex.mul_im,real,sourceNativeOriginReal]
  change (⟨sourceField (sourceFiniteOriginPart false branch epsilon s n),
    sourceField (sourceFiniteOriginPart true branch epsilon s n)⟩:ComplexDirection)=_
  have re:=scaled false
  have im:=scaled true
  simp only [sourceOriginPart,Bool.false_eq_true,if_false,if_true] at re im
  rw [originalComplexDirection,re,im,sourceFiniteOriginPart_field,sourceFiniteOriginPart_field]
  rfl

/-- Every original density coordinate consumes exactly the source current-column amplitude and the same full252 Noether operator. -/
theorem sourceFiniteOrigin_density (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    complexCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n)) k=
      if k=0 then sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginCanonicalFiber 0 else 0 := by
  rw [sourceFiniteOrigin_actionDirection,sourceSoftDensity_scaled,sourceSoftDensity_Noether]

theorem sourceFiniteOrigin_frequency (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    complexFrequencyCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n)) k=
      if k=0 then sourceFiniteOriginAmplitude branch epsilon s n • (-sourceNativeOriginCanonicalFiber 0) else 0 := by
  rw [sourceFiniteOrigin_actionDirection,sourceSoftFrequency_scaled,sourceSoftFrequency_Noether]

/-- The origin-origin contact is zero by the actual source field identification; no origin/jet or origin/residual cross is removed. -/
theorem sourceFiniteOrigin_originContact (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    complexMixedCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n))
      (originalComplexDirection (sourcePoleOriginField branch epsilon s n)) k=0 := by
  simp only [sourceFiniteOrigin_actionDirection,sourceSoftMixed_scaled]

/-- The full finite density retains both jet channels and every frame residual after the origin identification. -/
theorem sourceFinitePoleDensity_origin (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    sourceFinitePoleDensity branch epsilon s n k=
      (if k=0 then sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginCanonicalFiber 0 else 0)+
      (epsilon:ℂ)^2 • complexCoefficients (originalComplexDirection (sourcePoleLiteralJet branch epsilon s n)) k+
      (epsilon:ℂ)^2 • complexCoefficients (originalComplexDirection (sourcePoleFastJet branch epsilon s n)) k+
      complexCoefficients (originalComplexDirection (sourcePoleFrameResidual branch epsilon s n)) k := by
  rw [sourceFinitePoleDensity_literal,sourceFiniteOrigin_density]

theorem sourceFinitePoleFrequency_origin (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    sourceFinitePoleFrequency branch epsilon s n k=
      (if k=0 then sourceFiniteOriginAmplitude branch epsilon s n • (-sourceNativeOriginCanonicalFiber 0) else 0)+
      (epsilon:ℂ)^2 • complexFrequencyCoefficients (originalComplexDirection (sourcePoleLiteralJet branch epsilon s n)) k+
      (epsilon:ℂ)^2 • complexFrequencyCoefficients (originalComplexDirection (sourcePoleFastJet branch epsilon s n)) k+
      complexFrequencyCoefficients (originalComplexDirection (sourcePoleFrameResidual branch epsilon s n)) k := by
  rw [sourceFinitePoleFrequency_literal,sourceFiniteOrigin_frequency]

/-- This representation is only for the action coefficients, not a replacement of the complete source field. -/
def sourceFiniteOriginActionComponents (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 3→Fin 289→ℂ :=
  fun j=>if j=0 then sourceFiniteOriginAmplitude branch epsilon s n • nativeBranchVector 0
    else sourceFinitePoleComponents branch epsilon s n j

private theorem components_action (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (j : Fin 3) :
    originalComplexDirection (sourceFinitePoleComponents branch epsilon s n j)=
      originalComplexDirection (sourceFiniteOriginActionComponents branch epsilon s n j) := by
  by_cases zero:j=0
  · subst j
    simp only [sourceFinitePoleComponents,Matrix.cons_val_zero,sourceFiniteOriginActionComponents]
    exact sourceFiniteOrigin_actionDirection branch epsilon s n
  · simp only [sourceFiniteOriginActionComponents,if_neg zero]

/-- Every ordered mixed cross still appears in its original place, with only the generated origin action substitution. -/
theorem sourceFinitePoleMixed_origin (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    sourceFinitePoleMixed branch epsilon s n k=
      ∑i : Fin 3,∑j : Fin 3,complexMixedCoefficients
        (originalComplexDirection (sourceFiniteOriginActionComponents branch epsilon s n i))
        (originalComplexDirection (sourceFiniteOriginActionComponents branch epsilon s n j)) k := by
  simp only [sourceFinitePoleMixed,components_action]

/-- The actual finite origin's phase-color operator uses its source-generated amplitude, without choosing a charge sector. -/
def sourceFiniteOriginGenerator (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : YangMills.FullPairing.Mother :=
  sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginGenerator

theorem sourceFiniteOriginGenerator_basis (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (i : Quantum.Index) :
    sourceFiniteOriginGenerator branch epsilon s n (Quantum.wholeBasis i)=
      (sourceFiniteOriginAmplitude branch epsilon s n*((sourceWholeWeight i:ℂ)*Complex.I)) • Quantum.wholeBasis i := by
  simp only [sourceFiniteOriginGenerator,LinearMap.smul_apply,sourcePhaseGenerator_basis,smul_smul]

theorem sourceFiniteOriginGenerator_projection (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (a : Fin 3) :
    sourceFiniteOriginGenerator branch epsilon s n*sourcePhaseProjection a=
      (sourceFiniteOriginAmplitude branch epsilon s n*((sourcePhaseLevel a:ℂ)*Complex.I)) • sourcePhaseProjection a := by
  rw [sourceFiniteOriginGenerator,smul_mul_assoc,sourcePhaseProjection_eigen,smul_smul]

private theorem fiber_zero (c : ℂ) : c • (0:FiberOperators)=0 :=
  @_root_.smul_zero ℂ FiberOperators _ _ c

/-- The full actual Hamiltonian Ward insertion is exactly the commutator with the amplitude-weighted original X. -/
theorem sourceFiniteOriginHamiltonian_commutator (branch : Fin 2) (epsilon s : ℝ) (n p : PhysicalMomentum) :
    affine (complexFrequencyCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n))) p=
      (sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginGeneratorFiber)*sourceHamiltonianFiber p-
        sourceHamiltonianFiber p*(sourceFiniteOriginAmplitude branch epsilon s n • sourceNativeOriginGeneratorFiber) := by
  have comm : -sourceNativeOriginCanonicalFiber 0=
      sourceNativeOriginGeneratorFiber*sourceHamiltonianFiber p-sourceHamiltonianFiber p*sourceNativeOriginGeneratorFiber :=
    (sourceNativeOriginEnergy_NoetherFiber p).symm.trans (sourceNativeOriginEnergyFiber p)
  simp only [affine,sourceFiniteOrigin_frequency,Fin.succ_ne_zero,if_false,if_true,fiber_zero,Finset.sum_const_zero,add_zero]
  rw [comm,smul_sub,smul_mul_assoc,mul_smul_comm]

/-- The origin part of the actual finite photon reader retains both independent current emitters and the original negative adjoint. -/
def sourceFiniteOriginPhotonReader (Ap An : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) : FiberOperators :=
  (2:ℂ)⁻¹ • (sourcePhotonEmitter An branch epsilon s n •
    complexCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n)) 0+
    (sourcePhotonEmitter Ap branch epsilon s n •
      complexCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n)) 0).adjoint)

theorem sourceFiniteOriginPhotonReader_generated (Ap An : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) :
    sourceFiniteOriginPhotonReader Ap An branch epsilon s n=
      sourceSoftNoetherReader 0
        (sourcePhotonEmitter Ap branch epsilon s n*sourceFiniteOriginAmplitude branch epsilon s n)
        (sourcePhotonEmitter An branch epsilon s n*sourceFiniteOriginAmplitude branch epsilon s n) := by
  simp only [sourceFiniteOriginPhotonReader,sourceFiniteOrigin_density,if_true,smul_smul,
    map_smulₛₗ,starRingEnd_apply,sourceSoftNoetherReader]

def sourceFiniteOriginTimeReader (Ap An : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (time : ℝ) : FullMatterL2→L[ℂ]FullMatterL2 :=
  spatialFlow 0 (-time)*(sourceFiniteOriginPhotonReader Ap An branch epsilon s n).compLpL 2 volume*spatialFlow 0 time

/-- The actual finite origin reader now consumes the existing same-X time boundary on the original filtered preparation, including the full Yukawa defect. -/
theorem sourceFiniteOriginReader_preparation (Ap An : SourcePhotonLeg) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (side edge : Fin 2) (time : ℝ) :
    sourceFiniteOriginTimeReader Ap An branch epsilon s n time (sourceChargedFilteredPacket side edge)=
      (-Complex.I/2) • ((sourcePhotonEmitter An branch epsilon s n*sourceFiniteOriginAmplitude branch epsilon s n) •
        deriv (fun t=>sourceWardSpatial false t (sourceChargedFilteredPacket side edge)) time+
        star (sourcePhotonEmitter Ap branch epsilon s n*sourceFiniteOriginAmplitude branch epsilon s n) •
          deriv (fun t=>sourceWardSpatial true t (sourceChargedFilteredPacket side edge)) time)+
      (star (sourcePhotonEmitter Ap branch epsilon s n*sourceFiniteOriginAmplitude branch epsilon s n)/2) •
        sourceWardDefect time (sourceChargedFilteredPacket side edge) := by
  rw [sourceFiniteOriginTimeReader,sourceFiniteOriginPhotonReader_generated]
  exact sourceWardReader_preparation _ _ time (sourceChargedFilteredPacket side edge)

end LowEnergy.PreparationPhysicalFiniteOriginCovariance
