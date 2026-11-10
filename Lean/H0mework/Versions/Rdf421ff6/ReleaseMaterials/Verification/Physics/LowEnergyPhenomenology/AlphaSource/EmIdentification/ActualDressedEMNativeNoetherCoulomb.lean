import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedEMNativeStaticGreen
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualEMPhysicalCarrierEnergy
import H0mework.Versions.AB.Physics.MotherSource.StaticHamiltonian.Hamiltonian
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.Electromagnetic.CanonicalQuantumUnits

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedEMNativeCoulomb
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumStaticSpatialSource
open ActualDressedEMNativeMomentum ActualDressedEMNativePrincipal ActualDressedEMNativeAuxiliary
open PreparationVacuumGaugeSourceInjection PreparationCoordinates PreparationVacuumMixedFieldReturn ActualEMCarrierOwn ActualEMCurrentSplit ActualEMPhysicalCarrier
open ActualDressedNoetherCoulombUnit ActualCompositeFieldCurrent PhysicalEMGaugeRealization
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineCanonicalCauchyState
open DiracExteriorMatterAction StageNineCoframeLocalDifferentiability Stage10
open MeasureTheory SU7MotherLieAlgebra SU7MotherGaugeTheory
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _
local instance : IsTopologicalAddGroup P286CoordinateCarrier where
  toContinuousAdd := inferInstance
  toContinuousNeg := inferInstance
open scoped Matrix BigOperators SchwartzMap

private theorem original_em_auxiliary_zero (j : Fin 72) (mu : Fin 4) :
    emInsertion (Fin.natAdd 217 j) mu=0 := by
  have ne (a : Fin 12) : Fin.natAdd 217 j≠gaugeSlot mu a := by
    intro same
    have val := congrArg Fin.val same
    change 217+j.val=9+12*mu.val+a.val at val
    omega
  simp only [emInsertion,emGaugeField,Finset.sum_apply,Pi.smul_apply,gaugeField,Pi.single_apply,
    ne,if_false,smul_zero,Finset.sum_const_zero,Complex.ofReal_zero]

/-- Restricting the actual source insertion to its remaining fields preserves its original Gram: all auxiliary input slots are zero. -/
theorem actual_native_rest_coordinate_gram :
    nativeEMRestInsertion.transpose*nativeEMRestInsertion=(3/4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext mu nu
  let E : Fin 289 → Fin 4 → ℂ := emInsertion
  have full : (∑j : Fin 289,E j mu*E j nu)=((3/4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) mu nu := by
    exact congrFun (congrFun em_coordinate_gram mu) nu
  have split : (∑j : Fin 289,E j mu*E j nu)=
      (∑j : Fin 217,E (Fin.castAdd 72 j) mu*E (Fin.castAdd 72 j) nu)+
      (∑j : Fin 72,E (Fin.natAdd 217 j) mu*E (Fin.natAdd 217 j) nu) :=
    Fin.sum_univ_add (a := 217) (b := 72) (fun j => E j mu*E j nu)
  have zero : (∑j : Fin 72,E (Fin.natAdd 217 j) mu*E (Fin.natAdd 217 j) nu)=0 := by
    simp only [E,original_em_auxiliary_zero,mul_zero,Finset.sum_const_zero]
  have rest : (∑j : Fin 217,E (Fin.castAdd 72 j) mu*E (Fin.castAdd 72 j) nu)=
      ((3/4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ)) mu nu := by
    calc
      _ = (∑j : Fin 217,E (Fin.castAdd 72 j) mu*E (Fin.castAdd 72 j) nu)+
          (∑j : Fin 72,E (Fin.natAdd 217 j) mu*E (Fin.natAdd 217 j) nu) := by rw [zero,add_zero]
      _ = (∑j : Fin 289,E j mu*E j nu) := split.symm
      _ = _ := full
  simpa only [E,nativeEMRestInsertion,nativeRestIndex,Matrix.mul_apply,Matrix.transpose_apply,Matrix.submatrix_apply,id_eq] using rest

/-- One Gram is consumed between the original EM insertion and observation. -/
def nativeStaticCoordinateGreen (k : PhysicalMomentum) (f : Fin 4 → ℂ) : Fin 4 → ℂ :=
  nativeStaticGreen k ((nativeEMRestInsertion.transpose*nativeEMRestInsertion)*ᵥf)

theorem actual_native_coordinate_green_gram (k : PhysicalMomentum) (f : Fin 4 → ℂ) :
    nativeStaticCoordinateGreen k f=nativeStaticGreen k ((3/4 : ℂ) • f) := by
  rw [nativeStaticCoordinateGreen,actual_native_rest_coordinate_gram,Matrix.smul_mulVec,Matrix.one_mulVec]

/-- The original Euler minus fixes the field vertex h*j_N before any energy interpretation. -/
theorem actual_native_noether_action_vertex (p : PhysicalMomentum) (left right : CompositeLeg) (mu : Fin 4) :
    -PreparationVacuumRawJointFeedback.rawForm (emGaugeField mu) p (compositeUnitLeg left) (compositeUnitLeg right) 0=
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*noetherEMCurrent p left right mu := by
  rw [actual_noether_em_reader]
  have hn : (Stage10.ActionNormalization.phaseMomentum : ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr Stage10.ActionNormalization.phaseMomentum_positive.ne'
  field_simp [hn]

/-- Both vertices are the original action-generated coordinate Noether units. -/
def nativeTemporalNoetherRead (k pd ps : PhysicalMomentum) (dL dR sL sR : CompositeLeg) : ℂ :=
  emCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent pd dL dR) 0*
    nativeStaticCoordinateGreen k (emCoordinateCurrent (ActualCompositeFieldCurrent.compositeCurrent ps sL sR)) 0

def nativeNoetherResponseWeight : ℂ :=
  noetherPairScale^2*(3/4 : ℂ)/(2*(lapse : ℂ))

theorem actual_native_noether_temporal_read (k pd ps : PhysicalMomentum)
    (dL dR sL sR : CompositeLeg) :
    nativeTemporalNoetherRead k pd ps dL dR sL sR=
      nativeNoetherResponseWeight*(spatialSquare k : ℂ)⁻¹*
        noetherEMCurrent pd dL dR 0*noetherEMCurrent ps sL sR 0 := by
  rw [nativeTemporalNoetherRead,actual_native_coordinate_green_gram,
    actual_coordinate_noether_unit,actual_coordinate_noether_unit]
  simp only [nativeStaticGreen,Matrix.cons_val_zero,Pi.smul_apply,smul_eq_mul,
    nativeNoetherResponseWeight,noetherPairScale,div_eq_mul_inv,mul_inv_rev]
  ring1

/-- Positive Green response coefficient, before the separately paid ordered-action minus. -/
def nativeNoetherCoulomb : ℂ := nativeNoetherResponseWeight/(4*(Real.pi : ℂ))

theorem actual_native_noether_response_weight :
    nativeNoetherResponseWeight=(2/3 : ℂ)*(Stage10.ActionNormalization.phaseMomentum : ℂ)^2*(lapse : ℂ)⁻¹ := by
  unfold nativeNoetherResponseWeight noetherPairScale
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring1

/-- This ratio is generated from the original EM Gram and original electron vertices, rather than copied from the canonical Y coefficient. -/
theorem actual_native_canonical_coulomb_ratio :
    nativeNoetherCoulomb=(4/3 : ℂ)*
      (SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb : ℂ) := by
  have h := SaturationMonoid.PhysicsCore.LowEnergy.Electromagnetic.CanonicalQuantumUnits.unit_leg_initial_coulomb
  have hn : Stage10.ActionNormalization.phaseMomentum≠0 := Stage10.ActionNormalization.phaseMomentum_positive.ne'
  have canonical :
      SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.UnifiedAction.AtomicScales.canonicalCoulomb=
        Stage10.ActionNormalization.phaseMomentum^2/(8*Real.pi*lapse) := by
    apply (div_eq_iff (pow_ne_zero 2 hn)).mp at h
    rw [h]
    ring
  unfold nativeNoetherCoulomb
  rw [actual_native_noether_response_weight,canonical]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring1

/-- The original Fourier frequency is converted to the same literal jet momentum; no Fourier convention is changed. -/
theorem actual_native_fourier_jet (frequency : PhysicalMomentum) (j : Fin 3) :
    physicalFrequencyMomentum 0 (sourceSpatialMomentum frequency) j.succ=
      Complex.I*((2*Real.pi : ℝ) : ℂ)*(frequency j : ℂ) := by
  simp only [physicalFrequencyMomentum,Fin.cases_succ,sourceSpatialMomentum,Pi.smul_apply,smul_eq_mul,Complex.ofReal_mul]
  ring1

def nativeNoetherPotentialPacket (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) : ℂ :=
  ∫frequency,sourceSpatialPhase frequency x*test frequency*
    (nativeNoetherResponseWeight*(spatialSquare (sourceSpatialMomentum frequency) : ℂ)⁻¹)

/-- The single4pi is the proved transform of the original source-space phase and its physical momentum. -/
theorem actual_native_noether_packet_newton (test : 𝓢(PhysicalMomentum,ℂ)) (x : PhysicalMomentum) :
    nativeNoetherPotentialPacket test x=
      ∫y : PhysicalMomentum,nativeNoetherCoulomb/(Real.sqrt (spatialSquare y) : ℂ)*emPacket test (x-y) := by
  have packet : nativeNoetherPotentialPacket test x=nativeNoetherResponseWeight*emNewtonPacket 1 0 test x := by
    unfold nativeNoetherPotentialPacket
    change (∫frequency,sourceSpatialPhase frequency x*test frequency*
      (nativeNoetherResponseWeight*(spatialSquare (sourceSpatialMomentum frequency) : ℂ)⁻¹))=
      nativeNoetherResponseWeight*(∫frequency,(1 : ℂ)*sourceSpatialPhase frequency x*test frequency*
        emNewtonMultiplier 1 0 frequency)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with frequency
    simp [emNewtonMultiplier]
    ring1
  rw [packet,em_newton_massless_convolution,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [nativeNoetherCoulomb,div_eq_mul_inv,mul_inv_rev]
  ring1

/-- The actual original Legendre energy keeps its electric Gram, background and independent-dual matter term. -/
theorem actual_em_static_hamiltonian (V : BasePoint → ℝ) (hV : Differentiable ℝ V)
    (matter : BasePoint → DiracExteriorMatterCarrier)
    (dual : BasePoint → Module.Dual ℂ DiracExteriorMatterCarrier) (x : StageNineSpatialPoint) :
    StaticHamiltonian.hamiltonianDensity Stage10.Runtime.source (emCauchyField V matter dual) (canonicalCauchySlicePoint 0 x)-
      StaticHamiltonian.hamiltonianDensity Stage10.Runtime.source (StaticHamiltonian.reference matter dual) (canonicalCauchySlicePoint 0 x)=
      -lapse*((3/4 : ℝ)*(∑i : Fin 3,(fieldDirectionalDerivative V (canonicalCauchySlicePoint 0 x) i.succ)^2)+
        gaugeScale^2*(V (canonicalCauchySlicePoint 0 x))^2)-
      (dual (canonicalCauchySlicePoint 0 x) (Stage9DEF.Compatibility.currentAction 0
        (emPotential V (canonicalCauchySlicePoint 0 x)) (matter (canonicalCauchySlicePoint 0 x)))).re := by
  have regular : CanonicalGauss.PotentialDifferentiable (emPotential V) := by
    unfold CanonicalGauss.PotentialDifferentiable emPotential directionalPotential
    simp only [map_smul]
    exact hV.smul_const (p286CoordinateEquiv emDirection)
  rw [emCauchyField,StaticHamiltonian.original_hamiltonian_shift _ regular,
    em_cauchy_electric_energy V _ (hV _)]

/-- The principal part of that same generated Hamiltonian, at the literal physical momentum. Its field vertex is h times the source Noether unit. -/
def nativeStaticHamiltonianMode (k : PhysicalMomentum) (charge : ℂ) (potential : ℂ) : ℂ :=
  -(3/4 : ℂ)*(lapse : ℂ)*(spatialSquare k : ℂ)*potential^2+
    (Stage10.ActionNormalization.phaseMomentum : ℂ)*charge*potential

def nativeNoetherPotentialMode (k : PhysicalMomentum) (charge : ℂ) : ℂ :=
  (Stage10.ActionNormalization.phaseMomentum : ℂ)*charge/
    ((3/2 : ℂ)*(lapse : ℂ)*(spatialSquare k : ℂ))

/-- The Hamiltonian quadratic is the original EM principal Hessian with its Legendre minus and one half. -/
theorem actual_native_hamiltonian_principal (k : PhysicalMomentum) (charge potential : ℂ) :
    nativeStaticHamiltonianMode k charge potential=
      -(1/2 : ℂ)*potential*((3/4 : ℂ)*
        (nativeEMMomentumMatrix (physicalFrequencyMomentum 0 k)*ᵥPi.single 0 potential) 0)+
      (Stage10.ActionNormalization.phaseMomentum : ℂ)*charge*potential := by
  rw [actual_native_physical_em_principal]
  simp only [nativeStaticHamiltonianMode,nativePhysicalEMPrincipal,Matrix.cons_val_zero,
    Pi.single_eq_same,Complex.ofReal_zero,mul_zero,spatialSquare,Complex.ofReal_add,Complex.ofReal_pow]
  ring1

/-- The potential is the same generated temporal Green after converting the source read to the original field coefficient. -/
theorem actual_native_noether_potential_green (k : PhysicalMomentum) (charge : ℂ) :
    nativeNoetherPotentialMode k charge=(4/3 : ℂ)*
      nativeStaticGreen k ((Stage10.ActionNormalization.phaseMomentum : ℂ) • Pi.single 0 charge) 0 := by
  simp only [nativeNoetherPotentialMode,nativeStaticGreen,Matrix.cons_val_zero,Pi.smul_apply,
    Pi.single_eq_same,smul_eq_mul,div_eq_mul_inv,mul_inv_rev]
  ring1

/-- The self-energy half follows from the actual Hamiltonian quadratic and the generated Gauss inverse. -/
theorem actual_native_hamiltonian_half (k : PhysicalMomentum) (nonzero : spatialSquare k≠0) (charge : ℂ) :
    nativeStaticHamiltonianMode k charge (nativeNoetherPotentialMode k charge)=
      (1/2 : ℂ)*nativeNoetherResponseWeight*(spatialSquare k : ℂ)⁻¹*charge^2 := by
  unfold nativeStaticHamiltonianMode nativeNoetherPotentialMode
  rw [actual_native_noether_response_weight]
  field_simp [Complex.ofReal_ne_zero.mpr nonzero,Complex.ofReal_ne_zero.mpr lapse_pos.ne']
  ring1

/-- Polarizing two independent source charges consumes the half exactly once. -/
theorem actual_native_hamiltonian_cross (k : PhysicalMomentum) (nonzero : spatialSquare k≠0) (detector source : ℂ) :
    nativeStaticHamiltonianMode k (detector+source) (nativeNoetherPotentialMode k (detector+source))-
      nativeStaticHamiltonianMode k detector (nativeNoetherPotentialMode k detector)-
      nativeStaticHamiltonianMode k source (nativeNoetherPotentialMode k source)=
      nativeNoetherResponseWeight*(spatialSquare k : ℂ)⁻¹*detector*source := by
  rw [actual_native_hamiltonian_half _ nonzero,actual_native_hamiltonian_half _ nonzero,
    actual_native_hamiltonian_half _ nonzero]
  ring1

/-- The actual composite action-current read is the polarized energy of the same principal Hamiltonian, with both original charge calibrations still in its vertices. -/
theorem actual_native_noether_hamiltonian_read (k pd ps : PhysicalMomentum) (nonzero : spatialSquare k≠0)
    (dL dR sL sR : CompositeLeg) :
    nativeTemporalNoetherRead k pd ps dL dR sL sR=
      let d := noetherEMCurrent pd dL dR 0
      let s := noetherEMCurrent ps sL sR 0
      nativeStaticHamiltonianMode k (d+s) (nativeNoetherPotentialMode k (d+s))-
        nativeStaticHamiltonianMode k d (nativeNoetherPotentialMode k d)-
        nativeStaticHamiltonianMode k s (nativeNoetherPotentialMode k s) := by
  dsimp only
  rw [actual_native_hamiltonian_cross _ nonzero,actual_native_noether_temporal_read]

end LowEnergy.GaussComposite.ActualDressedEMNativeCoulomb
