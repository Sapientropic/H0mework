import H0mework.Versions.AE.Physics.LowEnergy.AlphaSource.CanonicalPreparationCausalFieldVariation

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCausalFieldResponse
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge GaussHistoryHilbert SourceQuantumGaugeSliceCoordinates
open GaussCoreHilbert GaussCoreDifferential GaussQuantumMultiplier
open PreparationVacuumMixedFieldReturn PreparationVacuumSourceFieldFamily
open PreparationVacuumActualFieldQuantization CanonicalGradedSpatialSource
open FullQuantum.StateGreen FullQuantum.CoframeResponse Electromagnetic.CanonicalCoframe
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _
local instance : DecidableEq Quantum.Index := Classical.decEq _
local instance : NormedAddCommGroup LorentzianCoframe := Matrix.normedAddCommGroup
local instance : SeminormedAddCommGroup LorentzianCoframe := Matrix.seminormedAddCommGroup
local instance : NormedSpace ℝ LorentzianCoframe := Matrix.normedSpace
local instance : NormedAlgebra ℝ SourceMatrix := NormedAlgebra.restrictScalars ℝ ℂ _

 theorem contactFiber_derivative (f g : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    HasDerivAt (fun t : ℝ=>stateFiber f p (sourceState z.val+t • fieldDirection g))
      (contactFiber f g p z.val) 0 := by
  have path : HasDerivAt (fun t : ℝ=>sourceState z.val+t • fieldDirection g) (fieldDirection g) 0 := by
    convert!
      (hasDerivAt_const (0 : ℝ) (sourceState z.val)).add ((hasDerivAt_id (0 : ℝ)).smul_const (fieldDirection g)) using 1
    simp only [one_smul,zero_add]
  have generated := ((stateFiber_smooth f p (sourceState z.val) (coframe_nondegenerate z)
    (CanonicalGradedSpatialSource.temporal_noncharacteristic z)).differentiableAt (by simp)).hasFDerivAt
  have generated' : HasFDerivAt (stateFiber f p) (fderiv ℝ (stateFiber f p) (sourceState z.val))
      (sourceState z.val+(0 : ℝ) • fieldDirection g) := by simpa only [zero_smul,add_zero] using generated
  convert! generated'.comp_hasDerivAt 0 path using 1

 theorem contact_generated (f g : Field289) (p : PhysicalMomentum) (z : physicalChart) :
    contactFiber f g p z.val=quantizer (fourierLinear p (fun i=>
      phaseVariation g (sourceState z.val)*familyDensity f z.val i+
      familyPhase z.val*(densitySecond f g (sourceState z.val) i+shellSecond f g (sourceState z.val) i))) :=
  (contactFiber_derivative f g p z).unique (actual_fock_contact_derivative f g p z)

 def contactCoefficient (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) : FiberMap := (phi z:ℂ) • contactFiber f g p z

 theorem contact_zero (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) (outside : z∉tsupport phi) : contactCoefficient f g p phi z=0 := by
  rw [contactCoefficient,image_eq_zero_of_notMem_tsupport outside,Complex.ofReal_zero]
  apply ContinuousLinearMap.ext
  intro v
  exact zero_smul ℂ _

 theorem contact_support (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    tsupport (contactCoefficient f g p phi)⊆tsupport phi := by
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra outside
  exact hz (contact_zero f g p phi z outside)

 theorem contact_smooth (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    ContDiff ℝ ∞ (contactCoefficient f g p phi) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases inside : z∈tsupport phi
  · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z phi.contDiff.contDiffAt).smul
      (contactFiber_smooth f g p ⟨z,phi.tsupport_subset inside⟩)
  · apply (contDiffAt_const (c:=(0:FiberMap))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport phi).isOpen_compl.mem_nhds inside] with w hw
    exact contact_zero f g p phi w hw

 def contactTest (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) : 𝓓(physicalChart,FiberMap) where
  toFun:=contactCoefficient f g p phi
  contDiff':=contact_smooth f g p phi
  hasCompactSupport':=phi.hasCompactSupport.of_isClosed_subset isClosed_closure (contact_support f g p phi)
  tsupport_subset':=(contact_support f g p phi).trans phi.tsupport_subset

 def contactBound (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) : ℝ :=
  ‖(contactTest f g p phi:BoundedContinuousFunction SourceCoordinateSlice FiberMap)‖

 theorem contactBound_nonneg (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    0 ≤ contactBound f g p phi := norm_nonneg (contactTest f g p phi:BoundedContinuousFunction SourceCoordinateSlice FiberMap)

 theorem contact_bound (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) (v : FockFiber) :
    ‖contactCoefficient f g p phi z v‖ ≤ contactBound f g p phi*‖v‖ :=
  ((contactCoefficient f g p phi z).le_opNorm v).trans (mul_le_mul_of_nonneg_right
    ((contactTest f g p phi:BoundedContinuousFunction SourceCoordinateSlice FiberMap).norm_coe_le_norm z) (norm_nonneg v))

 theorem contact_weights (f g : Field289) (p : PhysicalMomentum) (phi : Localizer)
    (z : SourceCoordinateSlice) (w : ℕ→ℂ) :
    Commute (GaussFockWeights.weight w) (contactCoefficient f g p phi z) := by
  by_cases inside : z∈tsupport phi
  · unfold contactCoefficient
    rw [contact_generated f g p ⟨z,phi.tsupport_subset inside⟩]
    exact (weight_commute w _).smul_right (phi z:ℂ)
  · rw [contact_zero f g p phi z inside]
    exact Commute.zero_right _

 def contactCore (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (contactCoefficient f g p phi) (fun _=>(contact_smooth f g p phi).contDiffAt)

 def contactGauss (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) : Op :=
  GaussBoundedMultiplier.extension (contactCoefficient f g p phi) (fun _=>(contact_smooth f g p phi).contDiffAt)
    (fun z w=>contact_weights f g p phi z w) (contactBound f g p phi) (contactBound_nonneg f g p phi)
    (fun z=>contact_bound f g p phi z)

 theorem contactGauss_core (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) (test : QuantumTest) :
    contactGauss f g p phi (embed test)=embed (contactCore f g p phi test) :=
  GaussBoundedMultiplier.extension_core _ _ _ _ _ _ test

 theorem contactGauss_norm (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) :
    ‖contactGauss f g p phi‖ ≤ contactBound f g p phi :=
  GaussBoundedMultiplier.extension_norm _ _ _ _ _ _

 theorem contactCore_exact (f g : Field289) (p : PhysicalMomentum) (phi : Localizer) (test : QuantumTest)
    (covers : ∀ z∈tsupport test,phi z=1) : contactCore f g p phi test=familyContactCore f g p test := by
  apply DFunLike.ext
  intro z
  change (phi z:ℂ) • contactFiber f g p z (test z)=contactFiber f g p z (test z)
  by_cases inside : z∈tsupport test
  · rw [covers z inside,Complex.ofReal_one,one_smul]
  · rw [image_eq_zero_of_notMem_tsupport inside,map_zero,smul_zero]

 theorem generated_contact_core (f g : Field289) (p : PhysicalMomentum) (test : QuantumTest) :
    ∃ phi : Localizer,contactGauss f g p phi (embed test)=embed (familyContactCore f g p test) := by
  obtain ⟨phi,covers,_⟩:=CanonicalGradedLocalCurrent.coreLocalizer_exists test
  exact ⟨phi,by rw [contactGauss_core,contactCore_exact f g p phi test covers]⟩

end LowEnergy.PreparationVacuumCausalFieldResponse
