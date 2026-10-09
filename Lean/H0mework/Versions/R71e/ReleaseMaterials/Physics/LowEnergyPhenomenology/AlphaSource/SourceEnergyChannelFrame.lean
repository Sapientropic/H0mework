import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceNormalizedEnergyJet
import H0mework.Versions.R3bbcbd59.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChannelTwoSpinPort
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceChargedPropagatingRead
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.BosonCausal.Metric
import H0mework.Versions.R3bbcbd59.Physics.LowEnergy.InducedQuantum.Lapse

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalNormalizedFullField
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationVacuumOriginalGreenFeedback PreparationVacuumMixedPrincipal PreparationVacuumMixedEffective
open PreparationVacuumWholeOrigin PreparationVacuumFullOriginResponse PreparationVacuumMixedControl
open PreparationVacuumPhysicalPoleSheet PreparationVacuumPhysicalCharacteristic
open PreparationVacuumPhysicalChargedFieldFactor PreparationVacuumChargedLongRangeRead
open PreparationVacuumNativeSlowCoupling PreparationVacuumSourceFieldFamily
open PreparationVacuumMixedFieldReturn PreparationVacuumActionFieldLift
open PreparationVacuumPhysicalQuantumLockedCharge PreparationPhysicalActionUnits
open PreparationVacuumCausalPoleResponse PreparationVacuumActualFieldQuantization
open PreparationVacuumPhysicalFeedback PreparationVacuumChargedSpatialResponse
open PreparationVacuumFullSlowFieldResponse PreparationVacuumChargedPacketGreen
open PreparationVacuumQuantumSlowResidue
open PreparationVacuumGaugeSourceInjection GaussQuantumMultiplier GaussFockLift
open GaussCoreHilbert SourceQuantumFockGauge SourceQuantumConfigurationHilbert
open CanonicalGradedCharge GaussHistoryHilbert PreparationVacuumMovingPoleGaussReturn
open FullQuantum.StateGreen FullQuantum.CoframeResponse CanonicalGradedSpatialSource
open StageNineHolonomicField StageNineCurrentCoframeMatterTemporalPrincipal
open Stage9DEF Stage9DEF.Compatibility Stage9C.Material.SpinPair
open DiracCliffordRepresentation DiracExteriorMatterAction
open StageNineLorentzConnectionVariation PointwiseDiracSpinConnectionLift
open Stage10.CanonicalMatter PreparationVacuumElectromagneticIdentity
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology InnerProductSpace

/-- All three actual first-frame columns, with every surviving source row retained. -/
def sourceEnergyChannelTerms : List SourceTerm := [
  ⟨15,0,⟨1,0,0,0⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨15,1,⟨1,0,0,0⟩,⟨⟨(6/11:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨16,0,⟨1,0,0,0⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨16,1,⟨1,0,0,0⟩,⟨⟨(-5/11:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨19,1,⟨1,0,0,0⟩,⟨⟨(3/11:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨20,1,⟨1,0,0,0⟩,⟨⟨(5/11:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨22,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩⟩,
  ⟨33,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩⟩,
  ⟨51,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩⟩,
  ⟨52,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/72:ℚ)⟩⟩⟩,
  ⟨57,0,⟨1,0,0,0⟩,⟨⟨0,(-5/12:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨62,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/108:ℚ),0⟩⟩⟩,
  ⟨67,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/108:ℚ),0⟩⟩⟩,
  ⟨72,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/108:ℚ),0⟩⟩⟩,
  ⟨74,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(5/198:ℚ),0⟩⟩⟩,
  ⟨76,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-5/198:ℚ),0⟩⟩⟩,
  ⟨80,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-5/198:ℚ),0⟩⟩⟩,
  ⟨82,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(5/198:ℚ),0⟩⟩⟩,
  ⟨92,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(5/27:ℚ),0⟩⟩⟩,
  ⟨94,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-5/27:ℚ),0⟩⟩⟩,
  ⟨98,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/198:ℚ)⟩⟩⟩,
  ⟨100,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/198:ℚ)⟩⟩⟩,
  ⟨104,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/198:ℚ)⟩⟩⟩,
  ⟨106,1,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/198:ℚ)⟩⟩⟩,
  ⟨110,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/27:ℚ)⟩⟩⟩,
  ⟨112,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-5/27:ℚ)⟩⟩⟩,
  ⟨127,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/27:ℚ)⟩⟩⟩,
  ⟨130,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/108:ℚ)⟩⟩⟩,
  ⟨134,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/27:ℚ)⟩⟩⟩,
  ⟨137,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/108:ℚ)⟩⟩⟩,
  ⟨141,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(5/27:ℚ)⟩⟩⟩,
  ⟨144,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨0,(-25/108:ℚ)⟩⟩⟩,
  ⟨148,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/54:ℚ),0⟩⟩⟩,
  ⟨155,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/54:ℚ),0⟩⟩⟩,
  ⟨162,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/54:ℚ),0⟩⟩⟩,
  ⟨163,0,⟨1,0,0,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨170,0,⟨1,0,0,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨177,0,⟨1,0,0,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨181,0,⟨1,0,0,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨184,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-20/27:ℚ),0⟩⟩⟩,
  ⟨188,0,⟨1,0,0,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨191,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-20/27:ℚ),0⟩⟩⟩,
  ⟨195,0,⟨1,0,0,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨198,2,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-20/27:ℚ),0⟩⟩⟩,
  ⟨202,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/54:ℚ),0⟩⟩⟩,
  ⟨209,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/54:ℚ),0⟩⟩⟩,
  ⟨216,0,⟨1,0,0,0⟩,⟨⟨0,0⟩,⟨(-25/54:ℚ),0⟩⟩⟩,
  ⟨218,0,⟨1,0,0,0⟩,⟨⟨0,(-25/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨229,0,⟨1,0,0,0⟩,⟨⟨0,(-25/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨247,0,⟨1,0,0,0⟩,⟨⟨0,(-25/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨248,0,⟨1,0,0,0⟩,⟨⟨0,(25/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨10,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(5/72:ℚ)⟩⟩⟩,
  ⟨27,0,⟨0,1,0,0⟩,⟨⟨(1/4:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨27,1,⟨0,1,0,0⟩,⟨⟨(39/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨28,0,⟨0,1,0,0⟩,⟨⟨(-1/4:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨28,1,⟨0,1,0,0⟩,⟨⟨(-34/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨31,1,⟨0,1,0,0⟩,⟨⟨(15/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨32,1,⟨0,1,0,0⟩,⟨⟨(25/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨46,0,⟨0,1,0,0⟩,⟨⟨(1/4:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨46,1,⟨0,1,0,0⟩,⟨⟨(-3/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨61,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(179/540:ℚ),0⟩⟩⟩,
  ⟨77,0,⟨0,1,0,0⟩,⟨⟨0,(-5/12:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨77,1,⟨0,1,0,0⟩,⟨⟨0,(5/67:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨79,0,⟨0,1,0,0⟩,⟨⟨0,(-5/12:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨83,1,⟨0,1,0,0⟩,⟨⟨0,(5/67:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨85,2,⟨0,1,0,0⟩,⟨⟨0,(5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨89,2,⟨0,1,0,0⟩,⟨⟨0,(-5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨91,2,⟨0,1,0,0⟩,⟨⟨0,(5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨95,2,⟨0,1,0,0⟩,⟨⟨0,(-5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨97,0,⟨0,1,0,0⟩,⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨101,1,⟨0,1,0,0⟩,⟨⟨(10/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨107,0,⟨0,1,0,0⟩,⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨107,1,⟨0,1,0,0⟩,⟨⟨(10/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨109,2,⟨0,1,0,0⟩,⟨⟨(5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨113,2,⟨0,1,0,0⟩,⟨⟨(-5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨115,2,⟨0,1,0,0⟩,⟨⟨(5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨119,2,⟨0,1,0,0⟩,⟨⟨(-5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨121,2,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(2/15:ℚ)⟩⟩⟩,
  ⟨124,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨0,(25/108:ℚ)⟩⟩⟩,
  ⟨135,0,⟨0,1,0,0⟩,⟨⟨(5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨138,2,⟨0,1,0,0⟩,⟨⟨(10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨140,0,⟨0,1,0,0⟩,⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨143,2,⟨0,1,0,0⟩,⟨⟨(-10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨153,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-179/540:ℚ),0⟩⟩⟩,
  ⟨158,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(179/540:ℚ),0⟩⟩⟩,
  ⟨189,2,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(4/15:ℚ),0⟩⟩⟩,
  ⟨192,0,⟨0,1,0,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨194,2,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-4/15:ℚ),0⟩⟩⟩,
  ⟨197,0,⟨0,1,0,0⟩,⟨⟨0,(-5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨207,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-71/540:ℚ),0⟩⟩⟩,
  ⟨210,2,⟨0,1,0,0⟩,⟨⟨0,(-10/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨212,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(71/540:ℚ),0⟩⟩⟩,
  ⟨215,2,⟨0,1,0,0⟩,⟨⟨0,(10/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨223,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-1/6:ℚ),0⟩⟩⟩,
  ⟨223,1,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(2/67:ℚ),0⟩⟩⟩,
  ⟨224,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(1/6:ℚ),0⟩⟩⟩,
  ⟨224,1,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-2/67:ℚ),0⟩⟩⟩,
  ⟨242,0,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(1/6:ℚ),0⟩⟩⟩,
  ⟨242,1,⟨0,1,0,0⟩,⟨⟨0,0⟩,⟨(-2/67:ℚ),0⟩⟩⟩,
  ⟨271,0,⟨0,1,0,0⟩,⟨⟨0,(25/36:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨272,0,⟨0,1,0,0⟩,⟨⟨0,(-25/36:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨277,0,⟨0,1,0,0⟩,⟨⟨0,(-25/36:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨9,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(5/72:ℚ)⟩⟩⟩,
  ⟨39,0,⟨0,0,1,0⟩,⟨⟨(1/4:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨39,1,⟨0,0,1,0⟩,⟨⟨(39/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨40,0,⟨0,0,1,0⟩,⟨⟨(-1/4:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨40,1,⟨0,0,1,0⟩,⟨⟨(-34/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨43,1,⟨0,0,1,0⟩,⟨⟨(15/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨44,1,⟨0,0,1,0⟩,⟨⟨(25/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨45,0,⟨0,0,1,0⟩,⟨⟨(1/4:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨45,1,⟨0,0,1,0⟩,⟨⟨(-3/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨65,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(179/540:ℚ),0⟩⟩⟩,
  ⟨73,2,⟨0,0,1,0⟩,⟨⟨0,(5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨77,2,⟨0,0,1,0⟩,⟨⟨0,(5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨79,2,⟨0,0,1,0⟩,⟨⟨0,(5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨83,2,⟨0,0,1,0⟩,⟨⟨0,(5/18:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨89,0,⟨0,0,1,0⟩,⟨⟨0,(-5/12:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨89,1,⟨0,0,1,0⟩,⟨⟨0,(5/67:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨91,0,⟨0,0,1,0⟩,⟨⟨0,(5/12:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨95,1,⟨0,0,1,0⟩,⟨⟨0,(5/67:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨97,2,⟨0,0,1,0⟩,⟨⟨(-5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨101,2,⟨0,0,1,0⟩,⟨⟨(-5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨103,2,⟨0,0,1,0⟩,⟨⟨(-5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨107,2,⟨0,0,1,0⟩,⟨⟨(-5/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨109,0,⟨0,0,1,0⟩,⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨113,1,⟨0,0,1,0⟩,⟨⟨(-10/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨119,0,⟨0,0,1,0⟩,⟨⟨(5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨119,1,⟨0,0,1,0⟩,⟨⟨(-10/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨122,2,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(2/15:ℚ)⟩⟩⟩,
  ⟨125,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨0,(25/108:ℚ)⟩⟩⟩,
  ⟨129,0,⟨0,0,1,0⟩,⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨132,2,⟨0,0,1,0⟩,⟨⟨(-10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨139,0,⟨0,0,1,0⟩,⟨⟨(5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨142,2,⟨0,0,1,0⟩,⟨⟨(10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨147,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(179/540:ℚ),0⟩⟩⟩,
  ⟨157,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-179/540:ℚ),0⟩⟩⟩,
  ⟨183,2,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-4/15:ℚ),0⟩⟩⟩,
  ⟨186,0,⟨0,0,1,0⟩,⟨⟨0,(-5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨193,2,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(4/15:ℚ),0⟩⟩⟩,
  ⟨196,0,⟨0,0,1,0⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨201,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(71/540:ℚ),0⟩⟩⟩,
  ⟨204,2,⟨0,0,1,0⟩,⟨⟨0,(10/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨211,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-71/540:ℚ),0⟩⟩⟩,
  ⟨214,2,⟨0,0,1,0⟩,⟨⟨0,(-10/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨235,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-1/6:ℚ),0⟩⟩⟩,
  ⟨235,1,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(2/67:ℚ),0⟩⟩⟩,
  ⟨236,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(1/6:ℚ),0⟩⟩⟩,
  ⟨236,1,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-2/67:ℚ),0⟩⟩⟩,
  ⟨241,0,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(1/6:ℚ),0⟩⟩⟩,
  ⟨241,1,⟨0,0,1,0⟩,⟨⟨0,0⟩,⟨(-2/67:ℚ),0⟩⟩⟩,
  ⟨259,0,⟨0,0,1,0⟩,⟨⟨0,(-25/36:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨260,0,⟨0,0,1,0⟩,⟨⟨0,(25/36:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨278,0,⟨0,0,1,0⟩,⟨⟨0,(25/36:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨15,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(5/72:ℚ)⟩⟩⟩,
  ⟨16,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(-5/72:ℚ)⟩⟩⟩,
  ⟨51,0,⟨0,0,0,1⟩,⟨⟨(1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨51,1,⟨0,0,0,1⟩,⟨⟨(36/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨52,0,⟨0,0,0,1⟩,⟨⟨(-1/2:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨52,1,⟨0,0,0,1⟩,⟨⟨(-31/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨55,1,⟨0,0,0,1⟩,⟨⟨(15/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨56,1,⟨0,0,0,1⟩,⟨⟨(25/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨69,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(179/540:ℚ),0⟩⟩⟩,
  ⟨74,0,⟨0,0,0,1⟩,⟨⟨0,(-5/24:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨74,1,⟨0,0,0,1⟩,⟨⟨0,(5/134:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨76,0,⟨0,0,0,1⟩,⟨⟨0,(-5/24:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨76,1,⟨0,0,0,1⟩,⟨⟨0,(5/134:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨80,0,⟨0,0,0,1⟩,⟨⟨0,(5/24:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨80,1,⟨0,0,0,1⟩,⟨⟨0,(5/134:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨82,0,⟨0,0,0,1⟩,⟨⟨0,(5/24:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨82,1,⟨0,0,0,1⟩,⟨⟨0,(5/134:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨88,2,⟨0,0,0,1⟩,⟨⟨0,(-5/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨94,2,⟨0,0,0,1⟩,⟨⟨0,(-5/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨98,0,⟨0,0,0,1⟩,⟨⟨(5/12:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨98,1,⟨0,0,0,1⟩,⟨⟨(5/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨100,0,⟨0,0,0,1⟩,⟨⟨(5/12:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨100,1,⟨0,0,0,1⟩,⟨⟨(5/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨104,0,⟨0,0,0,1⟩,⟨⟨(-5/12:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨104,1,⟨0,0,0,1⟩,⟨⟨(5/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨106,0,⟨0,0,0,1⟩,⟨⟨(-5/12:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨106,1,⟨0,0,0,1⟩,⟨⟨(5/67:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨112,2,⟨0,0,0,1⟩,⟨⟨(-10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨118,2,⟨0,0,0,1⟩,⟨⟨(-10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨123,2,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(2/15:ℚ)⟩⟩⟩,
  ⟨126,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨0,(25/108:ℚ)⟩⟩⟩,
  ⟨128,0,⟨0,0,0,1⟩,⟨⟨(5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨131,2,⟨0,0,0,1⟩,⟨⟨(10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨133,0,⟨0,0,0,1⟩,⟨⟨(-5/6:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨136,2,⟨0,0,0,1⟩,⟨⟨(-10/9:ℚ),0⟩,⟨0,0⟩⟩⟩,
  ⟨146,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-179/540:ℚ),0⟩⟩⟩,
  ⟨151,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(179/540:ℚ),0⟩⟩⟩,
  ⟨182,2,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(4/15:ℚ),0⟩⟩⟩,
  ⟨185,0,⟨0,0,0,1⟩,⟨⟨0,(5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨187,2,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-4/15:ℚ),0⟩⟩⟩,
  ⟨190,0,⟨0,0,0,1⟩,⟨⟨0,(-5/6:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨200,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(-71/540:ℚ),0⟩⟩⟩,
  ⟨203,2,⟨0,0,0,1⟩,⟨⟨0,(-10/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨205,0,⟨0,0,0,1⟩,⟨⟨0,0⟩,⟨(71/540:ℚ),0⟩⟩⟩,
  ⟨208,2,⟨0,0,0,1⟩,⟨⟨0,(10/9:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨253,0,⟨0,0,0,1⟩,⟨⟨0,(25/36:ℚ)⟩,⟨0,0⟩⟩⟩,
  ⟨266,0,⟨0,0,0,1⟩,⟨⟨0,(-25/36:ℚ)⟩,⟨0,0⟩⟩⟩]


private def firstThree (j : Fin 289) : Bool:=decide (j.val<3)

private def channelKernelTerms : List SourceTerm :=
  fastNormalizeTerms (productTerms fullKernelTerms (columnTerms firstThree slowFastFrameTerms))

private def channelForceTerms : List SourceTerm :=
  fastNormalizeTerms (productTerms (degreeTerms (positiveTerms activeTerms) 1) channelKernelTerms)

private def channelResponseTerms : List SourceTerm :=
  fastNormalizeTerms (productTerms
    (componentInverseTerms 0++componentInverseTerms 1++componentInverseTerms 2) channelForceTerms)

private def frameTerms : List SourceTerm :=
  productTerms (degreeTerms (positiveTerms originalChangeTerms) 1) channelKernelTerms++
    negativeTerms (productTerms (originTerms originalChangeTerms) channelResponseTerms)

private theorem literal_certificate :
    fastNormalizeTerms (frameTerms++negativeTerms sourceEnergyChannelTerms)=[] := by
  decide +kernel

private theorem inverseTerms_constant (v : Fin 4→ℂ) (i : Fin 3) :
    sourceMatrix (componentInverseTerms i) v=componentInverse i := by
  fin_cases i <;> rfl

private theorem frameTerms_value (v : Fin 4→ℂ) :
    sourceMatrix frameTerms v=sourceChargedNativeFrameJet v*projectionMatrix firstThree := by
  simp only [frameTerms,channelKernelTerms,channelForceTerms,channelResponseTerms,
    fastNormalizeTerms_value,productTerms_value,sourceMatrix_append,negativeTerms_value,
    columnTerms_value,inverseTerms_constant,
    fullKernel_generated,slowFastFrame_constant]
  have origin : sourceMatrix (originTerms originalChangeTerms) v=originalChange 0 := by
    calc
      _=sourceMatrix (originTerms originalChangeTerms) 0 := by
        simpa only [degreeTensor,degreeTerms,PreparationVacuumMixedPrincipal.originTerms,zero_smul,pow_zero,one_smul] using
          (degreeTensor_scaled originalChangeTerms 0 (0:ℂ) v).symm
      _=originalChange 0 := originTerms_generated originalChangeTerms
  rw [origin]
  simp only [sourceChargedNativeFrameJet,sourceLinearPart,degreeTensor,fullInverse,Fin.sum_univ_three]
  simp only [sub_eq_add_neg,add_mul,neg_mul,mul_assoc]

/-- The literal matrix is paid from the original complete inverse and native frame, not chosen eigenvectors. -/
theorem sourceEnergyChannelMatrix_generated (v : Fin 4→ℂ) :
    sourceMatrix sourceEnergyChannelTerms v=
      sourceChargedNativeFrameJet v*projectionMatrix firstThree := by
  have h:=normalization_equal frameTerms sourceEnergyChannelTerms literal_certificate v
  rw [frameTerms_value] at h
  exact h.symm

theorem sourceEnergyChannelMatrix_entry (v : Fin 4→ℂ) (row : Fin 289) (i : Fin 3) :
    sourceMatrix sourceEnergyChannelTerms v row ⟨i.val,by omega⟩=
      sourceChargedNativeFrameJet v row ⟨i.val,by omega⟩ := by
  rw [sourceEnergyChannelMatrix_generated]
  simp [projectionMatrix,Matrix.mul_diagonal,firstThree,i.isLt]

end LowEnergy.PreparationPhysicalNormalizedFullField
