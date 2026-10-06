import H0mework.Versions.R2.Physics.RootRuntime.RecoveryConsumer
import H0mework.Physics.DiracEvolution.SafeVolterraOperator
import H0mework.Physics.GaugeAction.P286GaugeConnectionVariation
/-! The original repaired temporal Dirac operator generates the full gauge
insertion forcing. Only the connection varies; its spatial principal term and
temporal connection term are retained before any physical expectation. -/

set_option autoImplicit false
namespace SaturationMonoid.PhysicsCore.YangMills.Response.Forcing
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineEnrichedProofFreeSource
open DiracExteriorMatterAction StageNineP286GaugeConnectionVariation
open StageNineDiracDualFormNativeCauchySafeMatterVolterra
open StageNineDiracDualFormNativeCauchySafeMatterDifferentialOperator
open StageNineDiracDualFormNativeRepairedMatterResponseOperator
open StageNineCurrentCoframeMatterTemporalPrincipal StageNineCurrentCoframeMatterTimeResponse
open StageNineP286ActionCauchySplit StageNineGlobalIntegratedAction
open DiracCliffordRepresentation PointwiseDiracSpinConnectionLift
open SU7MotherLieAlgebra SU7MotherGaugeTheory Stage9C.Material.SpinPair
noncomputable section
local instance : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance : Fintype P286CoordinateIndex := Fintype.ofFinite _

def spatialInsertion (C : StageNineHolonomicConfiguration)
    (η : BasePoint → P286GaugeOneForm) (p : BasePoint) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  Complex.I • ∑ i : Fin 3,
    (diracMatrixMatterAction
      (inverseCoframeDiracGamma { coframe := C.coframe p, derivative := 0 } i.succ)).comp
      (diracExteriorMotherLieAction (p286GaugeConnectionMotherVariation η p i.succ))

def insertion (C : StageNineHolonomicConfiguration)
    (η : BasePoint → P286GaugeOneForm) (p : BasePoint) :
    Module.End ℂ DiracExteriorMatterCarrier :=
  -(currentCoframeMatterTemporalPrincipalInverse (C.coframe p)).comp (spatialInsertion C η p) -
    diracExteriorMotherLieAction (p286GaugeConnectionMotherVariation η p 0)

def forcing (C : StageNineHolonomicConfiguration) (η : BasePoint → P286GaugeOneForm)
    (φ : BasePoint → DiracExteriorMatterCarrier) (p : BasePoint) : MatterCoordinateCarrier :=
  matterCoordinateEquiv (insertion C η p (φ p))

private theorem known_affine (C : StageNineHolonomicConfiguration)
    (η : BasePoint → P286GaugeOneForm) (ε : ℝ) (p : BasePoint) :
    holonomicDiracDualCurrentCoframeMatterKnownVector
      (varyP286GaugeConnectionCoordinate C η ε) p =
      holonomicDiracDualCurrentCoframeMatterKnownVector C p +
        (ε : ℂ) • spatialInsertion C η p (C.matter p) := by
  have cov (μ : LorentzianIndex) :
      holonomicMatterCovariantDerivative (varyP286GaugeConnectionCoordinate C η ε) p μ =
        holonomicMatterCovariantDerivative C p μ +
          (ε : ℂ) • holonomicMatterGaugeConnectionVariation C η p μ :=
    holonomicMatterCovariantDerivative_gaugeConnection_expansion C η ε p μ
  unfold holonomicDiracDualCurrentCoframeMatterKnownVector
  simp only [show (varyP286GaugeConnectionCoordinate C η ε).coframe = C.coframe from rfl,
    show (varyP286GaugeConnectionCoordinate C η ε).scalar = C.scalar from rfl,
    show (varyP286GaugeConnectionCoordinate C η ε).matter = C.matter from rfl,
    cov, map_add, map_smul, Finset.sum_add_distrib, ← Finset.smul_sum, smul_add]
  simp only [spatialInsertion, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    holonomicMatterGaugeConnectionVariation]
  module

private theorem connection_affine (C : StageNineHolonomicConfiguration)
    (η : BasePoint → P286GaugeOneForm) (ε : ℝ) (p : BasePoint) (μ : LorentzianIndex) :
    holonomicMatterConnectionAction (varyP286GaugeConnectionCoordinate C η ε) p μ =
      holonomicMatterConnectionAction C p μ +
        (ε : ℂ) • holonomicMatterGaugeConnectionVariation C η p μ := by
  unfold holonomicMatterConnectionAction
  rw [gaugeConnection_varyP286GaugeConnectionCoordinate,
    p286LieBlockEmbed_add, p286LieBlockEmbed_real_smul,
    diracExteriorMotherLieAction_add, diracExteriorMotherLieAction_real_smul]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    holonomicMatterGaugeConnectionVariation, p286GaugeConnectionMotherVariation]
  exact (add_assoc _ _ _).symm

private theorem raw_affine (C : StageNineHolonomicConfiguration)
    (η : BasePoint → P286GaugeOneForm) (ε : ℝ) (p : BasePoint) :
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
        (varyP286GaugeConnectionCoordinate C η ε) p =
      actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity C p +
        (ε : ℂ) • insertion C η p (C.matter p) := by
  unfold actionGeneratedHolonomicDiracDualCurrentCoframeMatterRawTimeVelocity
    actionGeneratedHolonomicDiracDualCurrentCoframeMatterTimeCovariantDerivative
  rw [known_affine, connection_affine]
  unfold actionGeneratedCurrentCoframeMatterTemporalDerivative
  simp only [show (varyP286GaugeConnectionCoordinate C η ε).coframe = C.coframe from rfl,
    map_add, map_smul, insertion, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.comp_apply,
    holonomicMatterGaugeConnectionVariation, canonicalLorentzianTimeDirection]
  module

theorem velocity_affine (C : StageNineHolonomicConfiguration)
    (η : BasePoint → P286GaugeOneForm) (φ : BasePoint → DiracExteriorMatterCarrier)
    (ε : ℝ) (p : BasePoint) :
    cauchySafeMatterVolterraVelocity (varyP286GaugeConnectionCoordinate C η ε) φ p =
      cauchySafeMatterVolterraVelocity C φ p + ε • forcing C η φ p := by
  have commute : cauchySafeMatterCandidateActual (varyP286GaugeConnectionCoordinate C η ε) φ =
      varyP286GaugeConnectionCoordinate (cauchySafeMatterCandidateActual C φ) η ε := rfl
  unfold cauchySafeMatterVolterraVelocity
  rw [commute, raw_affine, map_add, map_smul]
  rfl


theorem velocity_hasDerivAt (C : StageNineHolonomicConfiguration)
    (η : BasePoint → P286GaugeOneForm) (φ : BasePoint → DiracExteriorMatterCarrier)
    (ε : ℝ) (p : BasePoint) :
    HasDerivAt (fun e => cauchySafeMatterVolterraVelocity
      (varyP286GaugeConnectionCoordinate C η e) φ p) (forcing C η φ p) ε := by
  simp only [velocity_affine]
  simpa only [Pi.add_apply, zero_add, one_smul, id_eq] using (hasDerivAt_const ε (cauchySafeMatterVolterraVelocity C φ p)).fun_add
    ((hasDerivAt_id ε).smul_const (forcing C η φ p))

theorem source_hasDerivAt (η : BasePoint → P286GaugeOneForm) (p : BasePoint) :
    HasDerivAt (fun ε => cauchySafeMatterVolterraVelocity
      (varyP286GaugeConnectionCoordinate Stage10.Runtime.configuration η ε)
      Stage10.Runtime.configuration.matter p)
      (forcing Stage10.Runtime.configuration η Stage10.Runtime.configuration.matter p) 0 :=
  velocity_hasDerivAt Stage10.Runtime.configuration η Stage10.Runtime.configuration.matter 0 p

end
end SaturationMonoid.PhysicsCore.YangMills.Response.Forcing
