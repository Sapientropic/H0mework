import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Flow
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.GaugeHistory.Free
import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialResponse.Fields

/-! Every continuous history of bounded original gauge fields supplies its own complete spatial flow. -/
set_option autoImplicit false
open MeasureTheory Set
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
open FullSpace GaugeGreen PerturbedGreen YangMills.FullPairing
open SU7MotherLieAlgebra SU7MotherGaugeTheory
open ProofFreeRicherAnholonomicSource StageNineHolonomicField
open StageNineP286GaugeConnectionVariation StageNineP286GaugeConnectionVariationDensity
noncomputable section
local instance historyGaugeFinite : Module.Finite ℝ P286LieBlockData :=
  FiniteDimensional.of_injective p286AmbientLinear p286AmbientLinear_injective
local instance historyGaugeFintype : Fintype P286CoordinateIndex := Fintype.ofFinite _

theorem spatialFree_joint : Continuous (fun tv : ℝ × FullMatterL2 => spatialFree tv.1 tv.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun t => (freeUnitary t).isometry.lipschitz) spatialFree_continuous

theorem spatialFree_pair (time : ℝ) (u v : FullMatterL2) :
    inner ℂ (spatialFree time u) v=inner ℂ u (spatialFree (-time) v) := by
  have paired := (freeUnitary time).inner_map_map u (spatialFree (-time) v)
  change inner ℂ (spatialFree time u) (spatialFree time (spatialFree (-time) v))=_ at paired
  rw [← spatialFree_add,add_neg_cancel,spatialFree_zero] at paired
  exact paired

def gaugeOperatorMap : GaugeProfile →L[ℝ] SpatialOperators :=
  let multiply : Lp (α := Position) FiberOperators ⊤ volume →L[ℝ] SpatialOperators :=
    ((ContinuousLinearMap.id ℂ FiberOperators).holderL volume ⊤ 2 2).restrictScalars ℝ
  multiply.comp (gaugeMap.compLpL ⊤ volume)

theorem gaugeOperatorMap_apply (profile : GaugeProfile) : gaugeOperatorMap profile=gaugePotential profile := rfl

def interactionHamiltonian (profile : ℝ → GaugeProfile) (time : ℝ) : SpatialOperators :=
  (spatialFree (-time)).comp ((gaugePotential (profile time)).comp (spatialFree time))

theorem interactionHamiltonian_apply (profile : ℝ → GaugeProfile) (time : ℝ) (v : FullMatterL2) :
    interactionHamiltonian profile time v=spatialFree (-time) (gaugePotential (profile time) (spatialFree time v)) := rfl

theorem interactionHamiltonian_continuous (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (v : FullMatterL2) : Continuous (fun t => interactionHamiltonian profile t v) := by
  have native : Continuous (fun t => gaugePotential (profile t)) := gaugeOperatorMap.continuous.comp continuousProfile
  have inside := native.clm_apply (spatialFree_continuous v)
  have composed := spatialFree_joint.comp (continuous_id.neg.prodMk inside)
  simpa only [interactionHamiltonian_apply,Function.comp_def,Pi.neg_apply,id_eq] using composed

theorem interactionHamiltonian_selfAdjoint (profile : ℝ → GaugeProfile) (time : ℝ) :
    IsSelfAdjoint (interactionHamiltonian profile time) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro u v
  change inner ℂ (spatialFree (-time) (gaugePotential (profile time) (spatialFree time u))) v=
    inner ℂ u (spatialFree (-time) (gaugePotential (profile time) (spatialFree time v)))
  rw [spatialFree_pair,neg_neg,← spatialFree_pair time]
  exact (gaugePotential_selfAdjoint (profile time)).isSymmetric _ _

theorem interactionHamiltonian_bound (profile : ℝ → GaugeProfile) (time : ℝ) :
    ‖interactionHamiltonian profile time‖≤‖gaugePotential (profile time)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  rw [interactionHamiltonian_apply,spatialFree_norm_eq]
  exact ((gaugePotential (profile time)).le_opNorm _).trans_eq (by rw [spatialFree_norm_eq])

theorem interactionHamiltonian_bounded (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (radius : ℝ) (_positive : 0<radius) :
    ∃ M, ∀ t ∈ Icc (-radius) radius, ‖interactionHamiltonian profile t‖≤M := by
  have native : Continuous (fun t => gaugePotential (profile t)) := gaugeOperatorMap.continuous.comp continuousProfile
  obtain ⟨M,bounded⟩ := (isCompact_Icc : IsCompact (Icc (-radius) radius)).exists_bound_of_continuousOn native.continuousOn
  exact ⟨M,fun t inside => (interactionHamiltonian_bound profile t).trans (bounded t inside)⟩

def nativeDevelopment (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile) :
    Development (interactionHamiltonian profile) :=
  development _ (interactionHamiltonian_continuous profile continuousProfile)
    (interactionHamiltonian_bounded profile continuousProfile) (interactionHamiltonian_selfAdjoint profile)

def gaugeUnitary (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) : FullMatterL2 ≃ₗᵢ[ℂ] FullMatterL2 :=
  ((freeUnitary (-start)).trans ((nativeDevelopment profile continuousProfile).unitary
    (interactionHamiltonian_selfAdjoint profile) epsilon start time)).trans (freeUnitary time)

theorem gaugeUnitary_apply (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) (initial : FullMatterL2) :
    gaugeUnitary profile continuousProfile epsilon start time initial=
      spatialFree time ((nativeDevelopment profile continuousProfile).curve epsilon start
        (spatialFree (-start) initial) time) := rfl

theorem gaugeUnitary_starts (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start : ℝ) (initial : FullMatterL2) :
    gaugeUnitary profile continuousProfile epsilon start start initial=initial := by
  rw [gaugeUnitary_apply,Development.starts,← spatialFree_add,add_neg_cancel,spatialFree_zero]

theorem gaugeUnitary_interaction (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) (initial : FullMatterL2) :
    spatialFree (-time) (gaugeUnitary profile continuousProfile epsilon start time initial)=
      (nativeDevelopment profile continuousProfile).curve epsilon start (spatialFree (-start) initial) time := by
  rw [gaugeUnitary_apply,spatialFree_inverse]

theorem gaugeUnitary_equation (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start time : ℝ) (initial : FullMatterL2) :
    HasDerivAt (fun t => spatialFree (-t) (gaugeUnitary profile continuousProfile epsilon start t initial))
      ((-Complex.I*(epsilon : ℂ)) • spatialFree (-time)
        (gaugePotential (profile time) (gaugeUnitary profile continuousProfile epsilon start time initial))) time := by
  simp only [gaugeUnitary_interaction]
  have generated := (nativeDevelopment profile continuousProfile).evolves epsilon start (spatialFree (-start) initial) time
  simpa only [generator,smul_apply,interactionHamiltonian_apply,gaugeUnitary_apply] using! generated

theorem gaugeUnitary_compose (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start middle time : ℝ) (initial : FullMatterL2) :
    gaugeUnitary profile continuousProfile epsilon middle time
      (gaugeUnitary profile continuousProfile epsilon start middle initial)=
        gaugeUnitary profile continuousProfile epsilon start time initial := by
  simp only [gaugeUnitary_apply,spatialFree_inverse]
  rw [Development.compose _ (interactionHamiltonian_selfAdjoint profile)]

theorem gaugeUnitary_continuous (profile : ℝ → GaugeProfile) (continuousProfile : Continuous profile)
    (epsilon start : ℝ) (initial : FullMatterL2) :
    Continuous (fun t => gaugeUnitary profile continuousProfile epsilon start t initial) := by
  have curve := continuous_iff_continuousAt.mpr (fun t =>
    ((nativeDevelopment profile continuousProfile).evolves epsilon start (spatialFree (-start) initial) t).continuousAt)
  have composed := spatialFree_joint.comp (continuous_id.prodMk curve)
  simpa only [Function.comp_def,id_eq,gaugeUnitary_apply] using! composed

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.GaugeHistory
