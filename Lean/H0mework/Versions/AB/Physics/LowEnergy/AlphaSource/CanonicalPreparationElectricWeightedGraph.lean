import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationElectricOrbitCurrent
import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationTemporalWardConsumer

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumElectricConstraint
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumGaugeSliceCoordinates
open SourceQuantumFockGauge GaussCoreHilbert GaussCoreDifferential GaussLiveMomentum
open GaussNativeForm GaussNativeMatter GaussQuantumMultiplier CanonicalGradedCharge GaussFockPair
open PreparationVacuumTemporalCharge PreparationVacuumLowerClassical PreparationVacuumFieldConstraintResponse
open Set Filter
open scoped ContDiff Topology BigOperators InnerProductSpace
attribute [local instance] SourceRealScalarFock.branchOrder
local instance : DecidableEq Mode := Classical.decEq _

def orbitAdjoint (a : NativeLie) : QuantumTest →ₗ[ℂ] QuantumTest :=
  (∑ j : ScalarIndex,(GaussMomentumAdjoint.adjoint (scalarDirection j)).comp
    (multiply (scalarOrbit a j) (fun _=>(scalarOrbit_smooth a j).contDiffAt)))+
  (∑ i : Fin 3,∑ j : LieIndex,(GaussMomentumAdjoint.adjoint (gaugeDirection i j)).comp
    (multiply (electricOrbit a i j) (fun _=>(electricOrbit_smooth a i j).contDiffAt)))

theorem orbit_adjoint_pair (a : NativeLie) (f g : QuantumTest) :
    sourcePair f (orbitAction a g)=sourcePair (orbitAdjoint a f) g := by
  have term (v : Ambient) (c : SourceCoordinateSlice → ℝ)
      (hc : ∀ z : GaussHistoryHilbert.physicalChart,ContDiffAt ℝ ∞ c z.val) :
      inner ℂ (embed f) (embed (multiply c hc (covariantMomentum v g)))=
        inner ℂ (embed (GaussMomentumAdjoint.adjoint v (multiply c hc f))) (embed g) :=
    (multiply_pair c hc f (covariantMomentum v g)).trans
      (GaussMomentumAdjoint.momentum_pair v (multiply c hc f) g)
  simp only [orbitAction,scalarOrbitAction,electricOrbitAction,orbitAdjoint,
    LinearMap.add_apply,LinearMap.sum_apply,LinearMap.comp_apply]
  simp only [sourcePair,map_add,map_sum,inner_add_right,inner_add_left,inner_sum,sum_inner]
  simp_rw [term]

theorem charge_pair (a : NativeLie) (f g : QuantumTest) :
    sourcePair f (chargeAction a g)=sourcePair (chargeAction a f) g := by
  have hermitian : (chargeMatrix a).conjTranspose=chargeMatrix a := by
    rw [chargeMatrix,Matrix.conjTranspose_smul,nativeFull_skew]
    simp only [Complex.star_def,Complex.conj_I,smul_neg,neg_smul,neg_neg]
  exact action_pair (fun _=>chargeMatrix a) (fun _=>contDiffAt_const)
    (fun _=>hermitian) f g

theorem orbit_pair (a : NativeLie) (f g : QuantumTest) :
    sourcePair f (orbitAction a g)=sourcePair (orbitAction a f) g := by
  rw [original_gauss_constraint]
  simp only [LinearMap.neg_apply,sourcePair,map_neg,inner_neg_right,inner_neg_left]
  exact congrArg Neg.neg (charge_pair a f g)

theorem weighted_adjoint_constraint (a : NativeLie) : orbitAdjoint a= -chargeAction a := by
  rw [←original_gauss_constraint]
  apply LinearMap.ext
  intro f
  apply embed_injective
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  have h:= (orbit_adjoint_pair a f (orbitAdjoint a f-orbitAction a f)).symm.trans
    (orbit_pair a f (orbitAdjoint a f-orbitAction a f))
  change inner ℂ (embed (orbitAdjoint a f)) (embed (_-_))=
    inner ℂ (embed (orbitAction a f)) (embed (_-_)) at h
  rw [map_sub] at h
  rw [inner_sub_left,h,sub_self]

/-- The ordering includes the source coefficient, its divergence and each Number density. -/
theorem original_weighted_ordering (a : NativeLie) : orbitAdjoint a=orbitAction a := by
  rw [weighted_adjoint_constraint,original_gauss_constraint]

def jointReader (a : Fin 12) : H →L[ℂ] H := -globalReader a

theorem jointReader_core (a : Fin 12) (f : QuantumTest) :
    jointReader a (embed f)=embed (scalarOrbitAction (originalUnit a) f+electricOrbitAction (originalUnit a) f) := by
  exact (temporal_constraint_source a f).symm

theorem jointReader_adjoint_core (a : Fin 12) (f : QuantumTest) :
    jointReader a (embed f)=embed (orbitAdjoint (originalUnit a) f) := by
  rw [original_weighted_ordering]
  exact (temporal_constraint_source a f).symm

theorem jointReader_price (a : Fin 12) : ‖jointReader a‖≤chargePrice a := by
  rw [jointReader,norm_neg]
  exact globalReader_norm a

def jointCoreGraph (a : Fin 12) : Set (H×H) :=
  Set.range (fun f : QuantumTest=>(embed f,embed (orbitAction (originalUnit a) f)))

theorem embed_dense : Dense (Set.range embed) := by
  have same : Set.range embed=(GaussCoreHilbert.Core : Set H) := by
    ext x
    constructor
    · rintro ⟨f,rfl⟩
      exact embed_mem_core f
    · intro hx
      exact embed_surjective_core ⟨x,hx⟩
  rw [same]
  exact GaussHistoryHilbert.fockTestDomain_dense

theorem original_joint_graph_closed (a : Fin 12) :
    closure (jointCoreGraph a)={xy | jointReader a xy.1=xy.2} := by
  apply le_antisymm
  · apply closure_minimal
    · rintro _ ⟨f,rfl⟩
      exact jointReader_core a f
    · exact isClosed_eq ((jointReader a).continuous.comp continuous_fst) continuous_snd
  · rintro ⟨x,y⟩ (same : jointReader a x=y)
    subst y
    have h:=image_closure_subset_closure_image
      (continuous_id.prodMk (jointReader a).continuous) (s:=Set.range embed)
    apply closure_mono _ (h ⟨x,embed_dense x,rfl⟩)
    rintro _ ⟨_,⟨f,rfl⟩,rfl⟩
    exact ⟨f,Prod.ext rfl (jointReader_core a f).symm⟩

theorem sourceApprox_joint_graph (a : Fin 12) (x : H) :
    Tendsto (fun F : GaussUnitaryHistory.Index=>
      (embed (sourceTestApprox F x),embed (orbitAction (originalUnit a) (sourceTestApprox F x))))
      GaussUnitaryHistory.sourceFilter (𝓝 (x,jointReader a x)) := by
  have value:=same_source_approximation x
  have graph:=(jointReader a).continuous.tendsto x |>.comp value
  have core (f : QuantumTest) : jointReader a (embed f)=embed (orbitAction (originalUnit a) f) :=
    jointReader_core a f
  simpa only [Function.comp_apply,core] using value.prodMk_nhds graph

end LowEnergy.PreparationVacuumElectricConstraint
