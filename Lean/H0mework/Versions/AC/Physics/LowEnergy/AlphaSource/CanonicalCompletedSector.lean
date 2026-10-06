import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussBoundedMultiplier
import H0mework.Versions.AC.Physics.LowEnergy.Quantum.GaussGradedUnitary
import H0mework.Versions.AB.Physics.LowEnergy.Electromagnetic.CanonicalSector
import H0mework.Physics.LowEnergyFockDynamics.Response

/-! The canonical source seed generates its reducing CAR carrier before any
configuration completion. The original Gauss operator and time are unchanged. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace LowEnergy.CanonicalCompletedSector
open SaturationMonoid.PhysicsCore
open SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumScalarChart
open SourceQuantumGaugeSliceCoordinates GaussCoreDifferential GaussCoreHilbert
open GaussFockWeights GaussQuantumMultiplier
open scoped InnerProductSpace ContDiff Distributions
attribute [local instance] SourceRealScalarFock.branchOrder

def seedCoordinates : Mode → ℂ :=
  Sum.elim
    (LowEnergy.Quantum.coordinates
      (Stage10.ChargedPreparation.CanonicalParticle.normalizedPreparation 0
        (Stage9DEF.Compatibility.embed (Stage9DEF.Source.vector 0))))
    (fun _ => 0)

def seed : FockFiber :=
  fiberCoordinates.symm (QuantizationCheck.Fermion.oneParticle seedCoordinates)

inductive Generator : (FockFiber →L[ℂ] FockFiber) → Prop
  | native (a : NativeLie) : Generator (GaussNativeMatter.nativeFock a)
  | spin (a : Fin 7) : Generator (quantized (GaussCoframeSpin.full a))
  | matter (i b : Fin 3) (z : SourceCoordinateSlice) :
      Generator (quantized (GaussMatterCore.localMatrix i b z))
  | number (w : ℕ → ℂ) : Generator (weight w)
  | adjoint {A : FockFiber →L[ℂ] FockFiber} : Generator A → Generator A.adjoint

inductive Generated : FockFiber → Prop
  | seed : Generated seed
  | step {A : FockFiber →L[ℂ] FockFiber} {v : FockFiber} :
      Generator A → Generated v → Generated (A v)

def carrier : Submodule ℂ FockFiber := Submodule.span ℂ {v | Generated v}

theorem seed_mem : seed ∈ carrier := Submodule.subset_span Generated.seed

theorem generator_stable {A : FockFiber →L[ℂ] FockFiber} (hA : Generator A)
    {v : FockFiber} (hv : v ∈ carrier) : A v ∈ carrier := by
  induction hv using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span (Generated.step hA hv)
  | zero => simpa only [map_zero] using carrier.zero_mem
  | add x y _ _ hx hy => simpa only [map_add] using carrier.add_mem hx hy
  | smul c x _ hx => simpa only [map_smul] using carrier.smul_mem c hx

theorem generator_orthogonal {A : FockFiber →L[ℂ] FockFiber} (hA : Generator A)
    {v : FockFiber} (hv : v ∈ carrierᗮ) : A v ∈ carrierᗮ := by
  intro w hw
  rw [← ContinuousLinearMap.adjoint_inner_left]
  exact hv _ (generator_stable (Generator.adjoint hA) hw)

def fiberProjection : FockFiber →L[ℂ] FockFiber := carrier.starProjection

theorem projection_commutes {A : FockFiber →L[ℂ] FockFiber} (hA : Generator A) :
    Commute fiberProjection A := by
  apply ContinuousLinearMap.ext
  intro v
  change carrier.starProjection (A v) = A (carrier.starProjection v)
  apply carrier.eq_starProjection_of_mem_orthogonal
  · exact generator_stable hA (carrier.starProjection_apply_mem v)
  · rw [← map_sub]
    exact generator_orthogonal hA (carrier.sub_starProjection_mem_orthogonal v)

theorem projection_seed : fiberProjection seed = seed :=
  carrier.starProjection_eq_self_iff.mpr seed_mem

theorem projection_pair (v w : FockFiber) :
    inner ℂ (fiberProjection v) w = inner ℂ v (fiberProjection w) :=
  carrier.inner_starProjection_left_eq_right v w

theorem projection_square : fiberProjection * fiberProjection = fiberProjection := by
  apply ContinuousLinearMap.ext
  intro v
  exact carrier.starProjection_eq_self_iff.mpr (carrier.starProjection_apply_mem v)

theorem projection_weight (w : ℕ → ℂ) : Commute (weight w) fiberProjection :=
  (projection_commutes (Generator.number w)).symm

theorem projection_bound (v : FockFiber) : ‖fiberProjection v‖ ≤ 1*‖v‖ := by
  simpa only [one_mul, fiberProjection] using carrier.norm_starProjection_apply_le v

def project : QuantumTest →ₗ[ℂ] QuantumTest :=
  localMultiplier (fun _ => fiberProjection) (fun _ => contDiffAt_const)

def projection : H →L[ℂ] H :=
  GaussBoundedMultiplier.extension (fun _ => fiberProjection)
    (fun _ => contDiffAt_const) (fun _ => projection_weight) 1 zero_le_one
    (fun _ => projection_bound)

theorem projection_core (f : QuantumTest) : projection (embed f) = embed (project f) :=
  GaussBoundedMultiplier.extension_core (fun _ => fiberProjection)
    (fun _ => contDiffAt_const) (fun _ => projection_weight) 1 zero_le_one
    (fun _ => projection_bound) f

theorem projection_norm : ‖projection‖ ≤ 1 :=
  GaussBoundedMultiplier.extension_norm (fun _ => fiberProjection)
    (fun _ => contDiffAt_const) (fun _ => projection_weight) 1 zero_le_one
    (fun _ => projection_bound)

theorem project_apply (f : QuantumTest) (z : SourceCoordinateSlice) :
    project f z = fiberProjection (f z) := rfl

theorem project_pair (f g : QuantumTest) :
    GaussFockPair.sourcePair f (project g) = GaussFockPair.sourcePair (project f) g := by
  rw [GaussFockPair.sourcePair_integral, GaussFockPair.sourcePair_integral]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z) (f z))
      (fiberProjection (g z)) =
    inner ℂ (weight (fun N => GaussDensityCore.complexDensity N z) (fiberProjection (f z))) (g z)
  rw [← projection_pair]
  exact congrArg (fun x => inner ℂ x (g z))
    (congrArg (fun A : FockFiber →L[ℂ] FockFiber => A (f z))
      (projection_commutes (Generator.number _)).eq)

theorem projection_symmetric : projection.toLinearMap.IsSymmetric := by
  intro x y
  have hx : Set.EqOn (fun x => inner ℂ (projection x) y)
      (fun x => inner ℂ x (projection y)) (Core : Set H) := by
    intro x hx
    obtain ⟨f, hf⟩ := embed_surjective_core ⟨x,hx⟩
    change embed f = x at hf
    dsimp only
    rw [← hf]
    have hy : Set.EqOn (fun y => inner ℂ (projection (embed f)) y)
        (fun y => inner ℂ (embed f) (projection y)) (Core : Set H) := by
      intro y hy
      obtain ⟨g, hg⟩ := embed_surjective_core ⟨y,hy⟩
      change embed g = y at hg
      dsimp only
      rw [← hg, projection_core, projection_core]
      exact (project_pair f g).symm
    exact hy.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense y)
  exact hx.closure (by fun_prop) (by fun_prop) (GaussHistoryHilbert.fockTestDomain_dense x)

#print axioms projection_commutes
#print axioms projection_core
#print axioms projection_symmetric
end LowEnergy.CanonicalCompletedSector
