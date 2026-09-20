import H0mework.Physics.LowEnergyFockDynamics.Hamiltonian
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Pointwise finite Hermitian source matrices act unitarily on the actual full L² carrier. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
open Fermion
noncomputable section
variable {ι X : Type*} [Fintype ι] [LinearOrder ι]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (H : X → Matrix ι ι ℂ)
  (continuousH : Continuous H) (hermitian : ∀ k, (H k).conjTranspose=H k)

abbrev Fiber := EuclideanSpace ℂ ι
abbrev Space := Lp (Fiber (ι := ι)) 2 μ

local instance : NormedAlgebra ℚ (Fiber (ι := ι) →L[ℂ] Fiber (ι := ι)) :=
  NormedAlgebra.restrictScalars ℚ ℂ _

theorem matrix_operator_continuous :
    Continuous (hamiltonianOperator (ι := ι)) :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

omit [MeasurableSpace X] [BorelSpace X] in
include continuousH in
theorem evolution_joint_continuous :
    Continuous (fun tk : ℝ × X => timeEvolution (H tk.2) tk.1) := by
  change Continuous (fun tk : ℝ × X => NormedSpace.exp
    ((tk.1 : ℂ) • ((-Complex.I) • hamiltonianOperator (H tk.2))))
  have cg : Continuous (fun k => (-Complex.I) • hamiltonianOperator (H k)) :=
    (continuous_const_smul (-Complex.I)).comp (matrix_operator_continuous.comp continuousH)
  have ct : Continuous (fun tk : ℝ × X =>
      (tk.1 : ℂ) • ((-Complex.I) • hamiltonianOperator (H tk.2))) :=
    (Complex.continuous_ofReal.comp continuous_fst).smul (cg.comp continuous_snd)
  have ce : Continuous (NormedSpace.exp :
      (Fiber (ι := ι) →L[ℂ] Fiber (ι := ι)) → (Fiber (ι := ι) →L[ℂ] Fiber (ι := ι))) :=
    NormedSpace.exp_continuous
  exact ce.comp ct

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem evolution_add (k : X) (s t : ℝ) :
    timeEvolution (H k) (s+t)=timeEvolution (H k) s*timeEvolution (H k) t := by
  change NormedSpace.exp (((s+t : ℝ) : ℂ) • timeGenerator (H k)) =
    NormedSpace.exp ((s : ℂ) • timeGenerator (H k))*NormedSpace.exp ((t : ℂ) • timeGenerator (H k))
  have added : (((s+t : ℝ) : ℂ) • timeGenerator (H k)) =
      (s : ℂ) • timeGenerator (H k)+(t : ℂ) • timeGenerator (H k) := by
    ext v i
    simp only [smul_apply,add_apply,PiLp.smul_apply,
      PiLp.add_apply,smul_eq_mul,Complex.ofReal_add]
    ring
  rw [added]
  apply NormedSpace.exp_add_of_commute
  change ((s : ℂ) • timeGenerator (H k))*((t : ℂ) • timeGenerator (H k)) =
    ((t : ℂ) • timeGenerator (H k))*((s : ℂ) • timeGenerator (H k))
  ext v i
  simp
  ring

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in
include hermitian in
theorem evolution_norm (k : X) (t : ℝ) (v : Fiber (ι := ι)) :
    ‖timeEvolution (H k) t v‖=‖v‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary
    (timeEvolution_unitary (H k) (hermitian k) t) v

include continuousH in
theorem orbit_measurable (t : ℝ) (f : Space (ι := ι) μ) :
    AEStronglyMeasurable (fun k => timeEvolution (H k) t (f k)) μ := by
  have operators : Continuous (fun k => timeEvolution (H k) t) :=
    (evolution_joint_continuous H continuousH).comp (continuous_const.prodMk continuous_id)
  exact (isBoundedBilinearMap_apply : IsBoundedBilinearMap ℂ
    (fun q : (Fiber (ι := ι) →L[ℂ] Fiber (ι := ι)) × Fiber (ι := ι) => q.1 q.2)).continuous.comp_aestronglyMeasurable
      (operators.aestronglyMeasurable.prodMk (Lp.memLp f).aestronglyMeasurable)

include continuousH hermitian in
theorem orbit_memLp (t : ℝ) (f : Space (ι := ι) μ) :
    MemLp (fun k => timeEvolution (H k) t (f k)) 2 μ := by
  apply (Lp.memLp f).of_le_mul (c := 1) (orbit_measurable μ H continuousH t f)
  exact ae_of_all _ fun k => by rw [evolution_norm H hermitian,one_mul]

def applyFlow (t : ℝ) (f : Space (ι := ι) μ) : Space (ι := ι) μ :=
  (orbit_memLp μ H continuousH hermitian t f).toLp _

theorem applyFlow_ae (t : ℝ) (f : Space (ι := ι) μ) :
    applyFlow μ H continuousH hermitian t f =ᵐ[μ]
      fun k => timeEvolution (H k) t (f k) :=
  (orbit_memLp μ H continuousH hermitian t f).coeFn_toLp

theorem applyFlow_add (t : ℝ) (f g : Space (ι := ι) μ) :
    applyFlow μ H continuousH hermitian t (f+g)=
      applyFlow μ H continuousH hermitian t f+applyFlow μ H continuousH hermitian t g := by
  apply Lp.ext
  filter_upwards [applyFlow_ae μ H continuousH hermitian t (f+g),
    applyFlow_ae μ H continuousH hermitian t f,applyFlow_ae μ H continuousH hermitian t g,
    Lp.coeFn_add f g,Lp.coeFn_add (applyFlow μ H continuousH hermitian t f)
      (applyFlow μ H continuousH hermitian t g)] with k hsum hf hg hin hout
  simp only [hsum,hout,hin,Pi.add_apply,hf,hg,map_add]

theorem applyFlow_smul (t : ℝ) (c : ℂ) (f : Space (ι := ι) μ) :
    applyFlow μ H continuousH hermitian t (c • f)=c • applyFlow μ H continuousH hermitian t f := by
  apply Lp.ext
  filter_upwards [applyFlow_ae μ H continuousH hermitian t (c • f),
    applyFlow_ae μ H continuousH hermitian t f,Lp.coeFn_smul c f,
    Lp.coeFn_smul c (applyFlow μ H continuousH hermitian t f)] with k hsum hf hin hout
  simp only [hsum,hout,hin,Pi.smul_apply,hf,map_smul]

theorem applyFlow_norm (t : ℝ) (f : Space (ι := ι) μ) :
    ‖applyFlow μ H continuousH hermitian t f‖=‖f‖ := by
  apply le_antisymm <;> apply Lp.norm_le_norm_of_ae_le
  · filter_upwards [applyFlow_ae μ H continuousH hermitian t f] with k hk
    rw [hk,evolution_norm H hermitian]
  · filter_upwards [applyFlow_ae μ H continuousH hermitian t f] with k hk
    rw [hk,evolution_norm H hermitian]

def flow (t : ℝ) : Space (ι := ι) μ →ₗᵢ[ℂ] Space (ι := ι) μ where
  toFun := applyFlow μ H continuousH hermitian t
  map_add' := applyFlow_add μ H continuousH hermitian t
  map_smul' := applyFlow_smul μ H continuousH hermitian t
  norm_map' := applyFlow_norm μ H continuousH hermitian t

theorem flow_zero (f : Space (ι := ι) μ) : flow μ H continuousH hermitian 0 f=f := by
  apply Lp.ext
  filter_upwards [applyFlow_ae μ H continuousH hermitian 0 f] with k hk
  change applyFlow μ H continuousH hermitian 0 f k=f k
  rw [hk,timeEvolution_zero]

theorem flow_add (s t : ℝ) (f : Space (ι := ι) μ) :
    flow μ H continuousH hermitian (s+t) f=
      flow μ H continuousH hermitian s (flow μ H continuousH hermitian t f) := by
  apply Lp.ext
  filter_upwards [applyFlow_ae μ H continuousH hermitian (s+t) f,
    applyFlow_ae μ H continuousH hermitian s (flow μ H continuousH hermitian t f),
    applyFlow_ae μ H continuousH hermitian t f] with k hadd hs ht
  change applyFlow μ H continuousH hermitian (s+t) f k=
    applyFlow μ H continuousH hermitian s (applyFlow μ H continuousH hermitian t f) k
  change applyFlow μ H continuousH hermitian s (applyFlow μ H continuousH hermitian t f) k=
    timeEvolution (H k) s (applyFlow μ H continuousH hermitian t f k) at hs
  rw [hadd,hs,ht,evolution_add]
  rfl

def unitary (t : ℝ) : Space (ι := ι) μ ≃ₗᵢ[ℂ] Space (ι := ι) μ where
  toFun := flow μ H continuousH hermitian t
  invFun := flow μ H continuousH hermitian (-t)
  left_inv f := by rw [← flow_add,neg_add_cancel,flow_zero]
  right_inv f := by rw [← flow_add,add_neg_cancel,flow_zero]
  map_add' := (flow μ H continuousH hermitian t).map_add
  map_smul' := (flow μ H continuousH hermitian t).map_smul
  norm_map' := (flow μ H continuousH hermitian t).norm_map

def action : Multiplicative ℝ →* (Space (ι := ι) μ ≃ₗᵢ[ℂ] Space (ι := ι) μ) where
  toFun t := unitary μ H continuousH hermitian t.toAdd
  map_one' := by apply LinearIsometryEquiv.ext; intro f; exact flow_zero μ H continuousH hermitian f
  map_mul' s t := by
    apply LinearIsometryEquiv.ext
    intro f
    exact flow_add μ H continuousH hermitian s.toAdd t.toAdd f

end
end SaturationMonoid.PhysicsCore.LowEnergy.MatterSpace
