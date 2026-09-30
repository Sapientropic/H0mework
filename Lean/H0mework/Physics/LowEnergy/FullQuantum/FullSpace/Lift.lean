import H0mework.Physics.LowEnergy.FullQuantum.FullSpace.Growth
import Mathlib.Analysis.Fourier.LpSpace

/-! Bounded complete-fiber multipliers act on the original 252-component L² carrier. -/
set_option autoImplicit false
open MeasureTheory Filter Topology
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
open YangMills.FullPairing
noncomputable section

abbrev Position := EuclideanSpace ℝ (Fin 3)
abbrev FullMatterL2 := Lp (α := Position) Hilbert 2 volume
abbrev FiberOperators := Hilbert →L[ℂ] Hilbert

variable (matrix : Position → FiberOperators) (continuousMatrix : Continuous matrix)
    (bound : ℝ) (bounded : ∀ x, ‖matrix x‖≤bound)

include continuousMatrix in
theorem multiplier_measurable (initial : FullMatterL2) :
    AEStronglyMeasurable (fun x => matrix x (initial x)) volume :=
  (isBoundedBilinearMap_apply : IsBoundedBilinearMap ℂ
    (fun pair : FiberOperators × Hilbert => pair.1 pair.2)).continuous.comp_aestronglyMeasurable
      (continuousMatrix.aestronglyMeasurable.prodMk (Lp.memLp initial).aestronglyMeasurable)

include continuousMatrix bounded in
theorem multiplier_memLp (initial : FullMatterL2) : MemLp (fun x => matrix x (initial x)) 2 volume := by
  apply (Lp.memLp initial).of_le_mul (c := bound) (multiplier_measurable matrix continuousMatrix initial)
  exact ae_of_all _ fun x => (matrix x).le_opNorm (initial x) |>.trans
    (mul_le_mul_of_nonneg_right (bounded x) (norm_nonneg _))

def multiplierValue (initial : FullMatterL2) : FullMatterL2 :=
  (multiplier_memLp matrix continuousMatrix bound bounded initial).toLp _

theorem multiplierValue_ae (initial : FullMatterL2) :
    multiplierValue matrix continuousMatrix bound bounded initial=ᵐ[volume] fun x => matrix x (initial x) :=
  (multiplier_memLp matrix continuousMatrix bound bounded initial).coeFn_toLp

theorem multiplierValue_add (first second : FullMatterL2) :
    multiplierValue matrix continuousMatrix bound bounded (first+second)=
      multiplierValue matrix continuousMatrix bound bounded first+multiplierValue matrix continuousMatrix bound bounded second := by
  apply Lp.ext
  filter_upwards [multiplierValue_ae matrix continuousMatrix bound bounded (first+second),
    multiplierValue_ae matrix continuousMatrix bound bounded first,
    multiplierValue_ae matrix continuousMatrix bound bounded second,Lp.coeFn_add first second,
    Lp.coeFn_add (multiplierValue matrix continuousMatrix bound bounded first)
      (multiplierValue matrix continuousMatrix bound bounded second)] with x hall hfirst hsecond input output
  simp only [hall,output,input,Pi.add_apply,hfirst,hsecond,map_add]

theorem multiplierValue_smul (c : ℂ) (initial : FullMatterL2) :
    multiplierValue matrix continuousMatrix bound bounded (c • initial)=
      c • multiplierValue matrix continuousMatrix bound bounded initial := by
  apply Lp.ext
  filter_upwards [multiplierValue_ae matrix continuousMatrix bound bounded (c • initial),
    multiplierValue_ae matrix continuousMatrix bound bounded initial,Lp.coeFn_smul c initial,
    Lp.coeFn_smul c (multiplierValue matrix continuousMatrix bound bounded initial)] with x hall hin input output
  simp only [hall,output,input,Pi.smul_apply,hin,map_smul]

theorem multiplierValue_bound (nonnegative : 0≤bound) (initial : FullMatterL2) :
    ‖multiplierValue matrix continuousMatrix bound bounded initial‖≤bound*‖initial‖ := by
  calc
    _ ≤ ‖(bound : ℂ) • initial‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [multiplierValue_ae matrix continuousMatrix bound bounded initial,
        Lp.coeFn_smul (bound : ℂ) initial] with x applied scaled
      rw [applied,scaled]
      change ‖matrix x (initial x)‖≤‖(bound : ℂ) • initial x‖
      rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg nonnegative]
      exact ((matrix x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (bounded x) (norm_nonneg _))
    _ = _ := by rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg nonnegative]

def multiplierLinear : FullMatterL2 →ₗ[ℂ] FullMatterL2 where
  toFun := multiplierValue matrix continuousMatrix bound bounded
  map_add' := multiplierValue_add matrix continuousMatrix bound bounded
  map_smul' c initial := multiplierValue_smul matrix continuousMatrix bound bounded c initial

def multiplier (nonnegative : 0≤bound) : FullMatterL2 →L[ℂ] FullMatterL2 :=
  (multiplierLinear matrix continuousMatrix bound bounded).mkContinuous bound
    (multiplierValue_bound matrix continuousMatrix bound bounded nonnegative)

theorem multiplier_norm (nonnegative : 0≤bound) :
    ‖multiplier matrix continuousMatrix bound bounded nonnegative‖≤bound :=
  LinearMap.mkContinuous_norm_le _ nonnegative _

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.FullSpace
