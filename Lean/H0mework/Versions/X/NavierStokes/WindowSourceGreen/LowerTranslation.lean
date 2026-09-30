import H0mework.Versions.X.NavierStokes.WindowSchurAbsolute.Fourier

set_option autoImplicit false
open scoped BigOperators Topology ENNReal
namespace SaturationMonoid.NavierStokes.NativeWindowWeakLowerTranslation
open Set Filter MeasureTheory UnitAddTorus
open ThreeDimensionalPeriodicCoarseFilterCore ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open NativePhysicalFourier (Torus)
open NativeWindowAbsoluteTimeFourier (polynomial)
open NativePhysicalGradient (multiplier)
noncomputable section
local instance physicalMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance physicalProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance physicalHaar : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs AddCircle.haarAddCircle.IsAddHaarMeasure
attribute [local instance 10000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
attribute [local instance 10000] PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def pairing (B : Torus → E →L[ℂ] E) (F : Finset IntegerWavevector) (u v : IntegerWavevector → E) : ℂ :=
  ∫ x : Torus,inner ℂ (polynomial F u x) (B x (polynomial F v x))

def orbit (B : Torus → E →L[ℂ] E) (j : Coordinate) (z : ℝ) : Torus → E →L[ℂ] E :=
  fun x => B (x+NativePhysicalTranslation.displacement j z)

def derivative (j : Coordinate) (u : IntegerWavevector → E) : IntegerWavevector → E :=
  fun k => multiplier k j • u k

theorem fourier_translation (f : Torus → ℂ) (offset : Torus) (k : IntegerWavevector) :
    mFourierCoeff (fun x => f (x+offset)) k=mFourier k offset*mFourierCoeff f k := by
  have shifted:=integral_add_right_eq_self (fun x : Torus => mFourier (-k) (x-offset)*f x) offset (μ := volume)
  simp only [add_sub_cancel_right] at shifted
  change (∫ x : Torus,mFourier (-k) x*f (x+offset))=_
  rw [shifted]
  simp_rw [sub_eq_add_neg,NativePhysicalTranslation.character_add,NativePhysicalTranslation.character_neg_neg]
  simp only [mFourierCoeff,smul_eq_mul,mul_assoc,mul_comm _ (mFourier k offset),← integral_const_mul]

theorem fourier_scale (f : Torus → ℂ) (a : ℂ) (k : IntegerWavevector) :
    mFourierCoeff (fun x => a*f x) k=a*mFourierCoeff f k := by
  simp only [mFourierCoeff,smul_eq_mul]
  simp_rw [show ∀ x : Torus,mFourier (-k) x*(a*f x)=a*(mFourier (-k) x*f x) by intro x; ring]
  exact integral_const_mul _ _

theorem pairing_fourier (B : Torus → E →L[ℂ] E)
    (regular : ∀ u v : E,Integrable (fun x : Torus => inner ℂ u (B x v)))
    (F : Finset IntegerWavevector) (u v : IntegerWavevector → E) :
    pairing B F u v=∑ p∈F,∑ q∈F,mFourierCoeff (fun x => inner ℂ (u p) (B x (v q))) (p-q) := by
  have paid (p q : IntegerWavevector) : Integrable (fun x : Torus =>
      mFourier (-(p-q)) x*inner ℂ (u p) (B x (v q))) :=
    (regular (u p) (v q)).bdd_mul (mFourier (-(p-q))).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => ((mFourier (-(p-q))).norm_coe_le_norm x).trans_eq mFourier_norm)
  have point (x : Torus) : inner ℂ (polynomial F u x) (B x (polynomial F v x))=
      ∑ p∈F,∑ q∈F,mFourier (-(p-q)) x*inner ℂ (u p) (B x (v q)) := by
    simp only [polynomial,ContinuousMap.coe_mk,map_sum,map_smul,sum_inner,inner_sum,inner_smul_left,inner_smul_right,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    rw [← mFourier_neg]
    have phase:mFourier (-p) x*mFourier q x=mFourier (-(p-q)) x := by
      rw [← mFourier_add]
      congr 1
      abel_nf
    calc
      _=(mFourier (-p) x*mFourier q x)*inner ℂ (u p) (B x (v q)) := by ring
      _=_ := by rw [phase]
  simp only [pairing,point]
  rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => paid p q))]
  exact Finset.sum_congr rfl fun p _ => by
    rw [integral_finsetSum _ (fun q _ => paid p q)]
    rfl

theorem orbit_regular (B : Torus → E →L[ℂ] E)
    (regular : ∀ u v : E,Integrable (fun x : Torus => inner ℂ u (B x v))) (j : Coordinate) (z : ℝ) :
    ∀ u v : E,Integrable (fun x : Torus => inner ℂ u (orbit B j z x v)) := by
  intro u v
  exact ((measurePreserving_add_right (volume : Measure Torus) (NativePhysicalTranslation.displacement j z)).integrable_comp (regular u v).aestronglyMeasurable).mpr (regular u v)

theorem orbit_fourier (B : Torus → E →L[ℂ] E)
    (regular : ∀ u v : E,Integrable (fun x : Torus => inner ℂ u (B x v)))
    (F : Finset IntegerWavevector) (u v : IntegerWavevector → E) (j : Coordinate) (z : ℝ) :
    pairing (orbit B j z) F u v=∑ p∈F,∑ q∈F,NativeSpatialTranslation.phase j z (p-q)*
      mFourierCoeff (fun x => inner ℂ (u p) (B x (v q))) (p-q) := by
  rw [pairing_fourier _ (orbit_regular B regular j z)]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  simpa only [orbit,NativePhysicalTranslation.character_displacement] using
    fourier_translation (fun x => inner ℂ (u p) (B x (v q))) (NativePhysicalTranslation.displacement j z) (p-q)

theorem weak_read (B : Torus → E →L[ℂ] E)
    (regular : ∀ u v : E,Integrable (fun x : Torus => inner ℂ u (B x v)))
    (F : Finset IntegerWavevector) (u v : IntegerWavevector → E) (j : Coordinate) :
    -pairing B F (derivative j u) v-pairing B F u (derivative j v)=
      ∑ p∈F,∑ q∈F,multiplier (p-q) j*mFourierCoeff (fun x => inner ℂ (u p) (B x (v q))) (p-q) := by
  simp only [pairing_fourier B regular,derivative,inner_smul_left,map_smul,inner_smul_right,fourier_scale,
    ← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  rw [starRingEnd_apply,NativeWindowStressHeatEnergy.multiplier_star,NativeWindowHistoryTranslation.multiplier_sub]
  ring

theorem coefficient_hasDerivAt (B : Torus → E →L[ℂ] E)
    (regular : ∀ u v : E,Integrable (fun x : Torus => inner ℂ u (B x v)))
    (F : Finset IntegerWavevector) (u v : IntegerWavevector → E) (j : Coordinate) :
    HasDerivAt (fun z => pairing (orbit B j z) F u v)
      (-pairing B F (derivative j u) v-pairing B F u (derivative j v)) 0 := by
  rw [weak_read B regular]
  have each (p q : IntegerWavevector) := (NativeSpatialTranslation.phase_hasDerivAt j (p-q) 0).mul_const
    (mFourierCoeff (fun x => inner ℂ (u p) (B x (v q))) (p-q))
  simp only [NativeSpatialTranslation.phase_zero,mul_one] at each
  have combined:=HasDerivAt.sum (u := F) (fun p _ => HasDerivAt.sum (u := F) (fun q _ => each p q))
  convert combined using 1
  funext z
  rw [orbit_fourier B regular]
  simp only [Finset.sum_apply]

end
end SaturationMonoid.NavierStokes.NativeWindowWeakLowerTranslation
