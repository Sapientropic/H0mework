import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceActualPoleFrameReturn
import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceScatteringFrequencyEnergy

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFinitePoleVertices
open SaturationMonoid SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open CanonicalGradedSpatialSource PreparationVacuumPhysicalCharacteristic PreparationVacuumPhysicalPoleSheet
open PreparationVacuumMixedFieldReturn PreparationVacuumFieldCovector
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativePhotonFluxReturn
open PreparationPhysicalNativePolarizationEmitter PreparationPhysicalScatteringFrequencyWard
open GaussComposite.PhysicalFullFieldScattering Electromagnetic.CanonicalCoframe
open FullQuantum FullSpace
open scoped BigOperators Matrix Topology
attribute [local irreducible] complexCoefficients complexFrequencyCoefficients complexMixedCoefficients
  realMixedCoefficientBilinear sourcePoleOriginField sourcePoleLiteralJet sourcePoleFastJet sourcePoleFrameResidual
  sourceNativeFrequencyPolarization

private def extendCoefficient (L : Field289→ₗ[ℝ] FiberOperators) (v : Fin 289→ℂ) : FiberOperators :=
  L (fun i=>(v i).re)+Complex.I • L (fun i=>(v i).im)

private theorem extendCoefficient_add (L : Field289→ₗ[ℝ] FiberOperators) (v w : Fin 289→ℂ) :
    extendCoefficient L (v+w)=extendCoefficient L v+extendCoefficient L w := by
  have re : (fun i=>((v+w) i).re)=(fun i=>(v i).re)+(fun i=>(w i).re) := rfl
  have im : (fun i=>((v+w) i).im)=(fun i=>(v i).im)+(fun i=>(w i).im) := rfl
  simp only [extendCoefficient,re,im,map_add,smul_add]
  abel

private theorem extendCoefficient_smul (L : Field289→ₗ[ℝ] FiberOperators) (z : ℂ) (v : Fin 289→ℂ) :
    extendCoefficient L (z • v)=z • extendCoefficient L v := by
  have real : (fun i=>((z • v) i).re)=z.re • (fun i=>(v i).re)-z.im • (fun i=>(v i).im) := by
    funext i
    simp [Complex.mul_re,smul_eq_mul]
  have imaginary : (fun i=>((z • v) i).im)=z.re • (fun i=>(v i).im)+z.im • (fun i=>(v i).re) := by
    funext i
    simp [Complex.mul_im,smul_eq_mul]
  rw [extendCoefficient,real,imaginary,map_sub,map_add,map_smul,map_smul,map_smul,map_smul]
  simp only [extendCoefficient]
  conv_rhs => rw [←Complex.re_add_im z]
  simp only [smul_add,smul_smul,add_smul,add_mul,mul_assoc,Complex.I_mul_I,mul_neg_one]
  module

private def coefficientLinear (L : Field289→ₗ[ℝ] FiberOperators) : (Fin 289→ℂ)→ₗ[ℂ] FiberOperators where
  toFun:=extendCoefficient L
  map_add':=extendCoefficient_add L
  map_smul':=extendCoefficient_smul L

private def densityLinear (k : Fin 4) : (Fin 289→ℂ)→ₗ[ℂ] FiberOperators :=
  coefficientLinear (realDensityCoefficients k)
private def frequencyLinear (k : Fin 4) : (Fin 289→ℂ)→ₗ[ℂ] FiberOperators :=
  coefficientLinear (realFrequencyCoefficients k)

private theorem density_source (v : Fin 289→ℂ) (k : Fin 4) :
    complexCoefficients (originalComplexDirection v) k=densityLinear k v := by
  simp only [densityLinear,coefficientLinear,extendCoefficient,complexCoefficients,
    originalComplexDirection,realDensityCoefficients_source,LinearMap.coe_mk,AddHom.coe_mk]
private theorem frequency_source (v : Fin 289→ℂ) (k : Fin 4) :
    complexFrequencyCoefficients (originalComplexDirection v) k=frequencyLinear k v := by
  simp only [frequencyLinear,coefficientLinear,extendCoefficient,complexFrequencyCoefficients,
    originalComplexDirection,realFrequencyCoefficients_source,LinearMap.coe_mk,AddHom.coe_mk]

private def extendBilinear (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (v w : Fin 289→ℂ) : FiberOperators :=
  L (fun i=>(v i).re) (fun i=>(w i).re)-L (fun i=>(v i).im) (fun i=>(w i).im)+
    Complex.I • (L (fun i=>(v i).re) (fun i=>(w i).im)+L (fun i=>(v i).im) (fun i=>(w i).re))
private theorem bilinear_left (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (v w : Fin 289→ℂ) :
    extendBilinear L v w=extendCoefficient
      (L.flip (fun i=>(w i).re)+Complex.I • L.flip (fun i=>(w i).im)) v := by
  simp only [extendBilinear,extendCoefficient,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.flip_apply,
    smul_add,smul_smul,Complex.I_mul_I]
  module
private theorem bilinear_right (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) (v w : Fin 289→ℂ) :
    extendBilinear L v w=extendCoefficient
      (L (fun i=>(v i).re)+Complex.I • L (fun i=>(v i).im)) w := by
  simp only [extendBilinear,extendCoefficient,LinearMap.add_apply,LinearMap.smul_apply,
    smul_add,smul_smul,Complex.I_mul_I]
  module
private def coefficientBilinear (L : Field289→ₗ[ℝ] Field289→ₗ[ℝ] FiberOperators) :
    (Fin 289→ℂ)→ₗ[ℂ] (Fin 289→ℂ)→ₗ[ℂ] FiberOperators where
  toFun v:=coefficientLinear (L (fun i=>(v i).re)+Complex.I • L (fun i=>(v i).im))
  map_add' v w:=by
    apply LinearMap.ext
    intro x
    change extendCoefficient _ x=extendCoefficient _ x+extendCoefficient _ x
    rw [←bilinear_right,←bilinear_right,←bilinear_right,bilinear_left,
      extendCoefficient_add,←bilinear_left,←bilinear_left]
  map_smul' z v:=by
    apply LinearMap.ext
    intro x
    change extendCoefficient _ x=z • extendCoefficient _ x
    rw [←bilinear_right,←bilinear_right,bilinear_left,extendCoefficient_smul,←bilinear_left]
private def mixedBilinear (k : Fin 4) := coefficientBilinear (realMixedCoefficientBilinear k)
private theorem mixed_source (v w : Fin 289→ℂ) (k : Fin 4) :
    complexMixedCoefficients (originalComplexDirection v) (originalComplexDirection w) k=mixedBilinear k v w := by
  change _=extendCoefficient _ w
  rw [←bilinear_right]
  simp only [complexMixedCoefficients,originalComplexDirection,extendBilinear,realMixedCoefficientBilinear_source]

/-- These are the original full fields; the jet keeps the literal slow columns and the original fast columns together. -/
def sourceFinitePoleComponents (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 3→Fin 289→ℂ :=
  ![sourcePoleOriginField branch epsilon s n,
    (epsilon:ℂ)^2 • (sourcePoleLiteralJet branch epsilon s n+sourcePoleFastJet branch epsilon s n),
    sourcePoleFrameResidual branch epsilon s n]

theorem sourceFinitePoleComponents_sum (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) :
    sourceNativeFrequencyPolarization branch epsilon s n=∑i : Fin 3,sourceFinitePoleComponents branch epsilon s n i := by
  have returned:=sourceNativeFrequencyPolarization_firstReturn branch epsilon s n nonzero
  rw [sourcePoleJetField_literal] at returned
  simp only [sourceFinitePoleComponents,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ]
  linear_combination returned

/-- Full252 density coefficients on all four coordinate legs. -/
def sourceFinitePoleDensity (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  fun k=>∑i : Fin 3,complexCoefficients (originalComplexDirection (sourceFinitePoleComponents branch epsilon s n i)) k
/-- Full independent-dual Hamiltonian frequency coefficients on all four coordinate legs. -/
def sourceFinitePoleFrequency (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  fun k=>∑i : Fin 3,complexFrequencyCoefficients (originalComplexDirection (sourceFinitePoleComponents branch epsilon s n i)) k
/-- All nine origin/jet/residual Hessian crosses, including both shell and density contacts. -/
def sourceFinitePoleMixed (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) : Fin 4→FiberOperators :=
  fun k=>∑i : Fin 3,∑j : Fin 3,complexMixedCoefficients
    (originalComplexDirection (sourceFinitePoleComponents branch epsilon s n i))
    (originalComplexDirection (sourceFinitePoleComponents branch epsilon s n j)) k

theorem sourceFinitePoleDensity_actual (c : ℂ) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) :
    complexCoefficients (originalComplexDirection (c • sourceNativeFrequencyPolarization branch epsilon s n))=
      c • sourceFinitePoleDensity branch epsilon s n := by
  funext k
  simp only [density_source,sourceFinitePoleComponents_sum branch epsilon s n nonzero,map_smul,map_sum,
    sourceFinitePoleDensity,Pi.smul_apply]

theorem sourceFinitePoleFrequency_actual (c : ℂ) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) :
    complexFrequencyCoefficients (originalComplexDirection (c • sourceNativeFrequencyPolarization branch epsilon s n))=
      c • sourceFinitePoleFrequency branch epsilon s n := by
  funext k
  simp only [frequency_source,sourceFinitePoleComponents_sum branch epsilon s n nonzero,map_smul,map_sum,
    sourceFinitePoleFrequency,Pi.smul_apply]

theorem sourceFinitePoleMixed_actual (c d : ℂ) (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum)
    (nonzero : epsilon≠0) :
    complexMixedCoefficients (originalComplexDirection (c • sourceNativeFrequencyPolarization branch epsilon s n))
      (originalComplexDirection (d • sourceNativeFrequencyPolarization branch epsilon s n))=
      (c*d) • sourceFinitePoleMixed branch epsilon s n := by
  funext k
  simp only [mixed_source,sourceFinitePoleComponents_sum branch epsilon s n nonzero,map_smul,map_sum,
    LinearMap.smul_apply,LinearMap.sum_apply,smul_smul,sourceFinitePoleMixed,Pi.smul_apply,Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem sourceFinitePoleDensity_literal (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    sourceFinitePoleDensity branch epsilon s n k=
      complexCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n)) k+
      (epsilon:ℂ)^2 • complexCoefficients (originalComplexDirection (sourcePoleLiteralJet branch epsilon s n)) k+
      (epsilon:ℂ)^2 • complexCoefficients (originalComplexDirection (sourcePoleFastJet branch epsilon s n)) k+
      complexCoefficients (originalComplexDirection (sourcePoleFrameResidual branch epsilon s n)) k := by
  simp only [sourceFinitePoleDensity,sourceFinitePoleComponents,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
    density_source,map_smul,map_add,smul_add]
  abel

theorem sourceFinitePoleFrequency_literal (branch : Fin 2) (epsilon s : ℝ) (n : PhysicalMomentum) (k : Fin 4) :
    sourceFinitePoleFrequency branch epsilon s n k=
      complexFrequencyCoefficients (originalComplexDirection (sourcePoleOriginField branch epsilon s n)) k+
      (epsilon:ℂ)^2 • complexFrequencyCoefficients (originalComplexDirection (sourcePoleLiteralJet branch epsilon s n)) k+
      (epsilon:ℂ)^2 • complexFrequencyCoefficients (originalComplexDirection (sourcePoleFastJet branch epsilon s n)) k+
      complexFrequencyCoefficients (originalComplexDirection (sourcePoleFrameResidual branch epsilon s n)) k := by
  simp only [sourceFinitePoleFrequency,sourceFinitePoleComponents,Fin.sum_univ_three,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
    frequency_source,map_smul,map_add,smul_add]
  abel

end LowEnergy.PreparationPhysicalFinitePoleVertices
