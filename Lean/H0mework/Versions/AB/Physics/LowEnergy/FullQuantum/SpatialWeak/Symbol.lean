import H0mework.Versions.AB.Physics.LowEnergy.FullQuantum.SpatialGreen.Integral

/-! The original uncompressed Dirac symbol is the Fourier image of its actual spatial partials. -/
set_option autoImplicit false
open MeasureTheory
namespace SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialWeak
open FullSpace SpatialGreen Retarded Triangular YangMills.FullPairing
open ProofFreeRicherAnholonomicSource Stage9C.Material.SpinPair DiracExteriorMatterAction
open StageNineHolonomicField StageNineCoframeLocalDifferentiability
noncomputable section

def gammaMother (point : BasePoint) (j : Fin 3) : Mother :=
  diracMatrixMatterAction (inverseCoframeDiracGamma {coframe := actual.coframe point, derivative := 0} j.succ)

theorem diracKernel_affine (point : BasePoint) (momentum : Fin 3 → ℝ) (z : ℂ) :
    diracKernel actual point momentum z=diracKernel actual point 0 z-
      ∑ j, (momentum j : ℂ) • gammaMother point j := by
  apply LinearMap.ext
  intro v
  simp only [diracKernel,lowerSymbol,knownSymbol,gammaMother,LinearMap.add_apply,
    LinearMap.sub_apply,LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply,
    Module.End.one_apply,Pi.zero_apply,Complex.ofReal_zero,mul_zero,zero_smul,zero_add,
    map_add,map_smul,Finset.sum_add_distrib,smul_add,Finset.smul_sum,smul_smul]
  have scalar (r : ℂ) : Complex.I*(Complex.I*r) = -r := by
    rw [← mul_assoc,Complex.I_mul_I,neg_one_mul]
  have minus (r : ℂ) (w : DiracExteriorMatterCarrier) : (-r) • w = -(r • w) := neg_smul r w
  simp only [scalar,minus,Finset.sum_neg_distrib]
  abel

def constant (point : BasePoint) (energy damping : ℝ) : FiberOperators :=
  operator (diracKernel actual point 0 (spectralParameter energy damping))

def spatial (point : BasePoint) (j : Fin 3) : FiberOperators := operator (gammaMother point j)

private theorem operator_sum {ι : Type*} [Fintype ι] (A : ι → Mother) :
    operator (∑ i, A i)=∑ i, operator (A i) := by
  ext v
  simp [operator]

private theorem operator_sub (A B : Mother) : operator (A-B)=operator A-operator B := by
  ext v
  simp [operator]

theorem symbol_affine (point : BasePoint) (energy damping : ℝ) (frequency : Position) :
    symbol point energy damping frequency=constant point energy damping-
      ∑ j, ((physicalMomentum frequency j : ℝ) : ℂ) • spatial point j := by
  rw [symbol,diracKernel_affine,operator_sub,operator_sum]
  simp only [operator_smul]
  rfl

end
end SaturationMonoid.PhysicsCore.LowEnergy.FullQuantum.SpatialWeak
