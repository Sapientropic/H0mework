import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed.Densities

set_option autoImplicit false
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
open Propagation.Interface Collision
open scoped Matrix BigOperators

def couplingCosineQ : ℚ := couplingQ.1
def couplingSineQ : ℚ := -couplingQ.2

theorem coupling_cosine_source : (couplingCosineQ : ℝ)=Input.finiteCosine := by
  have h := congrArg Complex.re couplingQ_value
  simpa [couplingCosineQ,Scalar.value,Input.finiteCosine] using h

theorem coupling_sine_source : (couplingSineQ : ℝ)=Input.finiteSine := by
  have h := congrArg Complex.im couplingQ_value
  have im : (couplingQ.2 : ℝ)=Input.finiteCouplingPhase.im := by simpa [Scalar.value] using h
  simp only [couplingSineQ,Rat.cast_neg,Input.finiteSine,im]

theorem scalar_value_sub (a b : Scalar.QComplex) : Scalar.value (a-b)=Scalar.value a-Scalar.value b := by
  simp only [Scalar.value,Prod.fst_sub,Prod.snd_sub,Rat.cast_sub]
  ring

def pairQ : MatrixQ (Basis × Basis) (Basis × Basis) := fun i j =>
  couplingCosineQ^2 • Scalar.multiply (systemQ i.1 j.1) (bathQ i.2 j.2)+
    couplingSineQ^2 • Scalar.multiply (bathQ i.1 j.1) (systemQ i.2 j.2)+
    Scalar.multiply (0,couplingCosineQ*couplingSineQ)
      (Scalar.multiply (systemQ i.1 j.2) (bathQ i.2 j.1)-
        Scalar.multiply (systemQ i.2 j.1) (bathQ i.1 j.2))

theorem pairQ_value : qvalue pairQ=InputProducts.pair := by
  have c : (couplingCosineQ : ℂ)=(Input.finiteCosine : ℂ) := by exact_mod_cast coupling_cosine_source
  have s : (couplingSineQ : ℂ)=(Input.finiteSine : ℂ) := by exact_mod_cast coupling_sine_source
  have sys (i j : Basis) : Scalar.value (systemQ i j)=InputProducts.system i j := congrFun (congrFun systemQ_value i) j
  have bath (i j : Basis) : Scalar.value (bathQ i j)=InputProducts.bath i j := congrFun (congrFun bathQ_value i) j
  have original : InputProducts.pair=jointNext InputProducts.system InputProducts.bath Input.finiteCosine Input.finiteSine := rfl
  rw [original,jointNext_expansion]
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [qvalue,pairQ,Scalar.value_add,Scalar.value_smul,Scalar.value_multiply,scalar_value_sub,sys,bath,
    Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul,mul_swap_apply,swap_mul_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply]
  simp only [Scalar.value,Rat.cast_zero,zero_add,Rat.cast_mul,Rat.cast_pow,c,s]
  ring

def ordinaryPairQ (a b : Basis) : MatrixQ (Fin 2) (Fin 2) := pairQ.submatrix (pairAddress a b) (pairAddress a b)

theorem ordinaryPairQ_value (a b : Basis) : qvalue (ordinaryPairQ a b)=originalPairBlock a b := by
  rw [ordinaryPairQ,qvalue_submatrix,pairQ_value]
  rfl

def ordinaryInputQ (a b : Basis) : MatrixQ (Fin 2 × Fin 2) (Fin 2 × Fin 2) := qkron (ordinaryPairQ a b) environmentQ

theorem ordinaryInputQ_value (a b : Basis) : qvalue (ordinaryInputQ a b)=Matrix.kronecker (originalPairBlock a b) Prepared.finiteEnvironment := by
  rw [ordinaryInputQ,qvalue_kron,ordinaryPairQ_value,environmentQ_value]

def diagonalInputQ (a : Basis) : MatrixQ (Fin 2) (Fin 2) := qscale (pairQ (a,a) (a,a)) environmentQ

theorem diagonalInputQ_value (a : Basis) : qvalue (diagonalInputQ a)=InputProducts.pair (a,a) (a,a) • Prepared.finiteEnvironment := by
  have same : Scalar.value (pairQ (a,a) (a,a))=InputProducts.pair (a,a) (a,a) := congrFun (congrFun pairQ_value (a,a)) (a,a)
  rw [diagonalInputQ,qvalue_scale,same,environmentQ_value]

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.NetContraction.Fixed
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
