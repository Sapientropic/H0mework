import H0mework.Versions.Rc015842c.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalLorentzQuadratic

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumGravityLegendreSource
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField StageNineGlobalIntegratedAction StageNineBlockwiseConstitutive
open StageNineTopologicalFourFormPairing StageNineTopologicalGravityCurvatureVariancePairing
open StageNineHolonomicGravityCurvatureVarianceNormalization StageNineLorentzConnectionVariation
open LowEnergy.PreparationVacuumLorentzFieldInjection PointwiseDiracSpinConnectionLift
open scoped BigOperators Matrix

def sourceFlatLorentzInverse (i j : LorentzIndex) : ℝ:=
  ![
    ![![![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ)], ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]]],
    ![![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ)], ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ)]]],
    ![![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ)], ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ)]], ![![(1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ)]]],
    ![![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ), (0 : ℝ)]], ![![(-1/2 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ), (0 : ℝ)]], ![![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (1/2 : ℝ), (0 : ℝ)], ![(0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (0 : ℝ), (-1/2 : ℝ)]]]
  ] i.1 i.2 j.1 j.2

def sourceLorentzInverseNumerator (e : LorentzianCoframe) : Matrix LorentzIndex LorentzIndex ℝ:=fun i j=>
  ∑rho : Fin 4,∑sigma : Fin 4,e rho i.1*sourceFlatLorentzInverse (rho,i.2) (sigma,j.2)*e sigma j.1

def sourceLorentzInverse (e : LorentzianCoframe) : Matrix LorentzIndex LorentzIndex ℝ:=
  e.det⁻¹ • sourceLorentzInverseNumerator e

private theorem sourceConnectionBasis_pi (i : LorentzIndex) :
    sourceConnectionBasis i=Pi.single i.1 (Pi.single i.2 1) :=by
  rcases i with ⟨nu,b⟩
  funext mu a
  by_cases hm : mu=nu <;> by_cases ha : a=b <;>
    simp [sourceConnectionBasis,Pi.single_apply,hm,ha]

private theorem sourceConnectionBasis_matrix (i : LorentzIndex) (mu : Fin 4) :
    sourceConnectionMatrix (sourceConnectionBasis i) mu=
      if mu=i.1 then frameGenerator i.2 else 0 :=by
  rw [sourceConnectionBasis_pi]
  funext a b
  by_cases hm : mu=i.1
  · subst mu
    simp [sourceConnectionMatrix,frameGenerator,lorentzGenerator,lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,Pi.single_apply]
  · simp [sourceConnectionMatrix,hm,lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,Pi.single_apply]

def sourceLorentzStructure (a b c : Fin 6) : ℝ:=
  minkowskiInternalSign (pairFirst c)*(frameGenerator a*frameGenerator b-frameGenerator b*frameGenerator a)
    (pairFirst c) (pairSecond c)

private theorem sourceCurvaturePolarization_basis (i j : LorentzIndex) (c p : Fin 6) :
    sourceCurvaturePolarization (sourceConnectionBasis i) (sourceConnectionBasis j) c p=
      orientedLorentzBivectorBasisCoefficient p i.1 j.1*sourceLorentzStructure i.2 j.2 c :=by
  rcases i with ⟨mu,a⟩
  rcases j with ⟨nu,b⟩
  fin_cases mu <;> fin_cases nu <;> fin_cases p <;>
    simp [sourceCurvaturePolarization,sourceConnectionBasis_matrix,sourceLorentzStructure,
      orientedLorentzBivectorBasisCoefficient,pairFirst,pairSecond,Matrix.add_apply,Matrix.sub_apply] <;> ring

theorem sourceLorentzHessian_coefficients (e : LorentzianCoframe) (i j : LorentzIndex) :
    sourceLorentzHessian e i j=
      ∑c : Fin 6,∑p : Fin 6,physicalIIPlusBivector e c p*
        (orientedLorentzBivectorBasisCoefficient (twoFormComplement p) i.1 j.1*sourceLorentzStructure i.2 j.2 c) :=by
  rw [sourceLorentzHessian,sourceLorentzBilinear,gravityTopologicalBFCoefficient_eq_mixed]
  simp only [gravityTopologicalMixedWedgeCoefficient,orientedTwoFormWedgeCoefficient,
    generatedTwoFormWedgeCoefficient,sourceCurvaturePolarization_basis]

attribute [local irreducible] sourceLorentzHessian sourceLorentzInverseNumerator

private def sourceStructureTable (a b c : Fin 6) : ℝ:=
  ![
    ![![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)]],
    ![![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)]],
    ![![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)]],
    ![![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ)]],
    ![![(0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ)]],
    ![![(0:ℝ), (-1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(1:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (-1:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (1:ℝ), (0:ℝ), (0:ℝ)], ![(0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ), (0:ℝ)]]
  ] a b c

private theorem sourceLorentzStructure_table (a b c : Fin 6) :
    sourceLorentzStructure a b c=sourceStructureTable a b c :=by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [sourceLorentzStructure,sourceStructureTable,frameGenerator,lorentzGenerator,
      lorentzSkewConnectionOfBivectorOneForm,loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,
      minkowskiInternalSign,pairFirst,pairSecond,Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_six,Pi.single_apply,
      Matrix.cons_val,Fin.coe_ofNat_eq_mod,Nat.reduceMod]

macro "solve_source_lorentz_inverse_cell" : tactic => `(tactic|
  (
    simp only [Fintype.sum_prod_type,Fin.sum_univ_four,Fin.sum_univ_six]
    simp only [sourceLorentzHessian_coefficients,Fin.sum_univ_six]
    simp only [orientedLorentzBivectorBasisCoefficient,twoFormComplement,pairFirst,pairSecond,
      Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,
      Fin.reduceEq,Fin.isValue,reduceIte,ite_self,eq_self,and_false,false_and,and_true,true_and,
      mul_zero,zero_mul,add_zero,zero_add]
    simp only [sourceLorentzStructure_table,sourceStructureTable,
      Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Fin.isValue,
      mul_zero,zero_mul,mul_one,one_mul,add_zero,zero_add,sub_self,sub_zero,zero_sub,neg_zero,mul_neg,neg_mul]
    simp only [sourceLorentzInverseNumerator,Fin.sum_univ_four,sourceFlatLorentzInverse,
      Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,
      Fin.isValue,mul_zero,zero_mul,add_zero,zero_add,mul_one,one_mul]
    simp only [physicalIIPlusBivector,internalBivectorDual,lorentzianCoframeHodge,coframeWedge,
      LinearMap.coe_mk,AddHom.coe_mk,
      pairFirst,pairSecond,Matrix.cons_val,Matrix.cons_val',Matrix.cons_val_zero,Matrix.cons_val_one,Fin.isValue]
    rw [Matrix.det_succ_row_zero]
    simp [Fin.sum_univ_four,Matrix.det_fin_three,Matrix.submatrix,Fin.succAbove]
    ring
  ))

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_0_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,0) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (0,0)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_0_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,0) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (0,0)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_0_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,0) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (0,0)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_0_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,0) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (0,0)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_1_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,1) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (0,1)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_1_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,1) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (0,1)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_1_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,1) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (0,1)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_1_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,1) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (0,1)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_2_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,2) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (0,2)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_2_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,2) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (0,2)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_2_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,2) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (0,2)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_2_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,2) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (0,2)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_3_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,3) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (0,3)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_3_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,3) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (0,3)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_3_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,3) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (0,3)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_3_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,3) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (0,3)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_4_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,4) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (0,4)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_4_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,4) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (0,4)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_4_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,4) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (0,4)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_4_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,4) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (0,4)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_5_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,5) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (0,5)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_5_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,5) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (0,5)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_5_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,5) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (0,5)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock0_5_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,5) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (0,5)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_0_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,0) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (1,0)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_0_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,0) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (1,0)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_0_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,0) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (1,0)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_0_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,0) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (1,0)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_1_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,1) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (1,1)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_1_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,1) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (1,1)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_1_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,1) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (1,1)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_1_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,1) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (1,1)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_2_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,2) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (1,2)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_2_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,2) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (1,2)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_2_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,2) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (1,2)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_2_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,2) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (1,2)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_3_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,3) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (1,3)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_3_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,3) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (1,3)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_3_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,3) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (1,3)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_3_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,3) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (1,3)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_4_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,4) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (1,4)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_4_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,4) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (1,4)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_4_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,4) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (1,4)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_4_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,4) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (1,4)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_5_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,5) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (1,5)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_5_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,5) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (1,5)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_5_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,5) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (1,5)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock1_5_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,5) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (1,5)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_0_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,0) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (2,0)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_0_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,0) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (2,0)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_0_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,0) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (2,0)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_0_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,0) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (2,0)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_1_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,1) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (2,1)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_1_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,1) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (2,1)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_1_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,1) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (2,1)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_1_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,1) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (2,1)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_2_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,2) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (2,2)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_2_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,2) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (2,2)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_2_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,2) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (2,2)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_2_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,2) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (2,2)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_3_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,3) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (2,3)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_3_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,3) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (2,3)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_3_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,3) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (2,3)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_3_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,3) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (2,3)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_4_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,4) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (2,4)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_4_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,4) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (2,4)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_4_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,4) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (2,4)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_4_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,4) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (2,4)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_5_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,5) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (2,5)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_5_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,5) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (2,5)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_5_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,5) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (2,5)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock2_5_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,5) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (2,5)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_0_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,0) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (3,0)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_0_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,0) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (3,0)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_0_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,0) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (3,0)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_0_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,0) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (3,0)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_1_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,1) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (3,1)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_1_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,1) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (3,1)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_1_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,1) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (3,1)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_1_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,1) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (3,1)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_2_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,2) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (3,2)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_2_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,2) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (3,2)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_2_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,2) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (3,2)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_2_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,2) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (3,2)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_3_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,3) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (3,3)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_3_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,3) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (3,3)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_3_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,3) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (3,3)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_3_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,3) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (3,3)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_4_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,4) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (3,4)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_4_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,4) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (3,4)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_4_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,4) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (3,4)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_4_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,4) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (3,4)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_5_0 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,5) k*sourceLorentzInverseNumerator e k (0,b))=
      e.det*(if (3,5)=(0,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_5_1 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,5) k*sourceLorentzInverseNumerator e k (1,b))=
      e.det*(if (3,5)=(1,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_5_2 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,5) k*sourceLorentzInverseNumerator e k (2,b))=
      e.det*(if (3,5)=(2,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

set_option maxHeartbeats 700000 in
private theorem sourceInverseBlock3_5_3 (e : LorentzianCoframe) (b : Fin 6) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,5) k*sourceLorentzInverseNumerator e k (3,b))=
      e.det*(if (3,5)=(3,b) then 1 else 0) :=by
  fin_cases b <;> solve_source_lorentz_inverse_cell

private theorem sourceInverseRow0_0 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,0) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (0,0)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock0_0_0 e b
  · simpa using sourceInverseBlock0_0_1 e b
  · simpa using sourceInverseBlock0_0_2 e b
  · simpa using sourceInverseBlock0_0_3 e b

private theorem sourceInverseRow0_1 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,1) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (0,1)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock0_1_0 e b
  · simpa using sourceInverseBlock0_1_1 e b
  · simpa using sourceInverseBlock0_1_2 e b
  · simpa using sourceInverseBlock0_1_3 e b

private theorem sourceInverseRow0_2 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,2) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (0,2)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock0_2_0 e b
  · simpa using sourceInverseBlock0_2_1 e b
  · simpa using sourceInverseBlock0_2_2 e b
  · simpa using sourceInverseBlock0_2_3 e b

private theorem sourceInverseRow0_3 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,3) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (0,3)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock0_3_0 e b
  · simpa using sourceInverseBlock0_3_1 e b
  · simpa using sourceInverseBlock0_3_2 e b
  · simpa using sourceInverseBlock0_3_3 e b

private theorem sourceInverseRow0_4 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,4) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (0,4)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock0_4_0 e b
  · simpa using sourceInverseBlock0_4_1 e b
  · simpa using sourceInverseBlock0_4_2 e b
  · simpa using sourceInverseBlock0_4_3 e b

private theorem sourceInverseRow0_5 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (0,5) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (0,5)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock0_5_0 e b
  · simpa using sourceInverseBlock0_5_1 e b
  · simpa using sourceInverseBlock0_5_2 e b
  · simpa using sourceInverseBlock0_5_3 e b

private theorem sourceInverseRow1_0 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,0) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (1,0)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock1_0_0 e b
  · simpa using sourceInverseBlock1_0_1 e b
  · simpa using sourceInverseBlock1_0_2 e b
  · simpa using sourceInverseBlock1_0_3 e b

private theorem sourceInverseRow1_1 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,1) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (1,1)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock1_1_0 e b
  · simpa using sourceInverseBlock1_1_1 e b
  · simpa using sourceInverseBlock1_1_2 e b
  · simpa using sourceInverseBlock1_1_3 e b

private theorem sourceInverseRow1_2 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,2) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (1,2)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock1_2_0 e b
  · simpa using sourceInverseBlock1_2_1 e b
  · simpa using sourceInverseBlock1_2_2 e b
  · simpa using sourceInverseBlock1_2_3 e b

private theorem sourceInverseRow1_3 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,3) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (1,3)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock1_3_0 e b
  · simpa using sourceInverseBlock1_3_1 e b
  · simpa using sourceInverseBlock1_3_2 e b
  · simpa using sourceInverseBlock1_3_3 e b

private theorem sourceInverseRow1_4 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,4) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (1,4)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock1_4_0 e b
  · simpa using sourceInverseBlock1_4_1 e b
  · simpa using sourceInverseBlock1_4_2 e b
  · simpa using sourceInverseBlock1_4_3 e b

private theorem sourceInverseRow1_5 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (1,5) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (1,5)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock1_5_0 e b
  · simpa using sourceInverseBlock1_5_1 e b
  · simpa using sourceInverseBlock1_5_2 e b
  · simpa using sourceInverseBlock1_5_3 e b

private theorem sourceInverseRow2_0 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,0) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (2,0)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock2_0_0 e b
  · simpa using sourceInverseBlock2_0_1 e b
  · simpa using sourceInverseBlock2_0_2 e b
  · simpa using sourceInverseBlock2_0_3 e b

private theorem sourceInverseRow2_1 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,1) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (2,1)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock2_1_0 e b
  · simpa using sourceInverseBlock2_1_1 e b
  · simpa using sourceInverseBlock2_1_2 e b
  · simpa using sourceInverseBlock2_1_3 e b

private theorem sourceInverseRow2_2 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,2) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (2,2)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock2_2_0 e b
  · simpa using sourceInverseBlock2_2_1 e b
  · simpa using sourceInverseBlock2_2_2 e b
  · simpa using sourceInverseBlock2_2_3 e b

private theorem sourceInverseRow2_3 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,3) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (2,3)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock2_3_0 e b
  · simpa using sourceInverseBlock2_3_1 e b
  · simpa using sourceInverseBlock2_3_2 e b
  · simpa using sourceInverseBlock2_3_3 e b

private theorem sourceInverseRow2_4 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,4) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (2,4)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock2_4_0 e b
  · simpa using sourceInverseBlock2_4_1 e b
  · simpa using sourceInverseBlock2_4_2 e b
  · simpa using sourceInverseBlock2_4_3 e b

private theorem sourceInverseRow2_5 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (2,5) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (2,5)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock2_5_0 e b
  · simpa using sourceInverseBlock2_5_1 e b
  · simpa using sourceInverseBlock2_5_2 e b
  · simpa using sourceInverseBlock2_5_3 e b

private theorem sourceInverseRow3_0 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,0) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (3,0)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock3_0_0 e b
  · simpa using sourceInverseBlock3_0_1 e b
  · simpa using sourceInverseBlock3_0_2 e b
  · simpa using sourceInverseBlock3_0_3 e b

private theorem sourceInverseRow3_1 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,1) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (3,1)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock3_1_0 e b
  · simpa using sourceInverseBlock3_1_1 e b
  · simpa using sourceInverseBlock3_1_2 e b
  · simpa using sourceInverseBlock3_1_3 e b

private theorem sourceInverseRow3_2 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,2) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (3,2)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock3_2_0 e b
  · simpa using sourceInverseBlock3_2_1 e b
  · simpa using sourceInverseBlock3_2_2 e b
  · simpa using sourceInverseBlock3_2_3 e b

private theorem sourceInverseRow3_3 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,3) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (3,3)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock3_3_0 e b
  · simpa using sourceInverseBlock3_3_1 e b
  · simpa using sourceInverseBlock3_3_2 e b
  · simpa using sourceInverseBlock3_3_3 e b

private theorem sourceInverseRow3_4 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,4) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (3,4)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock3_4_0 e b
  · simpa using sourceInverseBlock3_4_1 e b
  · simpa using sourceInverseBlock3_4_2 e b
  · simpa using sourceInverseBlock3_4_3 e b

private theorem sourceInverseRow3_5 (e : LorentzianCoframe) (j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e (3,5) k*sourceLorentzInverseNumerator e k j)=
      e.det*(if (3,5)=j then 1 else 0) :=by
  rcases j with ⟨nu,b⟩
  fin_cases nu
  · simpa using sourceInverseBlock3_5_0 e b
  · simpa using sourceInverseBlock3_5_1 e b
  · simpa using sourceInverseBlock3_5_2 e b
  · simpa using sourceInverseBlock3_5_3 e b

private theorem sourceLorentzInversePolynomial (e : LorentzianCoframe) (i j : LorentzIndex) :
    (∑k : LorentzIndex,sourceLorentzHessian e i k*sourceLorentzInverseNumerator e k j)=
      e.det*(if i=j then 1 else 0) :=by
  rcases i with ⟨mu,a⟩
  fin_cases mu <;> fin_cases a
  · exact sourceInverseRow0_0 e j
  · exact sourceInverseRow0_1 e j
  · exact sourceInverseRow0_2 e j
  · exact sourceInverseRow0_3 e j
  · exact sourceInverseRow0_4 e j
  · exact sourceInverseRow0_5 e j
  · exact sourceInverseRow1_0 e j
  · exact sourceInverseRow1_1 e j
  · exact sourceInverseRow1_2 e j
  · exact sourceInverseRow1_3 e j
  · exact sourceInverseRow1_4 e j
  · exact sourceInverseRow1_5 e j
  · exact sourceInverseRow2_0 e j
  · exact sourceInverseRow2_1 e j
  · exact sourceInverseRow2_2 e j
  · exact sourceInverseRow2_3 e j
  · exact sourceInverseRow2_4 e j
  · exact sourceInverseRow2_5 e j
  · exact sourceInverseRow3_0 e j
  · exact sourceInverseRow3_1 e j
  · exact sourceInverseRow3_2 e j
  · exact sourceInverseRow3_3 e j
  · exact sourceInverseRow3_4 e j
  · exact sourceInverseRow3_5 e j

theorem sourceLorentzInverse_right (e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    sourceLorentzHessian e*sourceLorentzInverse e=1 :=by
  ext i j
  simp only [sourceLorentzInverse,Matrix.mul_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply]
  have factor : (∑k : LorentzIndex,sourceLorentzHessian e i k*(e.det⁻¹*sourceLorentzInverseNumerator e k j))=
      e.det⁻¹*(∑k : LorentzIndex,sourceLorentzHessian e i k*sourceLorentzInverseNumerator e k j):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [factor,sourceLorentzInversePolynomial]
  rw [←mul_assoc,inv_mul_cancel₀ nondegenerate,one_mul]

theorem sourceLorentzInverse_left (e : LorentzianCoframe) (nondegenerate : e.det≠0) :
    sourceLorentzInverse e*sourceLorentzHessian e=1 :=
  mul_eq_one_comm.mp (sourceLorentzInverse_right e nondegenerate)

end LowEnergy.PreparationVacuumGravityLegendreSource
