import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.CanonicalPreparationOriginalSpinScalar

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace LowEnergy.PreparationVacuumLorentzFieldInjection
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open ProofFreeRicherAnholonomicSource StageNineHolonomicField DiracExteriorMatterAction DiracCliffordRepresentation
open PointwiseDiracSpinConnectionLift StageNineLorentzConnectionVariation
open SU7ExteriorBreakingYukawa SU7ExteriorMatterRepresentation StageNineDiracDualYukawaSpinJurisdiction
open FullQuantum.StateGreen FullQuantum.CoframeResponse
local instance : DecidableEq Quantum.Index:=Classical.decEq _
open PreparationVacuumGaugeSourceInjection PreparationVacuumNativeLocalWard
open scoped Matrix Matrix.Norms.L2Operator BigOperators
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def lorentzMatrix (v : Fin 6→ℝ) : LorentzianCoframe:=
  lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 v) 0

def spinMatrix (v : Fin 6→ℝ) : DiracMatrix:=
  diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 v)) 0

def lorentzBracketCoordinates (v w : Fin 6→ℝ) (a : Fin 6) : ℝ:=
  minkowskiInternalSign (lorentzBivectorFirst a)*
    (lorentzMatrix v*lorentzMatrix w-lorentzMatrix w*lorentzMatrix v)
      (lorentzBivectorFirst a) (lorentzBivectorSecond a)

 theorem spinMatrix_bivector (v : Fin 6→ℝ) :
    spinMatrix v=∑a : Fin 6,((2:ℂ)⁻¹*(v a:ℂ)) •
      (diracGamma (lorentzBivectorFirst a)*diracGamma (lorentzBivectorSecond a)) :=by
  unfold spinMatrix diracSpinConnectionLift
  simp only [loweredLorentzConnectionCoefficient_ofBivectorOneForm,Pi.single_eq_same]

/-- The original six bivector coefficients generate the actual infinitesimal Spin representation. -/
 theorem spinMatrix_lie (v w : Fin 6→ℝ) :
    spinMatrix (lorentzBracketCoordinates v w)=spinMatrix v*spinMatrix w-spinMatrix w*spinMatrix v :=by
  rw [spinMatrix_bivector,spinMatrix_bivector,spinMatrix_bivector]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBracketCoordinates,lorentzMatrix,lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst,lorentzBivectorSecond,pairFirst,pairSecond,minkowskiInternalSign,
      diracGamma,diracGammaZero,diracGammaOne,diracGammaTwo,diracGammaThree,
      Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,
      Pi.single_apply,Fin.coe_ofNat_eq_mod,Nat.reduceMod] <;>
    ring_nf <;> simp only [Complex.I_sq] <;> ring

 theorem lorentzMatrix_lie (v w : Fin 6→ℝ) :
    lorentzMatrix (lorentzBracketCoordinates v w)=lorentzMatrix v*lorentzMatrix w-lorentzMatrix w*lorentzMatrix v :=by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lorentzBracketCoordinates,lorentzMatrix,lorentzSkewConnectionOfBivectorOneForm,
      loweredLorentzBivectorMatrix,orientedLorentzBivectorBasisCoefficient,
      lorentzBivectorFirst,lorentzBivectorSecond,pairFirst,pairSecond,minkowskiInternalSign,
      Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_six,Matrix.cons_val,
      Pi.single_apply,Fin.coe_ofNat_eq_mod,Nat.reduceMod] <;> ring

 theorem spinLinear_coefficients (omega : LorentzBivectorOneForm) (mu : Fin 4) :
    spinLinear mu omega=spinCoordinates (spinMatrix (omega mu)) :=by
  change spinCoordinates (diracSpinConnectionLift (lorentzSkewConnectionOfBivectorOneForm omega) mu)=_
  apply congrArg spinCoordinates
  rw [spinMatrix_bivector,diracSpinConnectionLift]
  simp only [loweredLorentzConnectionCoefficient_ofBivectorOneForm]

 theorem spinCoordinates_multiply (A B : DiracMatrix) : spinCoordinates (A*B)=spinCoordinates A*spinCoordinates B :=by
  change Quantum.operatorMatrix (diracMatrixMatterAction (A*B))=
    Quantum.operatorMatrix (diracMatrixMatterAction A)*Quantum.operatorMatrix (diracMatrixMatterAction B)
  rw [←Quantum.matrix_composition]
  apply congrArg Quantum.operatorMatrix
  apply LinearMap.ext
  intro v
  exact (diracMatrixMatterAction_apply_apply A B v).symm

 theorem spinLinear_lie (v w : Fin 6→ℝ) :
    spinCoordinates (spinMatrix (lorentzBracketCoordinates v w))=
      spinCoordinates (spinMatrix v)*spinCoordinates (spinMatrix w)-
        spinCoordinates (spinMatrix w)*spinCoordinates (spinMatrix v) :=by
  rw [spinMatrix_lie,map_sub,spinCoordinates_multiply,spinCoordinates_multiply]

 def connectionBivectorDirection (a : Fin 6) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (omega : LorentzBivectorOneForm) : LorentzBivectorOneForm:=
  fun mu=>theta • lorentzBracketCoordinates (Pi.single a 1) (omega mu)-parameterDerivative mu • Pi.single a 1

 theorem connectionBivectorDirection_state (a : Fin 6) (theta : ℝ) (parameterDerivative : Fin 4→ℝ)
    (omega : LorentzBivectorOneForm) (mu : Fin 4) :
    spinLinear mu (connectionBivectorDirection a theta parameterDerivative omega)=
      theta • (nativeMatterGenerator (Fin.natAdd 3 a)*spinLinear mu omega-
        spinLinear mu omega*nativeMatterGenerator (Fin.natAdd 3 a))-
      parameterDerivative mu • nativeMatterGenerator (Fin.natAdd 3 a) :=by
  rw [spinLinear_coefficients,connectionBivectorDirection]
  have spinadd : ∀v w : Fin 6→ℝ,spinMatrix (v+w)=spinMatrix v+spinMatrix w:=by
    intro v w
    unfold spinMatrix
    rw [←diracSpinConnectionLiftLinear_apply]
    have source : lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 (v+w))=
        lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 v)+lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 w):=by
      rw [←lorentzSkewConnectionOfBivectorOneForm_add]
      exact congrArg lorentzSkewConnectionOfBivectorOneForm (Pi.single_add _ _ _)
    rw [source,map_add]
    rfl
  have spinreal (r : ℝ) (v : Fin 6→ℝ) : spinMatrix (r • v)=r • spinMatrix v:=by
    unfold spinMatrix
    rw [←diracSpinConnectionLiftLinear_apply]
    have source : lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 (r • v))=
        r • lorentzSkewConnectionOfBivectorOneForm (Pi.single 0 v):=by
      rw [←lorentzSkewConnectionOfBivectorOneForm_smul]
      exact congrArg lorentzSkewConnectionOfBivectorOneForm (Pi.single_smul _ _ _)
    rw [source,map_smul]
    rfl
  have spinlinear : spinMatrix
      (theta • lorentzBracketCoordinates (Pi.single a 1) (omega mu)-parameterDerivative mu • Pi.single a 1)=
      theta • spinMatrix (lorentzBracketCoordinates (Pi.single a 1) (omega mu))-
        parameterDerivative mu • spinMatrix (Pi.single a 1):=by
    rw [sub_eq_add_neg,spinadd,show -(parameterDerivative mu • Pi.single a 1)=(-parameterDerivative mu) • Pi.single a 1 by simp,
      spinreal,spinreal,neg_smul]
    rfl
  rw [spinlinear]
  have read : spinCoordinates
      (theta • spinMatrix (lorentzBracketCoordinates (Pi.single a 1) (omega mu))-
        parameterDerivative mu • spinMatrix (Pi.single a 1))=
      theta • spinCoordinates (spinMatrix (lorentzBracketCoordinates (Pi.single a 1) (omega mu)))-
        parameterDerivative mu • spinCoordinates (spinMatrix (Pi.single a 1)):=by
    exact (spinCoordinates.restrictScalars ℝ).map_sub _ _ |>.trans
      (congrArg₂ (fun x y : SourceMatrix=>x-y)
        ((spinCoordinates.restrictScalars ℝ).map_smul theta _)
        ((spinCoordinates.restrictScalars ℝ).map_smul (parameterDerivative mu) _))
  rw [read,spinLinear_lie,←spinLinear_coefficients]
  change theta • (spinCoordinates (spinGenerator a)*spinLinear mu omega-
    spinLinear mu omega*spinCoordinates (spinGenerator a))-
      parameterDerivative mu • spinCoordinates (spinGenerator a)=_
  rw [spinGenerator_original]

end LowEnergy.PreparationVacuumLorentzFieldInjection
