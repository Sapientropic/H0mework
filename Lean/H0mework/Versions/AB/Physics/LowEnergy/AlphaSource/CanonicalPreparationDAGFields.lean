import H0mework.Versions.AB.Physics.LowEnergy.AlphaSource.CanonicalPreparationEngineActualBudget

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumDAGCoefficient
open PreparationVacuumClockJacobian PreparationVacuumClockSymbol PreparationActualFactor
open PreparationVacuumEngineSource PreparationVacuumEngineBudget
open scoped BigOperators Matrix

abbrev CentralVariable := Fin 7
abbrev CentralPolynomial := MvPolynomial CentralVariable ℚ

-- The literal ordering is VARIABLES in source_clock_dag_majorants.py.
def sourceVariables (x : SourcePhase) : CentralVariable → ℝ :=
  ![actualC x,actualT x,actualS x 0 0,actualS x 1 1,actualS x 0 1,actualS x 0 2,actualS x 1 2]

def evalAt (x : SourcePhase) : CentralPolynomial →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) (sourceVariables x)

def polynomialSymbol (P : CentralPolynomial) : RealSymbol := fun x => evalAt x P

-- S22 is eliminated by its actual source trace, exactly as in the original arena.
def centralQ : Matrix (Fin 3) (Fin 3) CentralPolynomial :=
  !![MvPolynomial.X 1-MvPolynomial.X 2,-MvPolynomial.X 4,-MvPolynomial.X 5;
     -MvPolynomial.X 4,MvPolynomial.X 1-MvPolynomial.X 3,-MvPolynomial.X 6;
     -MvPolynomial.X 5,-MvPolynomial.X 6,MvPolynomial.X 2+MvPolynomial.X 3]

def determinantPolynomial : CentralPolynomial := centralQ.det
def adjugatePolynomial (i j : Fin 3) : CentralPolynomial := centralQ.adjugate i j

theorem actual_trace (x : SourcePhase) : actualT x=actualS x 0 0+actualS x 1 1+actualS x 2 2 := by
  simp only [actualT,actualS,T,Fin.sum_univ_three]

theorem actual_S22 (x : SourcePhase) : actualS x 2 2=actualT x-actualS x 0 0-actualS x 1 1 := by
  have trace := actual_trace x
  linarith

theorem actual_S10 (x : SourcePhase) : actualS x 1 0=actualS x 0 1 := S_symmetric _ _ _ _
theorem actual_S20 (x : SourcePhase) : actualS x 2 0=actualS x 0 2 := S_symmetric _ _ _ _
theorem actual_S21 (x : SourcePhase) : actualS x 2 1=actualS x 1 2 := S_symmetric _ _ _ _

theorem centralQ_source (x : SourcePhase) : centralQ.map (evalAt x)=sourceM x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [centralQ,evalAt,sourceVariables,sourceM,Matrix.map_apply,Matrix.smul_apply,
      actual_S10,actual_S20,actual_S21,actual_S22]
  ring

theorem determinantPolynomial_source (x : SourcePhase) : evalAt x determinantPolynomial=sourceDet x := by
  change evalAt x centralQ.det=(sourceM x).det
  rw [(evalAt x).map_det]
  change (centralQ.map (evalAt x)).det=(sourceM x).det
  rw [centralQ_source]

theorem adjugatePolynomial_source (x : SourcePhase) (i j : Fin 3) :
    evalAt x (adjugatePolynomial i j)=(sourceM x).adjugate i j := by
  have entire := (evalAt x).map_adjugate centralQ
  change centralQ.adjugate.map (evalAt x)=(centralQ.map (evalAt x)).adjugate at entire
  rw [centralQ_source] at entire
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) entire

def polePolynomial : Fin 3 → CentralPolynomial :=
  ![MvPolynomial.X 0,MvPolynomial.X 1,determinantPolynomial]

def poleFunction : Fin 3 → RealSymbol := ![actualC,actualT,sourceDet]

theorem polePolynomial_source (x : SourcePhase) (i : Fin 3) : evalAt x (polePolynomial i)=poleFunction i x := by
  fin_cases i
  · simp [polePolynomial,poleFunction,evalAt,sourceVariables]
  · simp [polePolynomial,poleFunction,evalAt,sourceVariables]
  · exact determinantPolynomial_source x

theorem poleFunction_nonzero (x : SourcePhase) (hx : x∈poleDomain) (i : Fin 3) : poleFunction i x≠0 := by
  fin_cases i
  · exact (C_positive hx.1).ne'
  · exact hx.1.2.2.ne'
  · exact hx.2

end LowEnergy.PreparationVacuumDAGCoefficient
