import H0mework.Versions.CAP.Physics.LowEnergy.AlphaSource.CanonicalPreparationSourceSignalCausalResponse

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationVacuumCurrentNativeLaplaceBridge
open SourcePropagationNativeActionHessian SourcePropagationNativeEulerHistory
open PreparationVacuumPhysicalFeedback PreparationVacuumGaugeSourceInjection
open PreparationVacuumOriginalGreenFeedback PreparationVacuumCurrentSignalOperator
open scoped BigOperators ContDiff Topology Matrix
attribute [local irreducible] nativeHessian nativeJetBasis originalJacobi

private def timeSymbol (derivative : Option (Fin 4)) : ℂ:=
  if derivative=some 0 then 1 else 0

private def spatialSymbol (derivative : Option (Fin 4)) (spatial : Fin 3→ℂ) : ℂ:=
  jetSymbol derivative (fullMomentum spatial 0)

private theorem symbol_affine (derivative : Option (Fin 4)) (spatial : Fin 3→ℂ) (clock : ℂ) :
    jetSymbol derivative (fullMomentum spatial clock)=spatialSymbol derivative spatial+clock*timeSymbol derivative :=by
  cases derivative with
  | none=>simp [jetSymbol,spatialSymbol,timeSymbol]
  | some mu=>
    refine Fin.cases ?_ (fun j=>?_) mu
    · simp [jetSymbol,spatialSymbol,timeSymbol,fullMomentum]
    · simp [jetSymbol,spatialSymbol,timeSymbol,fullMomentum]

private theorem negative_momentum (spatial : Fin 3→ℂ) (clock : ℂ) :
    -(fullMomentum spatial clock)=fullMomentum (-spatial) (-clock) :=by
  funext mu
  refine Fin.cases ?_ (fun j=>?_) mu <;> rfl

def sourceTemporalFirst (spatial : Fin 3→ℂ) : Matrix (Fin 289) (Fin 289) ℂ:=fun row column=>
  ∑left : Option (Fin 4),∑right : Option (Fin 4),
    (nativeHessian (nativeJetBasis (left,row)) (nativeJetBasis (right,column)) : ℂ)*
      (spatialSymbol left (-spatial)*timeSymbol right-timeSymbol left*spatialSymbol right spatial)

def sourceTemporalSecond : Matrix (Fin 289) (Fin 289) ℂ:=fun row column=>
  ∑left : Option (Fin 4),∑right : Option (Fin 4),
    -(nativeHessian (nativeJetBasis (left,row)) (nativeJetBasis (right,column)) : ℂ)*timeSymbol left*timeSymbol right

theorem sourceTemporalSecond_actual (row column : Fin 289) :
    sourceTemporalSecond row column=
      -(nativeHessian (nativeJetBasis (some 0,row)) (nativeJetBasis (some 0,column)) : ℂ) :=by
  simp only [sourceTemporalSecond,timeSymbol,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true]

theorem sourceTemporalPencil_generated (spatial : Fin 3→ℂ) (clock : ℂ) :
    nativeFourierHessian nativeHessian (fullMomentum spatial clock)=
      nativeFourierHessian nativeHessian (fullMomentum spatial 0)+clock • sourceTemporalFirst spatial+
        clock^2 • sourceTemporalSecond :=by
  ext row column
  simp only [nativeFourierHessian,negative_momentum,symbol_affine,sourceTemporalFirst,sourceTemporalSecond,
    Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring

theorem sourceTemporalPencil_original (spatial : Fin 3→ℂ) (clock : ℂ) :
    originalJacobi (fullMomentum spatial clock)=originalJacobi (fullMomentum spatial 0)+
      clock • sourceTemporalFirst spatial+clock^2 • sourceTemporalSecond :=by
  rw [←nativeActionFourierHessian_original,sourceTemporalPencil_generated,nativeActionFourierHessian_original]

theorem sourceTemporalPencil_difference (spatial : Fin 3→ℂ) (readClock driveClock : ℂ) :
    originalJacobi (fullMomentum spatial readClock)-originalJacobi (fullMomentum spatial driveClock)=
      (readClock-driveClock) • (sourceTemporalFirst spatial+(readClock+driveClock) • sourceTemporalSecond) :=by
  rw [sourceTemporalPencil_original spatial readClock,sourceTemporalPencil_original spatial driveClock]
  ext row column
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  ring

end LowEnergy.PreparationVacuumCurrentNativeLaplaceBridge
