import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualSourcePreparedSchurClockField

set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 256
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace LowEnergy.GaussComposite.ActualSourcePreparedSchurClockBalance
open Polynomial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumPhysicalCharacteristic PreparationVacuumOriginalGreenFeedback
open ActualDressedFullCoulomb ActualDressedEMTensorClock ActualDressedCorrectedGreen
open ActualDressedUniformMaterialCoefficients ActualDressedOrderedStatic ActualDressedZeroDamping
open ActualEMAction ActualSourcePreparedEMClockEquation ActualSourcePreparedEMNativeRow ActualSourcePreparedEMNativeRead
open ActualSourcePreparedClockReducedPencil ActualSourcePreparedSchurClockField
open ActualSourcePreparedAuxiliarySchurBalance ActualSourcePreparedTemporalEMConstraint
open ActualSourcePreparedN3EMChargeRead ActualDressedNoetherCoulombUnit
open SaturationMonoid.PhysicsCore Stage9C.Material.SpinPair
open scoped Matrix BigOperators
attribute [local irreducible] commonJacobi emOriginalJacobi sourceMatrix sourceSchurClockFullFieldNumerator
  sourceSchurClockDeterminant sourceTemporalEMForce sourceEMClockForce Matrix.mulVec


private def clockConstant : ℂ →+* (ℂ[X])[X] :=
  (Polynomial.C : ℂ[X] →+* (ℂ[X])[X]).comp (Polynomial.C : ℂ →+* ℂ[X])


private theorem constant_eval_generic {R : Type*} [CommRing R] (x y z : R) :
    ((Polynomial.evalRingHom y).comp (Polynomial.mapRingHom (Polynomial.evalRingHom x)))
      (((Polynomial.C : R[X] →+* (R[X])[X]).comp (Polynomial.C : R →+* R[X])) z)=z := by
  simp only [RingHom.comp_apply,Polynomial.coe_mapRingHom,Polynomial.map_C,
    Polynomial.coe_evalRingHom,Polynomial.eval_C]

private theorem constant_eval (eps sigma : ℝ) (z : ℂ) : sourceClockEval eps sigma (clockConstant z)=z := by
  exact constant_eval_generic (eps : ℂ) (sigma : ℂ) z


private theorem force_eval (eps sigma : ℝ) : sourceClockEval eps sigma ∘ sourceEMClockForce=sourceTemporalEMForce := by
  funext i
  simp only [Function.comp_apply,sourceEMClockForce,sourceClockEval,RingHom.comp_apply,clockSpecialize,
    Polynomial.coe_mapRingHom,Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C]


private theorem constant_matrix_eval {I J : Type*} (M : Matrix I J ℂ) (eps sigma : ℝ) :
    (M.map clockConstant).map (sourceClockEval eps sigma)=M := by
  ext i j
  exact constant_eval eps sigma (M i j)


def sourceSchurClockJacobi (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) :=
  fun i j => staticIRClockSlice (commonJacobi n i j)

private theorem jacobi_eval (n : PhysicalMomentum) (eps sigma : ℝ) :
    (sourceSchurClockJacobi n).map (sourceClockEval eps sigma)=emOriginalJacobi (frequencyRay eps 0 n) := by
  ext i j
  have source := congrFun (congrFun (common_jacobi_eval n eps sigma 0) i) j
  change MvPolynomial.eval (irValues eps sigma 0) (commonJacobi n i j)=_ at source
  change (clockSpecialize eps (staticIRClockSlice (commonJacobi n i j))).eval (sigma : ℂ)=_
  rw [ir_clock_specialize,damping_slice_eval]
  exact source


def sourceSchurClockDriverNumerator (event : DressedEvent) (n : PhysicalMomentum) : Fin 289 → (ℂ[X])[X] :=
  sourceSchurClockJacobi n*ᵥsourceSchurClockFullFieldNumerator event n-
    sourceSchurClockDeterminant event n • sourceEMClockForce

private theorem map_driver {I : Type*} [Fintype I]
    (f : ((ℂ[X])[X]) →+* ℂ) (J : Matrix I I ((ℂ[X])[X]))
    (v E : I → (ℂ[X])[X]) (d : (ℂ[X])[X]) :
    f ∘ (J*ᵥv-d • E)=J.map f*ᵥ(f ∘ v)-f d • (f ∘ E) := by
  funext i
  change f ((J*ᵥv) i-d*E i)=(J.map f*ᵥ(f ∘ v)) i-f d*f (E i)
  rw [map_sub,map_mul,f.map_mulVec]


theorem source_schur_clock_driver_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma ∘ sourceSchurClockDriverNumerator event n=sourceSchurDriverNumerator event n eps sigma := by
  unfold sourceSchurClockDriverNumerator sourceSchurDriverNumerator
  rw [map_driver,jacobi_eval,source_schur_clock_full_field_eval,source_schur_clock_determinant_eval,force_eval]


private def clockBalance {I : Type*} [Fintype I]
    (E driver v : I → ((ℂ[X])[X])) (B L : Matrix I I ((ℂ[X])[X]))
    (x : (ℂ[X])[X]) (i : I) : (ℂ[X])[X] :=
  dotProduct E driver-(B*ᵥv) i-x^2*(L*ᵥv) i

attribute [local irreducible] clockBalance

private def clockBackgroundMatrix : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) :=
  (sourceMatrix sourceEMNativeBackgroundTerms 0).map clockConstant

private def clockLowerMatrix (n : PhysicalMomentum) : Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) :=
  (sourceMatrix sourceEMNativeLowerTerms (frequencyRay 1 0 n)).map clockConstant

private def clockEpsilon : (ℂ[X])[X] := (Polynomial.C : ℂ[X] →+* (ℂ[X])[X]) (X : ℂ[X])

attribute [local irreducible] clockBackgroundMatrix clockLowerMatrix clockEpsilon

/-- Complete numerator before either IR coordinate is specialized: original
Noether driver, Background10, epsilon squared Lower6 and reconstructed field. -/
def sourceSchurClockBalanceNumerator (event : DressedEvent) (n : PhysicalMomentum) : (ℂ[X])[X] :=
  @clockBalance (Fin 289) (inferInstance : Fintype (Fin 289))
    (show Fin 289 → (ℂ[X])[X] from sourceEMClockForce)
    (show Fin 289 → (ℂ[X])[X] from sourceSchurClockDriverNumerator event n)
    (show Fin 289 → (ℂ[X])[X] from sourceSchurClockFullFieldNumerator event n)
    (show Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) from clockBackgroundMatrix)
    (show Matrix (Fin 289) (Fin 289) ((ℂ[X])[X]) from clockLowerMatrix n)
    clockEpsilon (0 : Fin 289)

private theorem epsilon_eval (eps sigma : ℝ) : sourceClockEval eps sigma (C (X : ℂ[X]))=(eps : ℂ) := by
  simp only [sourceClockEval,RingHom.comp_apply,clockSpecialize,Polynomial.coe_mapRingHom,
    Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,Polynomial.eval_X]


private theorem map_clock_balance {I : Type*} [Fintype I]
    (f : ((ℂ[X])[X]) →+* ℂ) (E driver v : I → ((ℂ[X])[X]))
    (B L : Matrix I I ((ℂ[X])[X])) (x : (ℂ[X])[X]) (i : I) (N : (ℂ[X])[X])
    (value : N=clockBalance E driver v B L x i) :
    f N=dotProduct (f ∘ E) (f ∘ driver)-(B.map f*ᵥ(f ∘ v)) i-
      (f x)^2*(L.map f*ᵥ(f ∘ v)) i := by
  rw [value]
  unfold clockBalance
  rw [map_sub,map_sub,map_mul,map_pow,f.map_dotProduct,f.map_mulVec,f.map_mulVec]

theorem source_schur_clock_balance_numerator_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceClockEval eps sigma (sourceSchurClockBalanceNumerator event n)=
      dotProduct sourceTemporalEMForce (sourceSchurDriverNumerator event n eps sigma)-
        sourceEMNativeBackgroundRead (sourceSchurFullFieldNumerator event n eps sigma)-
        (eps : ℂ)^2*sourceEMNativeLowerRead (frequencyRay 1 0 n) (sourceSchurFullFieldNumerator event n eps sigma) := by
  have generated := map_clock_balance (sourceClockEval eps sigma) sourceEMClockForce
    (sourceSchurClockDriverNumerator event n) (sourceSchurClockFullFieldNumerator event n)
    clockBackgroundMatrix (clockLowerMatrix n) clockEpsilon (0 : Fin 289)
    (sourceSchurClockBalanceNumerator event n) rfl
  have background : clockBackgroundMatrix.map (sourceClockEval eps sigma)=sourceMatrix sourceEMNativeBackgroundTerms 0 := by
    unfold clockBackgroundMatrix
    exact constant_matrix_eval _ eps sigma
  have lower : (clockLowerMatrix n).map (sourceClockEval eps sigma)=sourceMatrix sourceEMNativeLowerTerms (frequencyRay 1 0 n) := by
    unfold clockLowerMatrix
    exact constant_matrix_eval _ eps sigma
  have epsilon : sourceClockEval eps sigma clockEpsilon=(eps : ℂ) := by
    unfold clockEpsilon
    exact epsilon_eval eps sigma
  rw [force_eval,source_schur_clock_driver_eval,source_schur_clock_full_field_eval,
    background,lower,epsilon] at generated
  unfold sourceEMNativeBackgroundRead sourceEMNativeLowerRead
  exact generated


/-- The complete bivariate source quotient equals the whole finite actual EM
balance. No coordinate return or joint-limit value is supplied as a premise. -/
theorem source_schur_clock_balance_fraction (event : DressedEvent) (n : PhysicalMomentum) (eps sigma : ℝ) :
    sourceSchurEMBalance event n eps sigma=
      sourceClockEval eps sigma (sourceSchurClockBalanceNumerator event n)/
        sourceClockEval eps sigma (sourceSchurClockDeterminant event n) := by
  rw [source_schur_clock_balance_numerator_eval,source_schur_clock_determinant_eval]
  rfl


theorem source_em_schur_clock_finite_return (event : DressedEvent) (e : scaleDomain) (sigma : ℝ)
    (n : PhysicalMomentum) (unit : spatialSquare n=1) (positive : 0<sigma)
    (regular : correctedDet event e.val 0 sigma n≠0) :
    (e.val : ℂ)^4*sourceN3TemporalEMCoefficient event e.val sigma n=
      noetherPairScale^2/(2*(lapse : ℂ))*((3/4 : ℂ)+
        sourceClockEval e.val sigma (sourceSchurClockBalanceNumerator event n)/
          sourceClockEval e.val sigma (sourceSchurClockDeterminant event n)) := by
  rw [←source_schur_clock_balance_fraction]
  exact source_em_schur_finite_return event e sigma n unit positive regular


end LowEnergy.GaussComposite.ActualSourcePreparedSchurClockBalance
