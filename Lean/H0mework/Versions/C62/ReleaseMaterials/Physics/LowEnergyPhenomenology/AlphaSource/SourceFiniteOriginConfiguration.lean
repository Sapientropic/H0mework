import H0mework.Versions.C62.ReleaseMaterials.Physics.LowEnergyPhenomenology.AlphaSource.SourceFiniteOriginDecomposition

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.PreparationPhysicalFiniteOriginCovariance
open SaturationMonoid.PhysicsCore SaturationMonoid.PhysicsCore.LowEnergy
open PreparationPhysicalNativePoleChargeReturn PreparationPhysicalNativeOriginPhaseWard
open PreparationVacuumMixedFieldReturn PreparationVacuumNativeFieldInjection PreparationVacuumNativeSourceRestriction
open SourcePropagationNativeActionHessian StageNineHolonomicField StageNineLorentzConnectionVariation
open Stage9C.Material.SpinPair ProofFreeRicherAnholonomicSource DiracExteriorMatterAction
open CanonicalGradedSpatialSource SourceQuantumScalarChart
open scoped BigOperators Matrix

private theorem primal_add (f g : Field289) : primalInsertion (f+g)=primalInsertion f+primalInsertion g := by
  have coefficients (spin : Fin 4) (color : Fin 3) :
      fieldPrimalComplex (f+g) spin color=fieldPrimalComplex f spin color+fieldPrimalComplex g spin color := by
    simp only [fieldPrimalComplex,fieldPrimal,Pi.add_apply,Complex.ofReal_add,mul_add]
    ring
  simp only [primalInsertion,coefficients,add_smul,Finset.sum_add_distrib]
private theorem primal_smul (r : ℝ) (f : Field289) : primalInsertion (r • f)=r • primalInsertion f := by
  have coefficients (spin : Fin 4) (color : Fin 3) :
      fieldPrimalComplex (r • f) spin color=r • fieldPrimalComplex f spin color := by
    simp [fieldPrimalComplex,fieldPrimal,Complex.real_smul,Complex.ofReal_mul]
    ring
  simp only [primalInsertion,coefficients,Complex.real_smul,mul_smul,←Finset.smul_sum]
  rfl
private theorem dual_add (f g : Field289) : dualInsertion (f+g)=dualInsertion f+dualInsertion g := by
  apply LinearMap.ext
  intro v
  have coefficients (spin : Fin 4) (color : Fin 3) :
      fieldDualComplex (f+g) spin color=fieldDualComplex f spin color+fieldDualComplex g spin color := by
    simp only [fieldDualComplex,fieldDual,Pi.add_apply,Complex.ofReal_add,mul_add]
    ring
  change (∑spin : Fin 4,∑color : Fin 3,fieldDualComplex (f+g) spin color*sourceTripletRead (v spin) color)=_
  simp only [coefficients,add_mul,Finset.sum_add_distrib]
  rfl
private theorem dual_smul (r : ℝ) (f : Field289) : dualInsertion (r • f)=r • dualInsertion f := by
  apply LinearMap.ext
  intro v
  have coefficients (spin : Fin 4) (color : Fin 3) :
      fieldDualComplex (r • f) spin color=r • fieldDualComplex f spin color := by
    simp [fieldDualComplex,fieldDual,Complex.real_smul,Complex.ofReal_mul]
    ring
  change (∑spin : Fin 4,∑color : Fin 3,fieldDualComplex (r • f) spin color*sourceTripletRead (v spin) color)=
    r • (∑spin : Fin 4,∑color : Fin 3,fieldDualComplex f spin color*sourceTripletRead (v spin) color)
  simp only [coefficients,smul_mul_assoc,←Finset.smul_sum]
private theorem auxiliary_add (f g : Field289) (pair : Fin 6) :
    gaugeBInsertion (f+g) pair=gaugeBInsertion f pair+gaugeBInsertion g pair := by
  simp only [gaugeBInsertion,fieldGaugeB,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  exact p286CoordinateEquiv.symm.map_add _ _
private theorem auxiliary_smul (r : ℝ) (f : Field289) (pair : Fin 6) :
    gaugeBInsertion (r • f) pair=r • gaugeBInsertion f pair := by
  simp only [gaugeBInsertion,fieldGaugeB,Pi.smul_apply,smul_eq_mul,mul_smul,←Finset.smul_sum]
  exact p286CoordinateEquiv.symm.map_smul _ _

/-- The source-generated independent primal/dual remainder has its actual spacetime rotation; none of its fields are erased. -/
def sourceFiniteOriginResidualPrimitive (imaginary : Bool) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) : StageNineHolonomicConfiguration where
  coframe:=0
  gravityConnection:=0
  gravityAuxiliary:=0
  gravitySimplicityMultiplier:=0
  gaugeConnection:=0
  gaugeAuxiliary:=0
  scalar:=0
  matter point:=diracMatrixMatterAction (ActiveGauge.rotation point)
    (primalInsertion (sourceFiniteOriginRemainderPart imaginary branch epsilon s n))
  conjugateMatter point:=(dualInsertion (sourceFiniteOriginRemainderPart imaginary branch epsilon s n)).comp
    (diracMatrixMatterAction (ActiveGauge.rotation point))

/-- All nine actual fields split into the same gauge-plus-phase ray and the retained independent matter/dual prototype. -/
theorem sourceFiniteOrigin_configuration (imaginary : Bool) (branch : Fin 2) (epsilon s : ℝ)
    (n : PhysicalMomentum) (r : ℝ) :
    nativeConfiguration (fun _=>r • sourceFiniteOriginPart imaginary branch epsilon s n)=
      configurationRay
        (configurationRay actual sourceOriginGaugePhasePrimitive
          (r*sourceOriginPart imaginary (sourceFiniteOriginAmplitude branch epsilon s n)))
        (sourceFiniteOriginResidualPrimitive imaginary branch epsilon s n) r := by
  rw [←sourceNativeOrigin_configuration,sourceFiniteOriginPart_decomposition]
  let a:=sourceOriginPart imaginary (sourceFiniteOriginAmplitude branch epsilon s n)
  let f:=sourceFiniteOriginRemainderPart imaginary branch epsilon s n
  let b:=sourceNativeOriginReal 0
  have zero:=sourceFiniteOriginRemainder_fields imaginary branch epsilon s n
  have lorentz : fieldLorentz (r • (a • b+f))=0 := by
    change r • (a • fieldLorentz b+fieldLorentz f)=0
    rw [(sourceNativeOriginReal_remaining 0).2.2,zero.2.2.2.1]
    simp
  have lorentzBase : fieldLorentz ((r*a) • b)=0 := by
    change (r*a) • fieldLorentz b=0
    rw [(sourceNativeOriginReal_remaining 0).2.2,smul_zero]
  have auxzero (pair : Fin 6) : gaugeBInsertion f pair=0 := by
    simp only [gaugeBInsertion,show fieldGaugeB f=0 from zero.2.2.2.2.2.2,Pi.zero_apply,
      zero_smul,Finset.sum_const_zero,map_zero]
  change nativeConfiguration (fun _=>r • (a • b+f))=
    configurationRay (nativeConfiguration (fun _=>(r*a) • b))
      (sourceFiniteOriginResidualPrimitive imaginary branch epsilon s n) r
  apply StageNineHolonomicConfiguration.ext <;> funext point
  all_goals simp only [nativeConfiguration,configurationRay,sourceFiniteOriginResidualPrimitive]
  · change actual.coframe point+r • (a • fieldCoframe b+fieldCoframe f)=
      actual.coframe point+(r*a) • fieldCoframe b+r • 0
    rw [zero.2.2.1]
    simp only [add_zero,smul_zero,smul_smul]
  · rw [lorentz,lorentzBase]
    simp
  · change actual.gravityAuxiliary point+r • (a • fieldGravityB b+fieldGravityB f)=
      actual.gravityAuxiliary point+(r*a) • fieldGravityB b+r • 0
    rw [zero.2.2.2.2.1]
    simp only [add_zero,smul_zero,smul_smul]
  · change actual.gravitySimplicityMultiplier point+r • (a • fieldMultiplier b+fieldMultiplier f)=
      actual.gravitySimplicityMultiplier point+(r*a) • fieldMultiplier b+r • 0
    rw [zero.2.2.2.2.2.1]
    simp only [add_zero,smul_zero,smul_smul]
  · funext mu
    rw [fieldGauge_smul,fieldGauge_add,fieldGauge_smul,show fieldGauge f mu=0 from congrFun zero.2.1 mu,
      fieldGauge_smul]
    simp only [add_zero,smul_smul,Pi.zero_apply,smul_zero]
  · funext pair
    rw [auxiliary_smul,auxiliary_add,auxiliary_smul,auxzero,auxiliary_smul]
    simp only [add_zero,smul_smul,Pi.zero_apply,smul_zero]
  · rw [fieldScalar_smul,fieldScalar_add,fieldScalar_smul,zero.1,fieldScalar_smul]
    simp only [add_zero,smul_smul,Pi.zero_apply,smul_zero]
  · rw [primal_smul,primal_add,primal_smul,primal_smul]
    change actual.matter point+diracMatrixMatterAction (ActiveGauge.rotation point)
      ((r:ℂ) • ((a:ℂ) • primalInsertion b+primalInsertion f))=
      actual.matter point+diracMatrixMatterAction (ActiveGauge.rotation point)
        (((r*a:ℝ):ℂ) • primalInsertion b)+(r:ℂ) •
          diracMatrixMatterAction (ActiveGauge.rotation point) (primalInsertion f)
    simp only [map_add,map_smul,smul_add,smul_smul,Complex.ofReal_mul]
    abel
  · rw [dual_smul,dual_add,dual_smul,dual_smul]
    change actual.conjugateMatter point+
      ((r:ℂ) • ((a:ℂ) • dualInsertion b+dualInsertion f)).comp
        (diracMatrixMatterAction (ActiveGauge.rotation point))=
      actual.conjugateMatter point+((((r*a:ℝ):ℂ) • dualInsertion b).comp
        (diracMatrixMatterAction (ActiveGauge.rotation point)))+
      (r:ℂ) • (dualInsertion f).comp (diracMatrixMatterAction (ActiveGauge.rotation point))
    simp only [LinearMap.smul_comp,LinearMap.add_comp,smul_add,smul_smul,Complex.ofReal_mul]
    abel

end LowEnergy.PreparationPhysicalFiniteOriginCovariance
