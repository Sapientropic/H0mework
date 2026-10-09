import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterNativeCarrier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore NamedMatterWedgeQt
open GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussDensityCore GaussScalarTransport GaussLiveMomentum
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open scoped BigOperators InnerProductSpace ContDiff

abbrev ScalarEnd:=ScalarTest→ₗ[ℂ]ScalarTest
def epsilonFiber20(dual:Bool)(e:Epsilon20):FockFiber:=wedgeFiber dual (epsilon20Coordinates dual e)
private theorem epsilon20_value(dual:Bool)(e:Epsilon20)(f:ScalarTest)(z:SourceCoordinateSlice):
    epsilon20Test dual e f z=f z • epsilonFiber20 dual e:=actual_wedge_test_value dual _ f z
attribute [local irreducible] epsilon20Test epsilonFiber20
def epsilonSection(dual:Bool)(e:Epsilon20):ScalarTest→ₗ[ℂ]QuantumTest where
  toFun f:=epsilon20Test dual e f
  map_add' f g:=by
    apply DFunLike.ext
    intro z
    change epsilon20Test dual e (f+g) z=epsilon20Test dual e f z+epsilon20Test dual e g z
    rw [epsilon20_value,epsilon20_value,epsilon20_value]
    exact add_smul _ _ _
  map_smul' c f:=by
    apply DFunLike.ext
    intro z
    change epsilon20Test dual e (c • f) z=c • epsilon20Test dual e f z
    rw [epsilon20_value,epsilon20_value]
    exact (smul_smul c (f z) (epsilonFiber20 dual e)).symm

theorem epsilon_section_value(dual:Bool)(e:Epsilon20)(f:ScalarTest)(z:SourceCoordinateSlice):
    epsilonSection dual e f z=f z • epsilonFiber20 dual e:=epsilon20_value dual e f z

private theorem epsilon_component(dual:Bool)(e:Epsilon20)(f:ScalarTest)(word:Occupation):
    component word (epsilonSection dual e f)=epsilonFiber20 dual e word • f:=by
  apply DFunLike.ext
  intro z
  rw [component_apply,epsilon_section_value]
  simp [PiLp.smul_apply,smul_eq_mul,mul_comm]

theorem actual_epsilon_number_three(dual:Bool)(e:Epsilon20)(word:Occupation)(hw:word.card≠3):
    epsilonFiber20 dual e word=0:=by
  classical
  simp only [epsilonFiber20,wedgeFiber,WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul]
  apply Finset.sum_eq_zero
  intro w _
  have hn:word≠occupation dual w.val:=by
    intro h
    apply hw
    rw [h,occupation_card,w.property]
  simp [fiberBasis,EuclideanSpace.single,hn]

/-- The original live native directional derivative stays on the same normalized epsilon source. -/
theorem actual_epsilon_directional(dual:Bool)(e:Epsilon20)(v:Ambient)(f:ScalarTest):
    directional v (epsilonSection dual e f)=epsilonSection dual e (fieldDerivative v f):=by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change component word (directional v (epsilonSection dual e f)) z=
    component word (epsilonSection dual e (fieldDerivative v f)) z
  rw [GaussMomentumAdjoint.component_directional,epsilon_component,map_smul,epsilon_component]

/-- The actual Number-weighted transpose returns with N=3; the coframe-volume density is retained. -/
theorem actual_epsilon_native_transpose(dual:Bool)(e:Epsilon20)(v:Ambient)(f:ScalarTest):
    GaussMomentumAdjoint.derivativeTranspose v (epsilonSection dual e f)=
      epsilonSection dual e (fieldTranspose 3 v f):=by
  apply embed_injective
  rw [GaussMomentumAdjoint.transpose_embed]
  apply PiLp.ext
  intro word
  change scalarEmbed word.card (fieldTranspose word.card v (component word (epsilonSection dual e f)))=
    scalarEmbed word.card (component word (epsilonSection dual e (fieldTranspose 3 v f)))
  rw [epsilon_component,epsilon_component,map_smul,map_smul,map_smul]
  by_cases hw:word.card=3
  · rw [hw]
  · rw [actual_epsilon_number_three dual e word hw,zero_smul,zero_smul]

def nativeCharge(dual:Bool)(v:Ambient)(z:SourceCoordinateSlice):ℂ:=
  3*nativeHyper dual (inverseL z v).1

theorem native_charge_smooth(dual:Bool)(v:Ambient)(z:physicalChart):
    ContDiffAt ℝ ∞ (nativeCharge dual v) z.val:=by
  let R:NativeLie→ₗ[ℝ]StageNineHolonomicField.P286CoordinateCarrier:=
    { toFun:=fun a=>a
      map_add':=by intros; rfl
      map_smul':=by intros; rfl }
  let L:NativeLie→ₗ[ℝ]ℂ:=
    { toFun:=fun a=>(StageNineHolonomicField.p286CoordinateEquiv.symm (R a)).2.2.1
      map_add':=by
        intro a b
        rw [R.map_add,StageNineHolonomicField.p286CoordinateEquiv.symm.map_add]
        rfl
      map_smul':=by
        intro r a
        rw [R.map_smul,StageNineHolonomicField.p286CoordinateEquiv.symm.map_smul]
        rfl }
  have hL:ContDiff ℝ ∞ L:=L.toContinuousLinearMap.contDiff
  have hH:ContDiff ℝ ∞ (nativeHyper dual):=by
    cases dual with
    | false=>exact hL
    | true=>exact Complex.conjCLE.contDiff.comp hL
  exact contDiffAt_const.mul (hH.contDiffAt.comp z.val (((inverse_smooth z).clm_apply contDiffAt_const).fst))

def nativeChargeAction(dual:Bool)(v:Ambient):ScalarEnd:=
  GaussDensityCore.multiply (nativeCharge dual v) (native_charge_smooth dual v)
def chargedScalarMomentum(dual:Bool)(v:Ambient):ScalarEnd:=
  (-Complex.I) • (fieldDerivative v+nativeChargeAction dual v)
def chargedScalarAdjoint(dual:Bool)(v:Ambient):ScalarEnd:=
  Complex.I • (fieldTranspose 3 v-nativeChargeAction dual v)

private theorem connection_section(dual:Bool)(e:Epsilon20)(v:Ambient)(f:ScalarTest):
    GaussFockPair.connectionAction v (epsilonSection dual e f)=
      epsilonSection dual e (nativeChargeAction dual v f):=by
  apply DFunLike.ext
  intro z
  change connection v z (epsilon20Test dual e f z)=_
  rw [actual_epsilon20_connection,epsilon20_value,epsilon_section_value]
  change nativeCharge dual v z • (f z • epsilonFiber20 dual e)=
    (nativeCharge dual v z*f z) • epsilonFiber20 dual e
  exact smul_smul _ _ _

theorem actual_epsilon_native_momentum(dual:Bool)(e:Epsilon20)(v:Ambient)(f:ScalarTest):
    covariantMomentum v (epsilonSection dual e f)=epsilonSection dual e (chargedScalarMomentum dual v f):=by
  change (-Complex.I) • (directional v (epsilonSection dual e f)+
    GaussFockPair.connectionAction v (epsilonSection dual e f))=_
  rw [actual_epsilon_directional,connection_section,←map_add,←map_smul]
  rfl

theorem actual_epsilon_native_adjoint(dual:Bool)(e:Epsilon20)(v:Ambient)(f:ScalarTest):
    GaussMomentumAdjoint.adjoint v (epsilonSection dual e f)=epsilonSection dual e (chargedScalarAdjoint dual v f):=by
  change Complex.I • (GaussMomentumAdjoint.derivativeTranspose v (epsilonSection dual e f)-
    GaussFockPair.connectionAction v (epsilonSection dual e f))=_
  rw [actual_epsilon_native_transpose,connection_section,←map_sub,←map_smul]
  rfl

def scalarRealMultiply(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val):ScalarEnd:=
  GaussDensityCore.multiply (fun z=>(c z:ℂ))
    (fun z=>Complex.ofRealCLM.contDiff.contDiffAt.comp z.val (hc z))

private theorem real_section(dual:Bool)(e:Epsilon20)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:ScalarTest):
    GaussNativeForm.multiply c hc (epsilonSection dual e f)=
      epsilonSection dual e (scalarRealMultiply c hc f):=by
  apply DFunLike.ext
  intro z
  rw [GaussNativeForm.multiply_apply,epsilon_section_value,epsilon_section_value]
  change (c z:ℂ) • (f z • epsilonFiber20 dual e)=((c z:ℂ)*f z) • epsilonFiber20 dual e
  exact smul_smul _ _ _

def chargedNativeSandwich(dual:Bool)(v w:Ambient)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val):ScalarEnd:=
  (chargedScalarAdjoint dual v).comp ((scalarRealMultiply c hc).comp (chargedScalarMomentum dual w))

private theorem sandwich_section(dual:Bool)(e:Epsilon20)(v w:Ambient)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:ScalarTest):
    GaussNativeForm.sandwich v w c hc (epsilonSection dual e f)=
      epsilonSection dual e (chargedNativeSandwich dual v w c hc f):=by
  simp only [GaussNativeForm.sandwich,LinearMap.comp_apply,actual_epsilon_native_momentum,
    real_section,actual_epsilon_native_adjoint,chargedNativeSandwich]

def chargedNativeAction(dual:Bool):ScalarEnd:=
  (1/2:ℂ) • (∑a:GaussNativeForm.ScalarIndex,
    chargedNativeSandwich dual (GaussNativeForm.scalarDirection a) (GaussNativeForm.scalarDirection a)
      GaussNativeEnergy.scalarWeight GaussNativeEnergy.scalarWeight_smooth)+
  (1/2:ℂ) • (∑a:GaussNativeForm.LieIndex,∑i:Fin 3,∑j:Fin 3,
    chargedNativeSandwich dual (GaussNativeForm.gaugeDirection i a) (GaussNativeForm.gaugeDirection j a)
      (fun z=>GaussNativeEnergy.gaugeWeight z i j) (GaussNativeEnergy.gaugeWeight_smooth i j))+
  scalarRealMultiply GaussNativePotential.potential GaussNativePotential.potential_smooth

/-- Every original scalar/gauge quadratic term, its Number-three adjoint, and the full native potential return on the same epsilon20 source. -/
theorem actual_epsilon_full_native_action(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    GaussNativeForm.nativeAction (epsilonSection dual e f)=
      epsilonSection dual e (chargedNativeAction dual f):=by
  simp only [GaussNativeForm.nativeAction,GaussNativeForm.scalarKinetic,GaussNativeForm.gaugeKinetic,
    LinearMap.add_apply,LinearMap.smul_apply,LinearMap.sum_apply,sandwich_section,real_section,
    chargedNativeAction,map_add,map_smul,map_sum]

end LowEnergy.NamedColorQtNext
