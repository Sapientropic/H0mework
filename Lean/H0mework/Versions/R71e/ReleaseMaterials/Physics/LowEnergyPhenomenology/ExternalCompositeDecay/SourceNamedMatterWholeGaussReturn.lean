import H0mework.Versions.R71e.ReleaseMaterials.Physics.LowEnergyPhenomenology.ExternalCompositeDecay.SourceNamedMatterNativeDynamics
import H0mework.Versions.AB.Physics.LowEnergy.Quantum.GaussFullHamiltonian
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
noncomputable section
namespace LowEnergy.NamedColorQtNext
open SaturationMonoid SaturationMonoid.PhysicsCore NamedMatterWedgeQt
open GaussHistoryHilbert GaussCoreDifferential GaussCoreHilbert GaussDensityCore GaussScalarTransport
open SourceQuantumScalarChart SourceQuantumConfigurationHilbert SourceQuantumFockGauge SourceQuantumGaugeSliceCoordinates
open scoped BigOperators InnerProductSpace ContDiff

private def fiberSection(q:FockFiber):ScalarTest→ₗ[ℂ]QuantumTest where
  toFun f:=⟨fun z=>f z • q,f.contDiff.smul contDiff_const,f.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left _ _).trans f.tsupport_subset⟩
  map_add' f g:=by apply DFunLike.ext; intro z; exact add_smul _ _ _
  map_smul' c f:=by apply DFunLike.ext; intro z; exact (smul_smul c (f z) q).symm
private theorem fiber_section_value(q:FockFiber)(f:ScalarTest)(z:SourceCoordinateSlice):
    fiberSection q f z=f z • q:=rfl
attribute [local irreducible] fiberSection epsilonFiber20 epsilonSection

private theorem fiber_section_epsilon(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    fiberSection (epsilonFiber20 dual e) f=epsilonSection dual e f:=by
  apply DFunLike.ext
  intro z
  rw [fiber_section_value,epsilon_section_value]

private def ThreeFiber(q:FockFiber):Prop:=∀word:Occupation,word.card≠3→q word=0
private theorem section_component(q:FockFiber)(f:ScalarTest)(word:Occupation):
    component word (fiberSection q f)=q word • f:=by
  apply DFunLike.ext
  intro z
  rw [component_apply,fiber_section_value]
  simp [PiLp.smul_apply,smul_eq_mul,mul_comm]

private theorem three_number(q:FockFiber)(hq:ThreeFiber q):
    SourceQuantumFockGauge.fiberNumber q=(3:ℂ) • q:=by
  apply PiLp.ext
  intro word
  rw [SourceQuantumFockGauge.fiberNumber_apply]
  by_cases hw:word.card=3
  · simp [hw,PiLp.smul_apply,smul_eq_mul]
  · simp [hq word hw,PiLp.smul_apply,smul_eq_mul]

private theorem quantum_three(A:Matrix Mode Mode ℂ)(q:FockFiber)(hq:ThreeFiber q):
    ThreeFiber (GaussQuantumMultiplier.quantized A q):=by
  have h:=congrArg (fun T:FockFiber→L[ℂ]FockFiber=>T q) (GaussQuantumMultiplier.number_commute A).eq
  simp only [mul_apply_eq_comp,three_number q hq,map_smul] at h
  intro word hw
  have he:=congrArg (fun v:FockFiber=>v word) h
  rw [SourceQuantumFockGauge.fiberNumber_apply] at he
  change (word.card:ℂ)*GaussQuantumMultiplier.quantized A q word=
    (3:ℂ)*GaussQuantumMultiplier.quantized A q word at he
  have hn:(word.card:ℂ)-(3:ℂ)≠0:=sub_ne_zero.mpr (by exact_mod_cast hw)
  apply (mul_eq_zero.mp (show ((word.card:ℂ)-3)*GaussQuantumMultiplier.quantized A q word=0 by
    linear_combination he)).resolve_left hn

private theorem section_derivative(q:FockFiber)(v:SourceCoordinateSlice)(f:ScalarTest):
    GaussCoframeCore.derivative v (fiberSection q f)=fiberSection q (GaussDensityCore.derivative v f):=by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  change component word (GaussCoframeCore.derivative v (fiberSection q f)) z=
    component word (fiberSection q (GaussDensityCore.derivative v f)) z
  rw [GaussCoframeCore.component_derivative,section_component,map_smul,section_component]

private theorem section_transpose(q:FockFiber)(hq:ThreeFiber q)(v:SourceCoordinateSlice)(f:ScalarTest):
    GaussCoframeCore.transpose v (fiberSection q f)=fiberSection q (weightedTranspose 3 v f):=by
  apply embed_injective
  rw [GaussCoframeCore.transpose_embed]
  apply PiLp.ext
  intro word
  change scalarEmbed word.card (weightedTranspose word.card v (component word (fiberSection q f)))=
    scalarEmbed word.card (component word (fiberSection q (weightedTranspose 3 v f)))
  rw [section_component,section_component,map_smul,map_smul,map_smul]
  by_cases hw:word.card=3
  · rw [hw]
  · rw [hq word hw,zero_smul,zero_smul]

def scalarCoframeMomentum(i:Fin 6):ScalarEnd:=(-Complex.I) • derivative (GaussCoframeCore.coframeDirection i)
def scalarCoframeAdjoint(i:Fin 6):ScalarEnd:=Complex.I • weightedTranspose 3 (GaussCoframeCore.coframeDirection i)

private theorem section_momentum(q:FockFiber)(i:Fin 6)(f:ScalarTest):
    GaussCoframeCore.momentum i (fiberSection q f)=fiberSection q (scalarCoframeMomentum i f):=by
  rw [GaussCoframeCore.momentum,LinearMap.smul_apply,section_derivative,←map_smul]
  rfl
private theorem section_adjoint(q:FockFiber)(hq:ThreeFiber q)(i:Fin 6)(f:ScalarTest):
    GaussCoframeCore.adjoint i (fiberSection q f)=fiberSection q (scalarCoframeAdjoint i f):=by
  rw [GaussCoframeCore.adjoint,LinearMap.smul_apply,section_transpose q hq,←map_smul]
  rfl
private theorem section_real(q:FockFiber)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:ScalarTest):
    GaussNativeForm.multiply c hc (fiberSection q f)=fiberSection q (scalarRealMultiply c hc f):=by
  apply DFunLike.ext
  intro z
  rw [GaussNativeForm.multiply_apply,fiber_section_value,fiber_section_value]
  exact smul_smul _ _ _

def sourceSpinFiber(a:Fin 7):FockFiber→L[ℂ]FockFiber:=GaussQuantumMultiplier.quantized (GaussCoframeSpin.full a)
private theorem section_spin(a:Fin 7)(q:FockFiber)(f:ScalarTest):
    GaussCoframeSpin.current a (fiberSection q f)=fiberSection (sourceSpinFiber a q) f:=by
  apply DFunLike.ext
  intro z
  change sourceSpinFiber a (fiberSection q f z)=_
  rw [fiber_section_value,map_smul,fiber_section_value]

private theorem section_number(q:FockFiber)(hq:ThreeFiber q)(f:ScalarTest):
    GaussCoframeForm.number (fiberSection q f)=fiberSection q ((3:ℂ) • f):=by
  apply DFunLike.ext
  intro z
  apply PiLp.ext
  intro word
  rw [GaussCoframeForm.number_apply,fiber_section_value,fiber_section_value]
  by_cases hw:word.card=3
  · simp [hw,PiLp.smul_apply,smul_eq_mul,mul_assoc]
  · simp [hq word hw,PiLp.smul_apply,smul_eq_mul]

def scalarCoframeKinetic:ScalarEnd:=∑i:Fin 6,∑j:Fin 6,
  (scalarCoframeAdjoint i).comp
    ((scalarRealMultiply (GaussCoframeKinetic.coefficient i j) (GaussCoframeKinetic.coefficient_smooth i j)).comp
      (scalarCoframeMomentum j))
def scalarMixedProfile(i:Fin 6)(c:SourceCoordinateSlice→ℝ)
    (hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val):ScalarEnd:=
  (1/2:ℂ) • ((scalarRealMultiply c hc).comp (scalarCoframeMomentum i)+
    (scalarCoframeAdjoint i).comp (scalarRealMultiply c hc))

private theorem kinetic_section(q:FockFiber)(hq:ThreeFiber q)(f:ScalarTest):
    GaussCoframeKinetic.kinetic (fiberSection q f)=fiberSection q (scalarCoframeKinetic f):=by
  simp only [GaussCoframeKinetic.kinetic,GaussCoframeKinetic.term,LinearMap.sum_apply,LinearMap.comp_apply,
    section_momentum,section_real,section_adjoint q hq,scalarCoframeKinetic,map_sum]

private theorem mixed_section(q:FockFiber)(hq:ThreeFiber q)(i:Fin 6)(a:Fin 7)
    (c:SourceCoordinateSlice→ℝ)(hc:∀z:physicalChart,ContDiffAt ℝ ∞ c z.val)(f:ScalarTest):
    GaussCoframeForm.mixed i a c hc (fiberSection q f)=
      fiberSection (sourceSpinFiber a q) (scalarMixedProfile i c hc f):=by
  have hs:ThreeFiber (sourceSpinFiber a q):=quantum_three (GaussCoframeSpin.full a) q hq
  simp only [GaussCoframeForm.mixed,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,
    section_momentum,section_real,section_spin,
    section_adjoint (sourceSpinFiber a q) hs,scalarMixedProfile,map_smul,map_add]

private theorem square_section(q:FockFiber)(a:Fin 7)(f:ScalarTest):
    GaussCoframeForm.spinSquare a (fiberSection q f)=
      fiberSection (sourceSpinFiber a (sourceSpinFiber a q))
        ((GaussCoframeForm.spinWeight a:ℂ) •
          scalarRealMultiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth f):=by
  simp only [GaussCoframeForm.spinSquare,LinearMap.smul_apply,LinearMap.comp_apply,
    section_spin,section_real,map_smul]

private theorem number_section(q:FockFiber)(hq:ThreeFiber q)(f:ScalarTest):
    GaussCoframeForm.numberShift (fiberSection q f)=
      fiberSection q ((3:ℂ) • scalarRealMultiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth f):=by
  simp only [GaussCoframeForm.numberShift,LinearMap.smul_apply,LinearMap.add_apply,LinearMap.comp_apply,
    section_real,section_number q hq,map_smul]
  module

def scalarCoframeRemainder:ScalarEnd:=scalarCoframeKinetic+
  (3:ℂ) • scalarRealMultiply GaussCoframeForm.numberCoefficient GaussCoframeForm.numberCoefficient_smooth+
  scalarRealMultiply GaussCoframeForm.volumePotential GaussCoframeForm.volumePotential_smooth

def epsilonCoframeReturn(dual:Bool)(e:Epsilon20)(f:ScalarTest):QuantumTest:=
  epsilonSection dual e (scalarCoframeRemainder f)+
  fiberSection (sourceSpinFiber 5 (epsilonFiber20 dual e))
    (scalarMixedProfile 1 (GaussCoframeForm.currentCoefficient 0) (GaussCoframeForm.currentCoefficient_smooth 0) f)+
  fiberSection (sourceSpinFiber 3 (epsilonFiber20 dual e))
    (scalarMixedProfile 3 (GaussCoframeForm.currentCoefficient 1) (GaussCoframeForm.currentCoefficient_smooth 1) f)+
  fiberSection (sourceSpinFiber 4 (epsilonFiber20 dual e))
    (scalarMixedProfile 3 (fun z=>-GaussCoframeForm.currentCoefficient 0 z)
      (fun z=>(GaussCoframeForm.currentCoefficient_smooth 0 z).neg) f)+
  fiberSection (sourceSpinFiber 3 (epsilonFiber20 dual e))
    (scalarMixedProfile 4 (GaussCoframeForm.currentCoefficient 2) (GaussCoframeForm.currentCoefficient_smooth 2) f)+
  ∑a:Fin 7,fiberSection (sourceSpinFiber a (sourceSpinFiber a (epsilonFiber20 dual e)))
    ((GaussCoframeForm.spinWeight a:ℂ) •
      scalarRealMultiply GaussCoframeForm.inverseVolume GaussCoframeForm.inverseVolume_smooth f)

/-- All36 ordered coframe kinetic terms, four current terms, seven signed spin squares, Number shift, and volume term return from the actual source. -/
theorem actual_epsilon_full_coframe_action(dual:Bool)(e:Epsilon20)(f:ScalarTest):
    GaussCoframeForm.coframeAction (epsilonSection dual e f)=epsilonCoframeReturn dual e f:=by
  have hq:ThreeFiber (epsilonFiber20 dual e):=actual_epsilon_number_three dual e
  rw [←fiber_section_epsilon]
  simp only [GaussCoframeForm.coframeAction,GaussCoframeForm.currentAction,
    LinearMap.add_apply,LinearMap.sum_apply,kinetic_section _ hq,mixed_section _ hq,
    square_section,number_section _ hq,section_real]
  simp only [fiber_section_epsilon,epsilonCoframeReturn,scalarCoframeRemainder,
    LinearMap.add_apply,LinearMap.smul_apply,map_add,map_smul]
  abel

def epsilonMatterFiber(dual:Bool)(e:Epsilon20)(z:SourceCoordinateSlice):FockFiber:=
  ∑i:Fin 3,∑b:Fin 3,GaussQuantumMultiplier.quantized (GaussMatterCore.localMatrix i b z) (epsilonFiber20 dual e)

def epsilonH0Value(dual:Bool)(e:Epsilon20)(f:ScalarTest)(z:SourceCoordinateSlice):FockFiber:=
  chargedNativeAction dual f z • epsilonFiber20 dual e+epsilonCoframeReturn dual e f z+
    f z • epsilonMatterFiber dual e z

/-- The complete original Gauss H0 returns on the same normalized epsilon test, retaining the actual spin×native matter leakage. -/
theorem actual_epsilon_full_H0(dual:Bool)(e:Epsilon20)(f:ScalarTest)(z:SourceCoordinateSlice):
    GaussDiagonalHistory.diagonalAction (epsilonSection dual e f) z=epsilonH0Value dual e f z:=by
  rw [GaussDiagonalHistory.diagonalAction,LinearMap.add_apply,LinearMap.add_apply,
    actual_epsilon_full_native_action,actual_epsilon_full_coframe_action]
  change epsilonSection dual e (chargedNativeAction dual f) z+epsilonCoframeReturn dual e f z+
    GaussMatterCore.matterAction (epsilonSection dual e f) z=_
  rw [epsilon_section_value]
  congr 1
  simp only [GaussMatterCore.matterAction,LinearMap.sum_apply,_root_.sum_apply]
  change (∑i:Fin 3,∑b:Fin 3,GaussQuantumMultiplier.quantized (GaussMatterCore.localMatrix i b z)
    (epsilonSection dual e f z))=f z • epsilonMatterFiber dual e z
  simp only [epsilon_section_value,map_smul,epsilonMatterFiber,Finset.smul_sum]

/-- The actual fullY and its independent sharp source retain every external epsilon channel and literal field-dependent leakage term. -/
theorem actual_epsilon_full_Y(dual sharp:Bool)(e:Epsilon20)(f:ScalarTest)(z:SourceCoordinateSlice):
    (if sharp then GaussFullHamiltonian.sharpAction else GaussFullHamiltonian.fullAction)
      (epsilonSection dual e f) z=
    epsilonH0Value dual e f z+f z •
      ((if sharp then GaussFullHamiltonian.adjointMap else GaussYukawaCoefficient.sourceMap)
        (GaussNativePotential.scalarField z) (epsilonFiber20 dual e)):=by
  cases sharp with
  | false=>
    change GaussDiagonalHistory.diagonalAction (epsilonSection dual e f) z+
      GaussYukawaCoefficient.sourceMap (GaussNativePotential.scalarField z) (epsilonSection dual e f z)=_
    rw [actual_epsilon_full_H0,epsilon_section_value,map_smul]
    rfl
  | true=>
    change GaussDiagonalHistory.diagonalAction (epsilonSection dual e f) z+
      GaussFullHamiltonian.adjointMap (GaussNativePotential.scalarField z) (epsilonSection dual e f z)=_
    rw [actual_epsilon_full_H0,epsilon_section_value,map_smul]
    rfl

end LowEnergy.NamedColorQtNext
