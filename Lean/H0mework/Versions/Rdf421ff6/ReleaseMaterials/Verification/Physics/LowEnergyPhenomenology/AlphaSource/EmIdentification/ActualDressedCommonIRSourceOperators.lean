import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedParameterCoefficientAlgebra
import H0mework.Versions.Rdf421ff6.ReleaseMaterials.Verification.Physics.LowEnergyPhenomenology.AlphaSource.EmIdentification.ActualDressedUniformRayResponse
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace LowEnergy.GaussComposite.ActualDressedUniformMaterialCoefficients
open Polynomial GaussCoreHilbert CanonicalPhysicalSpatial CanonicalGradedSpatialSource PreparationVacuumMixedFieldReturn
open PreparationVacuumJointFieldResponse SourcePropagationAlgebraicResponse SourcePropagationCommonMomentum
open PreparationVacuumPhysicalFeedback PreparationVacuumPropagationPencil PreparationVacuumActionFieldLift
open ActualEMJointCurrentMomentum ActualDressedNoether ActualDressedFullCoulomb
open ActualDressedUniformRayCoefficients ActualDressedPhysicalRayNumerator
open scoped TensorProduct
private theorem constant_affine_eval {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (P : Parameters) (a b : A) :
    coefficientEval v (Algebra.TensorProduct.includeRight a-P • (Algebra.TensorProduct.includeRight b : CoefficientAlgebra A))=
      a-MvPolynomial.eval v P • b := by
  have first:=coefficient_eval_constant (A:=A) v a
  have second:=(coefficient_eval_smul (A:=A) v P (Algebra.TensorProduct.includeRight b)).trans
    (congrArg (fun c : A=>MvPolynomial.eval v P • c) (coefficient_eval_constant (A:=A) v b))
  exact ((coefficientEval v).map_sub _ _).trans (congrArg₂ (fun a b : A=>a-b) first second)
private theorem negative_aeval_eval {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (T : CoefficientAlgebra A) (P : Parameters[X]) :
    coefficientEval v (-(aeval T P))= -(aeval (coefficientEval v T) (P.map (MvPolynomial.eval v))) := by
  have generated:=coefficient_eval_aeval (A:=A) v T P
  exact ((coefficientEval v).map_neg _).trans (congrArg (fun a : A=>-a) generated)
private theorem coefficient_sylvester_eval {A : Type*} [Ring A] [Algebra ℂ A]
    (v : Fin 3→ℂ) (r t : Parameters) (B C X : CoefficientAlgebra A) :
    coefficientEval v ((r • B)*X+X*(t • C))=
      MvPolynomial.eval v r • (coefficientEval v B*coefficientEval v X)+
      MvPolynomial.eval v t • (coefficientEval v X*coefficientEval v C) := by
  have left:=((coefficientEval v).map_mul (r • B) X).trans
    ((congrArg (fun x : A=>x*coefficientEval v X) (coefficient_eval_smul v r B)).trans (Algebra.smul_mul_assoc _ _ _))
  have right:=((coefficientEval v).map_mul X (t • C)).trans
    ((congrArg (fun x : A=>coefficientEval v X*x) (coefficient_eval_smul v t C)).trans (Algebra.mul_smul_comm _ _ _))
  exact ((coefficientEval v).map_add _ _).trans (congrArg₂ (fun a b : A=>a+b) left right)
abbrev Op:=H→L[ℂ]H
abbrev ParameterOp:=CoefficientAlgebra Op
@[instance_reducible] private def coefficientRing {A : Type*} [Ring A] [Algebra ℂ A] :
    Ring (CoefficientAlgebra A):=inferInstance
local instance : Ring ParameterOp:=coefficientRing (A:=Op)
local instance : AddCommGroup ParameterOp:=(inferInstance : Ring ParameterOp).toAddCommGroup
local instance : AddGroup ParameterOp:=(inferInstance : AddCommGroup ParameterOp).toAddGroup
local instance : NormedAlgebra ℝ Op:=NormedAlgebra.restrictScalars ℝ ℂ _
attribute [local irreducible] jointGenerator jointResolvent jointCurrent jointCurrentMomentum
  materialJointNumerator uniformClockPolynomial uniformClockNumerator evolutionGenerator sourceLeft sourceRight
  momentumCompression compression chargeJointPolynomial chargeClockPolynomial dressedKinematicPoint
/-- eps is the external kinematic IR scale, independent of the electron charge unit. -/
def irValues (eps sigma s : ℝ) : Fin 3→ℂ:=fun i=>if i=0 then (eps:ℂ) else if i=1 then (sigma:ℂ) else (s:ℂ)
def constantOp (A : Op) : ParameterOp:=Algebra.TensorProduct.includeRight A
def irCoefficientMap : ℂ[X]→+*Parameters:=eval₂RingHom MvPolynomial.C (MvPolynomial.X 0)
def commonJointPolynomial (event : DressedEvent) (n : PhysicalMomentum) : Parameters[X]:=
  (chargeJointPolynomial event.momentum n event.frame).map irCoefficientMap
def commonClockPolynomial (event : DressedEvent) (n : PhysicalMomentum) : Parameters[X]:=
  (chargeClockPolynomial event n).map irCoefficientMap
private theorem coefficient_map_eval (eps sigma s : ℝ) :
    (MvPolynomial.eval (irValues eps sigma s)).comp irCoefficientMap=evalRingHom (eps:ℂ) := by
  apply Polynomial.ringHom_ext
  · intro c;simp [irCoefficientMap]
  · simp [irCoefficientMap,irValues]
theorem common_joint_polynomial_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) :
    (commonJointPolynomial event n).map (MvPolynomial.eval (irValues eps sigma s))=
      jointPolynomial (event.momentum-(eps^2:ℝ) • n) event.frame := by
  rw [commonJointPolynomial,map_map,coefficient_map_eval,charge_joint_eval]
theorem common_clock_polynomial_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) :
    (commonClockPolynomial event n).map (MvPolynomial.eval (irValues eps sigma s))=
      uniformClockPolynomial (dressedKinematicPoint event ((eps^2:ℝ) • n)) := by
  rw [commonClockPolynomial,map_map,coefficient_map_eval,actual_uniform_clock_charge_coefficients]
def commonLeftGenerator (event : DressedEvent) (n : PhysicalMomentum) : ParameterOp:=
  constantOp (jointGenerator event.momentum event.frame 0 0)-
    ((MvPolynomial.X 0 : Parameters)^2) • constantOp (momentumCompression n event.frame)
theorem common_left_generator_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) :
    coefficientEval (irValues eps sigma s) (commonLeftGenerator event n)=
      jointGenerator (event.momentum-(eps^2:ℝ) • n) event.frame 0 0 := by
  have source:=actual_joint_charge_affine event.momentum n event.frame (eps^2)
  simpa only [commonLeftGenerator,map_sub,coefficient_eval_smul,constantOp,coefficient_eval_constant,
    map_pow,MvPolynomial.eval_X,irValues,ite_true,Complex.ofReal_pow,momentumCompression] using source.symm
attribute [local irreducible] commonLeftGenerator
private theorem affine_move {P E : Type*} [AddCommGroup P] [Module ℝ P]
    [AddCommGroup E] [Module ℝ E] [Module ℂ E] [IsScalarTower ℝ ℂ E]
    (C : E) (L : P→ₗ[ℝ]E) (p n : P) (r : ℝ) :
    C+L (p-r • n)=(C+L p)-(r:ℂ) • ((C+L n)-C) := by
  calc
    _=C+(L p-L (r • n)) := congrArg (fun x : E=>C+x) (L.map_sub p (r • n))
    _=C+(L p-r • L n) := congrArg (fun x : E=>C+(L p-x)) (L.map_smul r n)
    _=C+(L p-(r:ℂ) • L n) := congrArg (fun x : E=>C+(L p-x))
      (RCLike.real_smul_eq_coe_smul (K:=ℂ) (E:=E) r (L n))
    _=(C+L p)-(r:ℂ) • L n := (add_sub_assoc _ _ _).symm
    _=_ := congrArg (fun x : E=>(C+L p)-(r:ℂ) • x) (add_sub_cancel_left C (L n)).symm
/-- Consumes the source's differentiated full-field germ, not the h=0 Hamiltonian identity. -/
theorem actual_moving_current_affine (p n : PhysicalMomentum) (F : GaussUnitaryHistory.Index)
    (z : ℂ) (r : ℝ) (force : Field289) :
    jointCurrent (p-r • n) F z 0 force=jointCurrent p F z 0 force-
      (r:ℂ) • (jointCurrent n F z 0 force-jointCurrent 0 F z 0 force) := by
  let L:PhysicalMomentum→L[ℝ]Op:=(ContinuousLinearMap.apply ℝ Op force).comp (jointCurrentMomentum F z)
  have paid (k : PhysicalMomentum) : jointCurrent k F z 0 force=jointCurrent 0 F z 0 force+L k :=
    congrArg (fun J : Field289→L[ℝ]Op=>J force) (joint_current_affine F z k)
  exact (paid (p-r • n)).trans ((affine_move _ L.toLinearMap p n r).trans
    (congrArg₂ (fun A B : Op=>A-(r:ℂ) • (B-jointCurrent 0 F z 0 force)) (paid p).symm (paid n).symm))
def commonLeftCurrent (event : DressedEvent) (n : PhysicalMomentum) (z : ℂ) (force : Field289) : ParameterOp:=
  constantOp (jointCurrent event.momentum event.frame z 0 force)-
    ((MvPolynomial.X 0 : Parameters)^2) • constantOp (jointCurrent n event.frame z 0 force-jointCurrent 0 event.frame z 0 force)
theorem common_left_current_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ)
    (z : ℂ) (force : Field289) :
    coefficientEval (irValues eps sigma s) (commonLeftCurrent event n z force)=
      jointCurrent (event.momentum-(eps^2:ℝ) • n) event.frame z 0 force := by
  have evaluated:=constant_affine_eval (A:=Op) (irValues eps sigma s) ((MvPolynomial.X 0 : Parameters)^2)
    (jointCurrent event.momentum event.frame z 0 force)
    (jointCurrent n event.frame z 0 force-jointCurrent 0 event.frame z 0 force)
  have scalar : MvPolynomial.eval (irValues eps sigma s) ((MvPolynomial.X 0 : Parameters)^2)=((eps^2:ℝ):ℂ) := by
    simp only [map_pow,MvPolynomial.eval_X,irValues,ite_true,Complex.ofReal_pow]
  exact evaluated.trans ((congrArg (fun r : ℂ=>jointCurrent event.momentum event.frame z 0 force-r •
    (jointCurrent n event.frame z 0 force-jointCurrent 0 event.frame z 0 force)) scalar).trans
      (actual_moving_current_affine event.momentum n event.frame z (eps^2) force).symm)
attribute [local irreducible] commonLeftCurrent
def commonMaterialLeft (event : DressedEvent) (n : PhysicalMomentum) : ParameterOp:=
  -(aeval (commonLeftGenerator event n) ((commonJointPolynomial event n)/ₘ(X-C (MvPolynomial.C event.energy))))
theorem common_material_left_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) :
    coefficientEval (irValues eps sigma s) (commonMaterialLeft event n)=
      materialJointNumerator (event.momentum-(eps^2:ℝ) • n) event.frame event.energy := by
  have evaluated:=negative_aeval_eval (A:=Op) (irValues eps sigma s) (commonLeftGenerator event n)
    ((commonJointPolynomial event n)/ₘ(X-C (MvPolynomial.C event.energy)))
  have polynomial : (((commonJointPolynomial event n)/ₘ(X-C (MvPolynomial.C event.energy))).map
      (MvPolynomial.eval (irValues eps sigma s)))=
      (jointPolynomial (event.momentum-(eps^2:ℝ) • n) event.frame)/ₘ(X-C event.energy) := by
    rw [map_divByMonic _ (monic_X_sub_C _),common_joint_polynomial_eval,Polynomial.map_sub,map_X,map_C,MvPolynomial.eval_C]
  have shifted:=congrArg₂ (fun T : Op=>fun P : ℂ[X]=> -(aeval T P))
    (common_left_generator_eval event n eps sigma s) polynomial
  unfold materialJointNumerator
  exact evaluated.trans shifted
attribute [local irreducible] commonMaterialLeft
def commonEvolution (event : DressedEvent) (n : PhysicalMomentum) : Module.End Parameters ParameterOp:=
  LinearMap.mul Parameters ParameterOp ((MvPolynomial.C Complex.I : Parameters) • commonLeftGenerator event n)+
    (LinearMap.mul Parameters ParameterOp).flip
      ((MvPolynomial.C (-Complex.I) : Parameters) • constantOp (jointGenerator event.momentum event.frame 0 0))
attribute [local irreducible] commonEvolution
private theorem source_evolution_apply (q : PhysicalResponsePoint) (A : Op) :
    evolutionGenerator q A=Complex.I • (jointGenerator (q.p+q.k) q.F 0 0*A)+
      (-Complex.I) • (A*jointGenerator q.p q.F 0 0) := by
  have left : sourceLeft q A=jointGenerator (q.p+q.k) q.F 0 0*A := by unfold sourceLeft;rfl
  have right : sourceRight q A=A*jointGenerator q.p q.F 0 0 := by unfold sourceRight;rfl
  have paid:=congrArg (fun T : SourcePropagationResolvent.TransferOp=>T A) (sourceEvolution_multiplications q)
  simpa only [add_apply,smul_apply,left,right] using paid
theorem common_evolution_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ) (A : ParameterOp) :
    coefficientEval (irValues eps sigma s) (commonEvolution event n A)=
      evolutionGenerator (dressedKinematicPoint event ((eps^2:ℝ) • n)) (coefficientEval (irValues eps sigma s) A) := by
  have realized:=coefficient_sylvester_eval (A:=Op) (irValues eps sigma s)
    (MvPolynomial.C Complex.I) (MvPolynomial.C (-Complex.I)) (commonLeftGenerator event n)
    (constantOp (jointGenerator event.momentum event.frame 0 0)) A
  have actual:=source_evolution_apply (dressedKinematicPoint event ((eps^2:ℝ) • n)) (coefficientEval (irValues eps sigma s) A)
  have aligned : coefficientEval (irValues eps sigma s) (commonEvolution event n A)=
      Complex.I • (jointGenerator (event.momentum-(eps^2:ℝ) • n) event.frame 0 0*coefficientEval (irValues eps sigma s) A)+
      (-Complex.I) • (coefficientEval (irValues eps sigma s) A*jointGenerator event.momentum event.frame 0 0) := by
    unfold commonEvolution
    simpa only [LinearMap.add_apply,LinearMap.mul_apply',LinearMap.flip_apply,MvPolynomial.eval_C,
      common_left_generator_eval,constantOp,coefficient_eval_constant] using realized
  let q:=dressedKinematicPoint event ((eps^2:ℝ) • n)
  have qp : q.p=event.momentum := by unfold q dressedKinematicPoint;rfl
  have qF : q.F=event.frame := by unfold q dressedKinematicPoint;rfl
  have qm : q.p+q.k=event.momentum-(eps^2:ℝ) • n := by unfold q dressedKinematicPoint;rfl
  have left:=congrArg₂ (fun p : PhysicalMomentum=>fun F : GaussUnitaryHistory.Index=>jointGenerator p F 0 0) qm qF
  have right:=congrArg₂ (fun p : PhysicalMomentum=>fun F : GaussUnitaryHistory.Index=>jointGenerator p F 0 0) qp qF
  have returned:=congrArg₂ (fun L R : Op=>Complex.I • (L*coefficientEval (irValues eps sigma s) A)+
    (-Complex.I) • (coefficientEval (irValues eps sigma s) A*R)) left right
  exact aligned.trans (actual.trans returned).symm
def commonClockAction (event : DressedEvent) (n : PhysicalMomentum) (lambda : Parameters) :
    Module.End Parameters ParameterOp:=aeval (commonEvolution event n) ((commonClockPolynomial event n)/ₘ(X-C lambda))
attribute [local irreducible] commonClockAction
private def forget {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    (E→L[ℂ]E)→ₐ[ℂ]Module.End ℂ E where
  toRingHom:=ContinuousLinearMap.toLinearMapRingHom
  commutes':=fun _=>rfl
private theorem polynomial_clm_action {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E→L[ℂ]E) (P : ℂ[X]) (x : E) : aeval T.toLinearMap P x=aeval T P x := by
  have base (S : E→L[ℂ]E) : forget S=S.toLinearMap := rfl
  have closed:=aeval_algHom_apply (forget (E:=E)) T P
  rw [base T,base (aeval T P)] at closed
  exact congrArg (fun L : Module.End ℂ E=>L x) closed
theorem common_clock_action_eval (event : DressedEvent) (n : PhysicalMomentum) (eps sigma s : ℝ)
    (lambda : Parameters) (A : ParameterOp) :
    coefficientEval (irValues eps sigma s) (commonClockAction event n lambda A)=
      uniformClockNumerator (dressedKinematicPoint event ((eps^2:ℝ) • n))
        (MvPolynomial.eval (irValues eps sigma s) lambda) (coefficientEval (irValues eps sigma s) A) := by
  unfold commonClockAction uniformClockNumerator
  have moved:=polynomial_action_natural (MvPolynomial.eval (irValues eps sigma s))
    (coefficientEval (irValues eps sigma s)).toAddMonoidHom
    (coefficient_eval_smul (irValues eps sigma s)) (commonEvolution event n)
    (evolutionGenerator (dressedKinematicPoint event ((eps^2:ℝ) • n))).toLinearMap
    (common_evolution_eval event n eps sigma s) ((commonClockPolynomial event n)/ₘ(X-C lambda)) A
  have polynomial : (((commonClockPolynomial event n)/ₘ(X-C lambda)).map (MvPolynomial.eval (irValues eps sigma s)))=
      (uniformClockPolynomial (dressedKinematicPoint event ((eps^2:ℝ) • n)))/ₘ(X-C (MvPolynomial.eval (irValues eps sigma s) lambda)) := by
    rw [map_divByMonic _ (monic_X_sub_C _),common_clock_polynomial_eval,Polynomial.map_sub,map_X,map_C]
  have mapped:=congrArg (fun P : ℂ[X]=>aeval (evolutionGenerator (dressedKinematicPoint event ((eps^2:ℝ) • n))).toLinearMap P
    (coefficientEval (irValues eps sigma s) A)) polynomial
  exact moved.trans (mapped.trans (polynomial_clm_action _ _ _))

end LowEnergy.GaussComposite.ActualDressedUniformMaterialCoefficients
