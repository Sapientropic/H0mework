import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceEscapeSeedTail
import H0mework.Versions.AD.Physics.LowEnergy.Quantum.SourceBoundaryRadiusAction

/-! The actual Yukawa escape norm consumes one original finite-source current. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
noncomputable section
namespace LowEnergy.SourceEscapeCurrent
open GaussCoreHilbert GaussDiagonalHistory SourceEscapeSeedTail
open GaussUnitaryHistory (Index)
open FullYSourceResolventGraphSplice FullYSourceCutoffVolterra
open SourceRetardedIncrement SourceMinimalGraphParticular SourceBoundaryRadiusAction
open scoped InnerProductSpace

private theorem increment_core (sharp : Bool) (m n : ℕ) (g : diagonal.domain) :
    actualIncrement sharp m n (g : H)∈diagonal.domain := by
  cases sharp
  · exact (incrementCore m n g).property
  · exact diagonal.domain.sub_mem
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem n g)
      (FullYSourceCutoffSharp.cutoff_sharp_core_mem m g)

def sourceCore (F : Index) (z : ℂ) (hz : z.im≠0) (g : diagonal.domain) :
    diagonal.domain := ⟨finiteResolvent F z (g : H),finite_resolvent_mem_core F z hz g⟩

def incrementCommutator (F : Index) (z : ℂ) (hz : z.im≠0)
    (sharp : Bool) (m n : ℕ) (g : diagonal.domain) : H :=
  coreCommutator (actualIncrement sharp m n) (sourceCore F z hz g)
    (increment_core sharp m n (sourceCore F z hz g))

def sourceCurrent (F : Index) (z : ℂ) (hz : z.im≠0)
    (sharp : Bool) (m n : ℕ) (g : diagonal.domain) : ℝ :=
  -(inner ℂ (actualIncrement sharp m n (finiteResolvent F z (g : H)))
    (incrementCommutator F z hz sharp m n g+
      actualIncrement sharp m n (finiteProjectionDefect F z hz g))).im

private theorem symmetric_pair_im_zero (x : diagonal.domain) :
    (inner ℂ (x : H) (diagonal x)).im=0 := by
  have h := diagonal_pair x x
  have hh : starRingEnd ℂ (inner ℂ (x : H) (diagonal x))=
      inner ℂ (x : H) (diagonal x) := (inner_conj_symm _ _).trans h
  have hi := congrArg Complex.im hh
  change -(inner ℂ (x : H) (diagonal x)).im=(inner ℂ (x : H) (diagonal x)).im at hi
  linarith

private theorem shifted_pair_im {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x y : E) (z : ℂ) (h : (inner ℂ x y).im=0) :
    (inner ℂ x (y-z • x)).im = -z.im*‖x‖^2 := by
  rw [inner_sub_right,inner_smul_right,Complex.sub_im,h,Complex.mul_im]
  have hi : (inner ℂ x x).im=0 := inner_self_im (𝕜 := ℂ) x
  have hr : (inner ℂ x x).re=‖x‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) x
  rw [hi,hr]
  ring

/-- No projection defect at A q is introduced: symmetry closes that entire output pair. -/
theorem actual_source_mass (F : Index) (z : ℂ) (hz : z.im≠0)
    (sharp : Bool) (m n : ℕ) (g : diagonal.domain) :
    z.im*‖actualIncrement sharp m n (finiteResolvent F z (g : H))‖^2=
      sourceCurrent F z hz sharp m n g-
        (inner ℂ (actualIncrement sharp m n (finiteResolvent F z (g : H)))
          (actualIncrement sharp m n (g : H))).im := by
  let q := sourceCore F z hz g
  let A := actualIncrement sharp m n
  let aq : diagonal.domain := ⟨A (q : H),increment_core sharp m n q⟩
  have hr := congrArg (fun T : H →L[ℂ] H => T (g : H))
    (resolvent_right _ (GaussGradedCompression.compression_selfAdjoint F) z hz)
  change GaussGradedCompression.compression F (q : H)-z • (q : H)=(g : H) at hr
  have hshift : A (g : H)+incrementCommutator F z hz sharp m n g+
      A (finiteProjectionDefect F z hz g)=diagonal aq-z • (aq : H) := by
    change A (g : H)+(diagonal aq-A (diagonal q))+
      A (diagonal q-GaussGradedCompression.compression F (q : H))=
        diagonal aq-z • (A (q : H))
    rw [←hr,map_sub,map_smul,map_sub]
    abel
  have he := (congrArg (fun h : H => (inner ℂ (aq : H) h).im) hshift).trans
    (shifted_pair_im (aq : H) (diagonal aq) z (symmetric_pair_im_zero aq))
  simp only [inner_add_right,Complex.add_im] at he
  change z.im*‖(aq : H)‖^2=
    -(inner ℂ (aq : H) (incrementCommutator F z hz sharp m n g+
      A (finiteProjectionDefect F z hz g))).im-(inner ℂ (aq : H) (A (g : H))).im
  rw [inner_add_right,Complex.add_im]
  linarith

private theorem support_norm_split (F : Index) (x : H) :
    ‖x‖^2=‖supportProjection F x‖^2+‖escapeProjection F x‖^2 := by
  change ‖x‖^2=‖(supportSpan F).starProjection x‖^2+
    ‖(1-(supportSpan F).starProjection) x‖^2
  rw [←Submodule.starProjection_orthogonal']
  exact Submodule.norm_sq_eq_add_norm_sq_starProjection x (supportSpan F)

/-- The complete A=B d or A=B† d is retained inside the original support projection. -/
theorem actual_escape_balance (F : Index) (z : ℂ) (hz : z.im≠0)
    (sharp : Bool) (m n : ℕ) (g : diagonal.domain) :
    z.im*‖escapeProjection F
      (actualIncrement sharp m n (finiteResolvent F z (g : H)))‖^2=
      sourceCurrent F z hz sharp m n g-
        (inner ℂ (actualIncrement sharp m n (finiteResolvent F z (g : H)))
          (actualIncrement sharp m n (g : H))).im-
      z.im*‖supportProjection F
        (actualIncrement sharp m n (finiteResolvent F z (g : H)))‖^2 := by
  have h := actual_source_mass F z hz sharp m n g
  rw [support_norm_split F,mul_add] at h
  linarith

#print axioms actual_source_mass
#print axioms actual_escape_balance
end LowEnergy.SourceEscapeCurrent
