import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
set_option autoImplicit false
namespace LowEnergy.ActualCascadeBlockAlgebra
open scoped Matrix
variable {R:Type*} [Ring R]
theorem residual (A B D J L K E:R) :
    -(!![B,0;J,B])*!![1,L;K,E]-!![1,L;K,E]*!![A,D;0,A]-!![1,0;0,0]=
      !![-B-A-1,-B*L-D-L*A;-J-B*K-K*A,-J*L-B*E-K*D-E*A] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> noncomm_ring

omit [Ring R] in
theorem four_congr {a b c d a' b' c' d':R}
    (ha:a=a') (hb:b=b') (hc:c=c') (hd:d=d') :
    (!![a,b;c,d])=!![a',b';c',d'] := by rw [ha,hb,hc,hd]
end LowEnergy.ActualCascadeBlockAlgebra
