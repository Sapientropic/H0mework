import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B078
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B079

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1889_pa : Scalar.QComplex := ((999999138825890486287881166407 : Int)/10^30,(-1312382367073932207871048577 : Int)/10^30)
theorem v1889_pa_checked : Scalar.distance (sourceCoefficient 21 84 1 0) v1889_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1889_pb : Scalar.QComplex := ((-566263396857975937115290 : Int)/10^30,(-431477078185019034701893641 : Int)/10^30)
theorem v1889_pb_checked : Scalar.distance (sourceCoefficient 21 84 1 1) v1889_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1889_pg : Scalar.QComplex := ((-93086342048914118832010 : Int)/10^30,(122164979125724732200 : Int)/10^30)
theorem v1889_pg_checked : Scalar.distance (sourceCoefficient 21 84 1 2) v1889_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1889_mb : Scalar.QComplex := ((-938608471479690844643940 : Int)/10^30,(-431476428866575418009065746 : Int)/10^30)
theorem v1889_mb_checked : Scalar.distance (sourceCoefficient 21 84 3 1) v1889_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1889_mg : Scalar.QComplex := ((-93086201965739838936726 : Int)/10^30,(202494254373117968628 : Int)/10^30)
theorem v1889_mg_checked : Scalar.distance (sourceCoefficient 21 84 3 2) v1889_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1889_upper : Scalar.QComplex := ((999995384391734184358794144202 : Int)/10^30,(-3038288206834832011546149362 : Int)/10^30)
theorem v1889_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 84 5) 1) 14) v1889_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1889 : Material (21 : Basis) (84 : Basis) where
  plus := ![v1889_pa,v1889_pb,v1889_pg]
  minus := ![(Primitive.Addresses.material1889 1).one,v1889_mb,v1889_mg]
  upper := v1889_upper
  lower := (Primitive.Addresses.material1889 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1889_pa_checked.trans (by decide +kernel)
    · exact v1889_pb_checked.trans (by decide +kernel)
    · exact v1889_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 84 Primitive.Addresses.material1889
    · exact v1889_mb_checked.trans (by decide +kernel)
    · exact v1889_mg_checked.trans (by decide +kernel)
  upper_error := v1889_upper_checked
  lower_error := reuse_lower_error 21 84 Primitive.Addresses.material1889

def v1890_pa : Scalar.QComplex := ((999999031948129882082647591410 : Int)/10^30,(-1391439112254435467513045838 : Int)/10^30)
theorem v1890_pa_checked : Scalar.distance (sourceCoefficient 21 85 1 0) v1890_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1890_pb : Scalar.QComplex := ((-600374583282708133626004 : Int)/10^30,(-431477020303269265980700175 : Int)/10^30)
theorem v1890_pb_checked : Scalar.distance (sourceCoefficient 21 85 1 1) v1890_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1890_pg : Scalar.QComplex := ((-93086330830810734312674 : Int)/10^30,(129524086920280542989 : Int)/10^30)
theorem v1890_pg_checked : Scalar.distance (sourceCoefficient 21 85 1 2) v1890_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1890_mb : Scalar.QComplex := ((-972719595253926223823766 : Int)/10^30,(-431476341548429627570784306 : Int)/10^30)
theorem v1890_mb_checked : Scalar.distance (sourceCoefficient 21 85 3 1) v1890_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1890_mg : Scalar.QComplex := ((-93086184397062046639673 : Int)/10^30,(209853349746823643443 : Int)/10^30)
theorem v1890_mg_checked : Scalar.distance (sourceCoefficient 21 85 3 2) v1890_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1890_upper : Scalar.QComplex := ((999995141069362552373016020265 : Int)/10^30,(-3117344649808281054313325994 : Int)/10^30)
theorem v1890_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 85 5) 1) 14) v1890_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1890 : Material (21 : Basis) (85 : Basis) where
  plus := ![v1890_pa,v1890_pb,v1890_pg]
  minus := ![(Primitive.Addresses.material1890 1).one,v1890_mb,v1890_mg]
  upper := v1890_upper
  lower := (Primitive.Addresses.material1890 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1890_pa_checked.trans (by decide +kernel)
    · exact v1890_pb_checked.trans (by decide +kernel)
    · exact v1890_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 85 Primitive.Addresses.material1890
    · exact v1890_mb_checked.trans (by decide +kernel)
    · exact v1890_mg_checked.trans (by decide +kernel)
  upper_error := v1890_upper_checked
  lower_error := reuse_lower_error 21 85 Primitive.Addresses.material1890

def v1891_pa : Scalar.QComplex := ((999999011548129824103017597781 : Int)/10^30,(-1406023742087840531845165471 : Int)/10^30)
theorem v1891_pa_checked : Scalar.distance (sourceCoefficient 21 86 1 0) v1891_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1891_pb : Scalar.QComplex := ((-606667518807190138767591 : Int)/10^30,(-431477009232213540288442875 : Int)/10^30)
theorem v1891_pb_checked : Scalar.distance (sourceCoefficient 21 86 1 1) v1891_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1891_pg : Scalar.QComplex := ((-93086328687101163969315 : Int)/10^30,(130881717568135180373 : Int)/10^30)
theorem v1891_pg_checked : Scalar.distance (sourceCoefficient 21 86 1 2) v1891_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1891_mb : Scalar.QComplex := ((-979012518881438262407193 : Int)/10^30,(-431476325046858089805430900 : Int)/10^30)
theorem v1891_mb_checked : Scalar.distance (sourceCoefficient 21 86 3 1) v1891_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1891_mg : Scalar.QComplex := ((-93086181081779170813362 : Int)/10^30,(211210978039245533733 : Int)/10^30)
theorem v1891_mg_checked : Scalar.distance (sourceCoefficient 21 86 3 2) v1891_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1891_upper : Scalar.QComplex := ((999995095497644892622918619973 : Int)/10^30,(-3131929222711043786232495761 : Int)/10^30)
theorem v1891_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 86 5) 1) 14) v1891_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1891 : Material (21 : Basis) (86 : Basis) where
  plus := ![v1891_pa,v1891_pb,v1891_pg]
  minus := ![(Primitive.Addresses.material1891 1).one,v1891_mb,v1891_mg]
  upper := v1891_upper
  lower := (Primitive.Addresses.material1891 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1891_pa_checked.trans (by decide +kernel)
    · exact v1891_pb_checked.trans (by decide +kernel)
    · exact v1891_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 86 Primitive.Addresses.material1891
    · exact v1891_mb_checked.trans (by decide +kernel)
    · exact v1891_mg_checked.trans (by decide +kernel)
  upper_error := v1891_upper_checked
  lower_error := reuse_lower_error 21 86 Primitive.Addresses.material1891

def v1892_pa : Scalar.QComplex := ((999999010189786997514344479248 : Int)/10^30,(-1406989497572996650339300685 : Int)/10^30)
theorem v1892_pa_checked : Scalar.distance (sourceCoefficient 21 87 1 0) v1892_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1892_pb : Scalar.QComplex := ((-607084220294556403107152 : Int)/10^30,(-431477008494797685286781165 : Int)/10^30)
theorem v1892_pb_checked : Scalar.distance (sourceCoefficient 21 87 1 1) v1892_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1892_pg : Scalar.QComplex := ((-93086328544334926355912 : Int)/10^30,(130971616266552088757 : Int)/10^30)
theorem v1892_pg_checked : Scalar.distance (sourceCoefficient 21 87 1 2) v1892_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1892_mb : Scalar.QComplex := ((-979429219577290847912307 : Int)/10^30,(-431476323949847893318614658 : Int)/10^30)
theorem v1892_mb_checked : Scalar.distance (sourceCoefficient 21 87 3 1) v1892_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1892_mg : Scalar.QComplex := ((-93086180861434458511636 : Int)/10^30,(211300876580988215016 : Int)/10^30)
theorem v1892_mg_checked : Scalar.distance (sourceCoefficient 21 87 3 2) v1892_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1892_upper : Scalar.QComplex := ((999995092472497734400083901817 : Int)/10^30,(-3132894974413444064401573063 : Int)/10^30)
theorem v1892_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 87 5) 1) 14) v1892_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1892 : Material (21 : Basis) (87 : Basis) where
  plus := ![v1892_pa,v1892_pb,v1892_pg]
  minus := ![(Primitive.Addresses.material1892 1).one,v1892_mb,v1892_mg]
  upper := v1892_upper
  lower := (Primitive.Addresses.material1892 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1892_pa_checked.trans (by decide +kernel)
    · exact v1892_pb_checked.trans (by decide +kernel)
    · exact v1892_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 87 Primitive.Addresses.material1892
    · exact v1892_mb_checked.trans (by decide +kernel)
    · exact v1892_mg_checked.trans (by decide +kernel)
  upper_error := v1892_upper_checked
  lower_error := reuse_lower_error 21 87 Primitive.Addresses.material1892

def v1893_pa : Scalar.QComplex := ((999998993575018417806007822635 : Int)/10^30,(-1418749079391117854069190159 : Int)/10^30)
theorem v1893_pa_checked : Scalar.distance (sourceCoefficient 21 88 1 0) v1893_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1893_pb : Scalar.QComplex := ((-612158211871456264147830 : Int)/10^30,(-431476999472561982128152170 : Int)/10^30)
theorem v1893_pb_checked : Scalar.distance (sourceCoefficient 21 88 1 1) v1893_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1893_pg : Scalar.QComplex := ((-93086326797807155822637 : Int)/10^30,(132066273363086382997 : Int)/10^30)
theorem v1893_pg_checked : Scalar.distance (sourceCoefficient 21 88 1 2) v1893_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1893_mb : Scalar.QComplex := ((-984503201479128686588248 : Int)/10^30,(-431476310548989342783504729 : Int)/10^30)
theorem v1893_mb_checked : Scalar.distance (sourceCoefficient 21 88 3 1) v1893_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1893_mg : Scalar.QComplex := ((-93086178170267565506845 : Int)/10^30,(212395531762756838635 : Int)/10^30)
theorem v1893_mg_checked : Scalar.distance (sourceCoefficient 21 88 3 2) v1893_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1893_upper : Scalar.QComplex := ((999995055561782503289633455623 : Int)/10^30,(-3144654510041466239011500759 : Int)/10^30)
theorem v1893_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 88 5) 1) 14) v1893_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1893 : Material (21 : Basis) (88 : Basis) where
  plus := ![v1893_pa,v1893_pb,v1893_pg]
  minus := ![(Primitive.Addresses.material1893 1).one,v1893_mb,v1893_mg]
  upper := v1893_upper
  lower := (Primitive.Addresses.material1893 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1893_pa_checked.trans (by decide +kernel)
    · exact v1893_pb_checked.trans (by decide +kernel)
    · exact v1893_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 88 Primitive.Addresses.material1893
    · exact v1893_mb_checked.trans (by decide +kernel)
    · exact v1893_mg_checked.trans (by decide +kernel)
  upper_error := v1893_upper_checked
  lower_error := reuse_lower_error 21 88 Primitive.Addresses.material1893

def v1894_pa : Scalar.QComplex := ((999998970618641431767425746561 : Int)/10^30,(-1434838547541319639997672841 : Int)/10^30)
theorem v1894_pa_checked : Scalar.distance (sourceCoefficient 21 89 1 0) v1894_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1894_pb : Scalar.QComplex := ((-619100450614247943646723 : Int)/10^30,(-431476986999442546254215913 : Int)/10^30)
theorem v1894_pb_checked : Scalar.distance (sourceCoefficient 21 89 1 1) v1894_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1894_pg : Scalar.QComplex := ((-93086324383875832573836 : Int)/10^30,(133563983963195793263 : Int)/10^30)
theorem v1894_pg_checked : Scalar.distance (sourceCoefficient 21 89 1 2) v1894_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1894_mb : Scalar.QComplex := ((-991445426873267301447861 : Int)/10^30,(-431476292085035183019001927 : Int)/10^30)
theorem v1894_mb_checked : Scalar.distance (sourceCoefficient 21 89 3 1) v1894_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1894_mg : Scalar.QComplex := ((-93086174463880347561981 : Int)/10^30,(213893239722086131192 : Int)/10^30)
theorem v1894_mg_checked : Scalar.distance (sourceCoefficient 21 89 3 2) v1894_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1894_upper : Scalar.QComplex := ((999995004836477305978264468208 : Int)/10^30,(-3160743914607671125258033539 : Int)/10^30)
theorem v1894_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 89 5) 1) 14) v1894_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1894 : Material (21 : Basis) (89 : Basis) where
  plus := ![v1894_pa,v1894_pb,v1894_pg]
  minus := ![(Primitive.Addresses.material1894 1).one,v1894_mb,v1894_mg]
  upper := v1894_upper
  lower := (Primitive.Addresses.material1894 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1894_pa_checked.trans (by decide +kernel)
    · exact v1894_pb_checked.trans (by decide +kernel)
    · exact v1894_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 89 Primitive.Addresses.material1894
    · exact v1894_mb_checked.trans (by decide +kernel)
    · exact v1894_mg_checked.trans (by decide +kernel)
  upper_error := v1894_upper_checked
  lower_error := reuse_lower_error 21 89 Primitive.Addresses.material1894

def v1895_pa : Scalar.QComplex := ((999998932678353929532261710012 : Int)/10^30,(-1461041461754401857606850024 : Int)/10^30)
theorem v1895_pa_checked : Scalar.distance (sourceCoefficient 21 90 1 0) v1895_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1895_pb : Scalar.QComplex := ((-630406410500975227063379 : Int)/10^30,(-431476966367253867305190745 : Int)/10^30)
theorem v1895_pb_checked : Scalar.distance (sourceCoefficient 21 90 1 1) v1895_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1895_pg : Scalar.QComplex := ((-93086320392431351241357 : Int)/10^30,(136003118774569088972 : Int)/10^30)
theorem v1895_pg_checked : Scalar.distance (sourceCoefficient 21 90 1 2) v1895_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1895_mb : Scalar.QComplex := ((-1002751364745619420493345 : Int)/10^30,(-431476261696320005661962803 : Int)/10^30)
theorem v1895_mb_checked : Scalar.distance (sourceCoefficient 21 90 3 1) v1895_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1895_mg : Scalar.QComplex := ((-93086168367573864765458 : Int)/10^30,(216332370180821243256 : Int)/10^30)
theorem v1895_mg_checked : Scalar.distance (sourceCoefficient 21 90 3 2) v1895_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1895_upper : Scalar.QComplex := ((999994921672393489373096205807 : Int)/10^30,(-3186946724313096320140699913 : Int)/10^30)
theorem v1895_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 90 5) 1) 14) v1895_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1895 : Material (21 : Basis) (90 : Basis) where
  plus := ![v1895_pa,v1895_pb,v1895_pg]
  minus := ![(Primitive.Addresses.material1895 1).one,v1895_mb,v1895_mg]
  upper := v1895_upper
  lower := (Primitive.Addresses.material1895 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1895_pa_checked.trans (by decide +kernel)
    · exact v1895_pb_checked.trans (by decide +kernel)
    · exact v1895_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 90 Primitive.Addresses.material1895
    · exact v1895_mb_checked.trans (by decide +kernel)
    · exact v1895_mg_checked.trans (by decide +kernel)
  upper_error := v1895_upper_checked
  lower_error := reuse_lower_error 21 90 Primitive.Addresses.material1895

def v1896_pa : Scalar.QComplex := ((999998911002872705058567478841 : Int)/10^30,(-1475802516827756195437419563 : Int)/10^30)
theorem v1896_pa_checked : Scalar.distance (sourceCoefficient 21 91 1 0) v1896_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1896_pb : Scalar.QComplex := ((-636775468954910971279245 : Int)/10^30,(-431476954570456109154560578 : Int)/10^30)
theorem v1896_pb_checked : Scalar.distance (sourceCoefficient 21 91 1 1) v1896_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1896_pg : Scalar.QComplex := ((-93086318111071437967180 : Int)/10^30,(137377172153894203628 : Int)/10^30)
theorem v1896_pg_checked : Scalar.distance (sourceCoefficient 21 91 1 2) v1896_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1896_mb : Scalar.QComplex := ((-1009120410647958464721880 : Int)/10^30,(-431476244403316045996059011 : Int)/10^30)
theorem v1896_mb_checked : Scalar.distance (sourceCoefficient 21 91 3 1) v1896_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1896_mg : Scalar.QComplex := ((-93086164900468619655189 : Int)/10^30,(217706421079812630928 : Int)/10^30)
theorem v1896_mg_checked : Scalar.distance (sourceCoefficient 21 91 3 2) v1896_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1896_upper : Scalar.QComplex := ((999994874520702603828600109686 : Int)/10^30,(-3201707719991678872397155067 : Int)/10^30)
theorem v1896_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 91 5) 1) 14) v1896_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1896 : Material (21 : Basis) (91 : Basis) where
  plus := ![v1896_pa,v1896_pb,v1896_pg]
  minus := ![(Primitive.Addresses.material1896 1).one,v1896_mb,v1896_mg]
  upper := v1896_upper
  lower := (Primitive.Addresses.material1896 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1896_pa_checked.trans (by decide +kernel)
    · exact v1896_pb_checked.trans (by decide +kernel)
    · exact v1896_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 91 Primitive.Addresses.material1896
    · exact v1896_mb_checked.trans (by decide +kernel)
    · exact v1896_mg_checked.trans (by decide +kernel)
  upper_error := v1896_upper_checked
  lower_error := reuse_lower_error 21 91 Primitive.Addresses.material1896

def v1897_pa : Scalar.QComplex := ((999998863331377303368905014717 : Int)/10^30,(-1507758585907473573128671324 : Int)/10^30)
theorem v1897_pa_checked : Scalar.distance (sourceCoefficient 21 92 1 0) v1897_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1897_pb : Scalar.QComplex := ((-650563783196460203250078 : Int)/10^30,(-431476928602244948184910754 : Int)/10^30)
theorem v1897_pb_checked : Scalar.distance (sourceCoefficient 21 92 1 1) v1897_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1897_pg : Scalar.QComplex := ((-93086313091111784683621 : Int)/10^30,(140351847327136043965 : Int)/10^30)
theorem v1897_pg_checked : Scalar.distance (sourceCoefficient 21 92 1 2) v1897_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1897_mb : Scalar.QComplex := ((-1022908697346091480370298 : Int)/10^30,(-431476206536420366341981598 : Int)/10^30)
theorem v1897_mb_checked : Scalar.distance (sourceCoefficient 21 92 3 1) v1897_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1897_mg : Scalar.QComplex := ((-93086157313500135420764 : Int)/10^30,(220681090813447864702 : Int)/10^30)
theorem v1897_mg_checked : Scalar.distance (sourceCoefficient 21 92 3 2) v1897_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1897_upper : Scalar.QComplex := ((999994771696002003580174560527 : Int)/10^30,(-3233663659199908840378791470 : Int)/10^30)
theorem v1897_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 92 5) 1) 14) v1897_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1897 : Material (21 : Basis) (92 : Basis) where
  plus := ![v1897_pa,v1897_pb,v1897_pg]
  minus := ![(Primitive.Addresses.material1897 1).one,v1897_mb,v1897_mg]
  upper := v1897_upper
  lower := (Primitive.Addresses.material1897 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1897_pa_checked.trans (by decide +kernel)
    · exact v1897_pb_checked.trans (by decide +kernel)
    · exact v1897_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 92 Primitive.Addresses.material1897
    · exact v1897_mb_checked.trans (by decide +kernel)
    · exact v1897_mg_checked.trans (by decide +kernel)
  upper_error := v1897_upper_checked
  lower_error := reuse_lower_error 21 92 Primitive.Addresses.material1897

def v1898_pa : Scalar.QComplex := ((999998805429535456759259841522 : Int)/10^30,(-1545684153405179580080356307 : Int)/10^30)
theorem v1898_pa_checked : Scalar.distance (sourceCoefficient 21 93 1 0) v1898_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1898_pb : Scalar.QComplex := ((-666927798977618833073619 : Int)/10^30,(-431476897020721777192976923 : Int)/10^30)
theorem v1898_pb_checked : Scalar.distance (sourceCoefficient 21 93 1 1) v1898_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1898_pg : Scalar.QComplex := ((-93086306989494395236813 : Int)/10^30,(143882201490099568510 : Int)/10^30)
theorem v1898_pg_checked : Scalar.distance (sourceCoefficient 21 93 1 2) v1898_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1898_mb : Scalar.QComplex := ((-1039272679780747044838025 : Int)/10^30,(-431476160833500343366337379 : Int)/10^30)
theorem v1898_mb_checked : Scalar.distance (sourceCoefficient 21 93 3 1) v1898_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1898_mg : Scalar.QComplex := ((-93086148165348376496541 : Int)/10^30,(224211438396478188772 : Int)/10^30)
theorem v1898_mg_checked : Scalar.distance (sourceCoefficient 21 93 3 2) v1898_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1898_upper : Scalar.QComplex := ((999994648338157474528814899181 : Int)/10^30,(-3271589070278610896417206233 : Int)/10^30)
theorem v1898_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 93 5) 1) 14) v1898_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1898 : Material (21 : Basis) (93 : Basis) where
  plus := ![v1898_pa,v1898_pb,v1898_pg]
  minus := ![(Primitive.Addresses.material1898 1).one,v1898_mb,v1898_mg]
  upper := v1898_upper
  lower := (Primitive.Addresses.material1898 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1898_pa_checked.trans (by decide +kernel)
    · exact v1898_pb_checked.trans (by decide +kernel)
    · exact v1898_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 93 Primitive.Addresses.material1898
    · exact v1898_mb_checked.trans (by decide +kernel)
    · exact v1898_mg_checked.trans (by decide +kernel)
  upper_error := v1898_upper_checked
  lower_error := reuse_lower_error 21 93 Primitive.Addresses.material1898

def v1899_pa : Scalar.QComplex := ((999998735181660883630334314556 : Int)/10^30,(-1590482655820964419949933176 : Int)/10^30)
theorem v1899_pa_checked : Scalar.distance (sourceCoefficient 21 94 1 0) v1899_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1899_pb : Scalar.QComplex := ((-686257328061676885498975 : Int)/10^30,(-431476858649927151269583835 : Int)/10^30)
theorem v1899_pb_checked : Scalar.distance (sourceCoefficient 21 94 1 1) v1899_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1899_pg : Scalar.QComplex := ((-93086299580898403378153 : Int)/10^30,(148052332237278182490 : Int)/10^30)
theorem v1899_pg_checked : Scalar.distance (sourceCoefficient 21 94 1 2) v1899_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1899_mb : Scalar.QComplex := ((-1058602168555270410414308 : Int)/10^30,(-431476105782206974774196866 : Int)/10^30)
theorem v1899_mb_checked : Scalar.distance (sourceCoefficient 21 94 3 1) v1899_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1899_mg : Scalar.QComplex := ((-93086137158120124098420 : Int)/10^30,(228381561197641870991 : Int)/10^30)
theorem v1899_mg_checked : Scalar.distance (sourceCoefficient 21 94 3 2) v1899_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1899_upper : Scalar.QComplex := ((999994500772236446104781121649 : Int)/10^30,(-3316387384730830113911458637 : Int)/10^30)
theorem v1899_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 94 5) 1) 14) v1899_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1899 : Material (21 : Basis) (94 : Basis) where
  plus := ![v1899_pa,v1899_pb,v1899_pg]
  minus := ![(Primitive.Addresses.material1899 1).one,v1899_mb,v1899_mg]
  upper := v1899_upper
  lower := (Primitive.Addresses.material1899 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1899_pa_checked.trans (by decide +kernel)
    · exact v1899_pb_checked.trans (by decide +kernel)
    · exact v1899_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 94 Primitive.Addresses.material1899
    · exact v1899_mb_checked.trans (by decide +kernel)
    · exact v1899_mg_checked.trans (by decide +kernel)
  upper_error := v1899_upper_checked
  lower_error := reuse_lower_error 21 94 Primitive.Addresses.material1899

def v1900_pa : Scalar.QComplex := ((999998663784173852066818433835 : Int)/10^30,(-1634756821922799719909282351 : Int)/10^30)
theorem v1900_pa_checked : Scalar.distance (sourceCoefficient 21 95 1 0) v1900_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1900_pb : Scalar.QComplex := ((-705360616846611960924664 : Int)/10^30,(-431476819593845818089881219 : Int)/10^30)
theorem v1900_pb_checked : Scalar.distance (sourceCoefficient 21 95 1 1) v1900_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1900_pg : Scalar.QComplex := ((-93086292044874291674042 : Int)/10^30,(152173654284701468610 : Int)/10^30)
theorem v1900_pg_checked : Scalar.distance (sourceCoefficient 21 95 1 2) v1900_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1900_mb : Scalar.QComplex := ((-1077705416523538837852237 : Int)/10^30,(-431476050240862342747615194 : Int)/10^30)
theorem v1900_mb_checked : Scalar.distance (sourceCoefficient 21 95 3 1) v1900_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1900_mg : Scalar.QComplex := ((-93086126065583508928776 : Int)/10^30,(232502875207259206659 : Int)/10^30)
theorem v1900_mg_checked : Scalar.distance (sourceCoefficient 21 95 3 2) v1900_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1900_upper : Scalar.QComplex := ((999994352961661581916951530212 : Int)/10^30,(-3360661361665910327022665014 : Int)/10^30)
theorem v1900_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 95 5) 1) 14) v1900_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1900 : Material (21 : Basis) (95 : Basis) where
  plus := ![v1900_pa,v1900_pb,v1900_pg]
  minus := ![(Primitive.Addresses.material1900 1).one,v1900_mb,v1900_mg]
  upper := v1900_upper
  lower := (Primitive.Addresses.material1900 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1900_pa_checked.trans (by decide +kernel)
    · exact v1900_pb_checked.trans (by decide +kernel)
    · exact v1900_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 95 Primitive.Addresses.material1900
    · exact v1900_mb_checked.trans (by decide +kernel)
    · exact v1900_mg_checked.trans (by decide +kernel)
  upper_error := v1900_upper_checked
  lower_error := reuse_lower_error 21 95 Primitive.Addresses.material1900

def v1901_pa : Scalar.QComplex := ((999998628796466194792608792014 : Int)/10^30,(-1656020889787107625943692278 : Int)/10^30)
theorem v1901_pa_checked : Scalar.distance (sourceCoefficient 21 96 1 0) v1901_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1901_pb : Scalar.QComplex := ((-714535574752655931394518 : Int)/10^30,(-431476800435053039344579735 : Int)/10^30)
theorem v1901_pb_checked : Scalar.distance (sourceCoefficient 21 96 1 1) v1901_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1901_pg : Scalar.QComplex := ((-93086288349786672358786 : Int)/10^30,(154153049435199127945 : Int)/10^30)
theorem v1901_pg_checked : Scalar.distance (sourceCoefficient 21 96 1 2) v1901_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1901_mb : Scalar.QComplex := ((-1086880354480151375548918 : Int)/10^30,(-431476023164501249544982725 : Int)/10^30)
theorem v1901_mb_checked : Scalar.distance (sourceCoefficient 21 96 3 1) v1901_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1901_mg : Scalar.QComplex := ((-93086120662368399232260 : Int)/10^30,(234482266432043393735 : Int)/10^30)
theorem v1901_mg_checked : Scalar.distance (sourceCoefficient 21 96 3 2) v1901_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1901_upper : Scalar.QComplex := ((999994281274153962095557867592 : Int)/10^30,(-3381925337474277645635370629 : Int)/10^30)
theorem v1901_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 96 5) 1) 14) v1901_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1901 : Material (21 : Basis) (96 : Basis) where
  plus := ![v1901_pa,v1901_pb,v1901_pg]
  minus := ![(Primitive.Addresses.material1901 1).one,v1901_mb,v1901_mg]
  upper := v1901_upper
  lower := (Primitive.Addresses.material1901 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1901_pa_checked.trans (by decide +kernel)
    · exact v1901_pb_checked.trans (by decide +kernel)
    · exact v1901_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 96 Primitive.Addresses.material1901
    · exact v1901_mb_checked.trans (by decide +kernel)
    · exact v1901_mg_checked.trans (by decide +kernel)
  upper_error := v1901_upper_checked
  lower_error := reuse_lower_error 21 96 Primitive.Addresses.material1901

def v1902_pa : Scalar.QComplex := ((999998504961944382224031482502 : Int)/10^30,(-1729183008272046429796052133 : Int)/10^30)
theorem v1902_pa_checked : Scalar.distance (sourceCoefficient 21 97 1 0) v1902_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1902_pb : Scalar.QComplex := ((-746103349807164317698104 : Int)/10^30,(-431476732529216032789734026 : Int)/10^30)
theorem v1902_pb_checked : Scalar.distance (sourceCoefficient 21 97 1 1) v1902_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1902_pg : Scalar.QComplex := ((-93086275261168927395170 : Int)/10^30,(160963446131425390180 : Int)/10^30)
theorem v1902_pg_checked : Scalar.distance (sourceCoefficient 21 97 1 2) v1902_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1902_mb : Scalar.QComplex := ((-1118448059180855419177381 : Int)/10^30,(-431475928017121415206217280 : Int)/10^30)
theorem v1902_mb_checked : Scalar.distance (sourceCoefficient 21 97 3 1) v1902_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1902_mg : Scalar.QComplex := ((-93086101696689907796832 : Int)/10^30,(241292649297560091017 : Int)/10^30)
theorem v1902_mg_checked : Scalar.distance (sourceCoefficient 21 97 3 2) v1902_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1902_upper : Scalar.QComplex := ((999994031168637297038091272708 : Int)/10^30,(-3455087133265684723888955764 : Int)/10^30)
theorem v1902_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 21 97 5) 1) 14) v1902_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1902 : Material (21 : Basis) (97 : Basis) where
  plus := ![v1902_pa,v1902_pb,v1902_pg]
  minus := ![(Primitive.Addresses.material1902 1).one,v1902_mb,v1902_mg]
  upper := v1902_upper
  lower := (Primitive.Addresses.material1902 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1902_pa_checked.trans (by decide +kernel)
    · exact v1902_pb_checked.trans (by decide +kernel)
    · exact v1902_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 21 97 Primitive.Addresses.material1902
    · exact v1902_mb_checked.trans (by decide +kernel)
    · exact v1902_mg_checked.trans (by decide +kernel)
  upper_error := v1902_upper_checked
  lower_error := reuse_lower_error 21 97 Primitive.Addresses.material1902

def v1903_pa : Scalar.QComplex := ((999999945490458030825235633706 : Int)/10^30,(-330180376411226721230482359 : Int)/10^30)
theorem v1903_pa_checked : Scalar.distance (sourceCoefficient 22 23 1 0) v1903_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1903_pb : Scalar.QComplex := ((-142465410294455176413173 : Int)/10^30,(-431477497473368430112754169 : Int)/10^30)
theorem v1903_pb_checked : Scalar.distance (sourceCoefficient 22 23 1 1) v1903_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1903_pg : Scalar.QComplex := ((-93086424822053033206154 : Int)/10^30,(30735312461888633444 : Int)/10^30)
theorem v1903_pg_checked : Scalar.distance (sourceCoefficient 22 23 1 2) v1903_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1903_mb : Scalar.QComplex := ((-514811004542490488342644 : Int)/10^30,(-431477213873343944757033960 : Int)/10^30)
theorem v1903_mb_checked : Scalar.distance (sourceCoefficient 22 23 3 1) v1903_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1903_mg : Scalar.QComplex := ((-93086363638532424653728 : Int)/10^30,(111064693182216230325 : Int)/10^30)
theorem v1903_mg_checked : Scalar.distance (sourceCoefficient 22 23 3 2) v1903_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1903_upper : Scalar.QComplex := ((999997886246631512064489487968 : Int)/10^30,(-2056089071276477610306198466 : Int)/10^30)
theorem v1903_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 23 5) 1) 14) v1903_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1903 : Material (22 : Basis) (23 : Basis) where
  plus := ![v1903_pa,v1903_pb,v1903_pg]
  minus := ![(Primitive.Addresses.material1903 1).one,v1903_mb,v1903_mg]
  upper := v1903_upper
  lower := (Primitive.Addresses.material1903 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1903_pa_checked.trans (by decide +kernel)
    · exact v1903_pb_checked.trans (by decide +kernel)
    · exact v1903_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 23 Primitive.Addresses.material1903
    · exact v1903_mb_checked.trans (by decide +kernel)
    · exact v1903_mg_checked.trans (by decide +kernel)
  upper_error := v1903_upper_checked
  lower_error := reuse_lower_error 22 23 Primitive.Addresses.material1903

def v1904_pa : Scalar.QComplex := ((999999927371350203169625969861 : Int)/10^30,(-381126349546629977885425180 : Int)/10^30)
theorem v1904_pa_checked : Scalar.distance (sourceCoefficient 22 24 1 0) v1904_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1904_pb : Scalar.QComplex := ((-164447452387569785417109 : Int)/10^30,(-431477489393195497733232127 : Int)/10^30)
theorem v1904_pb_checked : Scalar.distance (sourceCoefficient 22 24 1 1) v1904_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1904_pg : Scalar.QComplex := ((-93086423107128216073052 : Int)/10^30,(35477691207869652608 : Int)/10^30)
theorem v1904_pg_checked : Scalar.distance (sourceCoefficient 22 24 1 2) v1904_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1904_mb : Scalar.QComplex := ((-536793031477860873962773 : Int)/10^30,(-431477186823661729061337745 : Int)/10^30)
theorem v1904_mb_checked : Scalar.distance (sourceCoefficient 22 24 3 1) v1904_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1904_mg : Scalar.QComplex := ((-93086357831148977093821 : Int)/10^30,(115807068682490025105 : Int)/10^30)
theorem v1904_mg_checked : Scalar.distance (sourceCoefficient 22 24 3 2) v1904_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1904_upper : Scalar.QComplex := ((999997780199422821565007780289 : Int)/10^30,(-2107034937261902058261339304 : Int)/10^30)
theorem v1904_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 22 24 5) 1) 14) v1904_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1904 : Material (22 : Basis) (24 : Basis) where
  plus := ![v1904_pa,v1904_pb,v1904_pg]
  minus := ![(Primitive.Addresses.material1904 1).one,v1904_mb,v1904_mg]
  upper := v1904_upper
  lower := (Primitive.Addresses.material1904 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1904_pa_checked.trans (by decide +kernel)
    · exact v1904_pb_checked.trans (by decide +kernel)
    · exact v1904_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 22 24 Primitive.Addresses.material1904
    · exact v1904_mb_checked.trans (by decide +kernel)
    · exact v1904_mg_checked.trans (by decide +kernel)
  upper_error := v1904_upper_checked
  lower_error := reuse_lower_error 22 24 Primitive.Addresses.material1904

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
