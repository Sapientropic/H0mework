import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B116

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v2785_pa : Scalar.QComplex := ((999998963576714727005399383274 : Int)/10^30,(-1439737995738378415727336242 : Int)/10^30)
theorem v2785_pa_checked : Scalar.distance (sourceCoefficient 34 83 1 0) v2785_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2785_pb : Scalar.QComplex := ((-621214515414928677953319 : Int)/10^30,(-431477028051306257251569592 : Int)/10^30)
theorem v2785_pb_checked : Scalar.distance (sourceCoefficient 34 83 1 1) v2785_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2785_pg : Scalar.QComplex := ((-93086328484361332223500 : Int)/10^30,(134020062904232596761 : Int)/10^30)
theorem v2785_pg_checked : Scalar.distance (sourceCoefficient 34 83 1 2) v2785_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2785_mb : Scalar.QComplex := ((-993559526312694568210463 : Int)/10^30,(-431476331312540899487974353 : Int)/10^30)
theorem v2785_mb_checked : Scalar.distance (sourceCoefficient 34 83 3 1) v2785_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2785_mg : Scalar.QComplex := ((-93086178170788735331716 : Int)/10^30,(214349322031838208292 : Int)/10^30)
theorem v2785_mg_checked : Scalar.distance (sourceCoefficient 34 83 3 2) v2785_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2785_upper : Scalar.QComplex := ((999994989338557975683808285225 : Int)/10^30,(-3165643343353850687263692576 : Int)/10^30)
theorem v2785_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 83 5) 1) 14) v2785_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2785 : Material (34 : Basis) (83 : Basis) where
  plus := ![v2785_pa,v2785_pb,v2785_pg]
  minus := ![(Primitive.Addresses.material2785 1).one,v2785_mb,v2785_mg]
  upper := v2785_upper
  lower := (Primitive.Addresses.material2785 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2785_pa_checked.trans (by decide +kernel)
    · exact v2785_pb_checked.trans (by decide +kernel)
    · exact v2785_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 83 Primitive.Addresses.material2785
    · exact v2785_mb_checked.trans (by decide +kernel)
    · exact v2785_mg_checked.trans (by decide +kernel)
  upper_error := v2785_upper_checked
  lower_error := reuse_lower_error 34 83 Primitive.Addresses.material2785

def v2786_pa : Scalar.QComplex := ((999998912368302941546930326865 : Int)/10^30,(-1474877015609843210460409195 : Int)/10^30)
theorem v2786_pa_checked : Scalar.distance (sourceCoefficient 34 84 1 0) v2786_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2786_pb : Scalar.QComplex := ((-636376204914969037868709 : Int)/10^30,(-431477001835915110890520402 : Int)/10^30)
theorem v2786_pb_checked : Scalar.distance (sourceCoefficient 34 84 1 1) v2786_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2786_pg : Scalar.QComplex := ((-93086323273119082018648 : Int)/10^30,(137291027985224722132 : Int)/10^30)
theorem v2786_pg_checked : Scalar.distance (sourceCoefficient 34 84 1 2) v2786_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2786_mb : Scalar.QComplex := ((-1008721187544643141897663 : Int)/10^30,(-431476292013304332926553926 : Int)/10^30)
theorem v2786_mb_checked : Scalar.distance (sourceCoefficient 34 84 3 1) v2786_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2786_mg : Scalar.QComplex := ((-93086170136852879412831 : Int)/10^30,(217620281397833187231 : Int)/10^30)
theorem v2786_mg_checked : Scalar.distance (sourceCoefficient 34 84 3 2) v2786_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2786_upper : Scalar.QComplex := ((999994877483461947972209306279 : Int)/10^30,(-3200782222508799951807012475 : Int)/10^30)
theorem v2786_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 84 5) 1) 14) v2786_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2786 : Material (34 : Basis) (84 : Basis) where
  plus := ![v2786_pa,v2786_pb,v2786_pg]
  minus := ![(Primitive.Addresses.material2786 1).one,v2786_mb,v2786_mg]
  upper := v2786_upper
  lower := (Primitive.Addresses.material2786 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2786_pa_checked.trans (by decide +kernel)
    · exact v2786_pb_checked.trans (by decide +kernel)
    · exact v2786_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 84 Primitive.Addresses.material2786
    · exact v2786_mb_checked.trans (by decide +kernel)
    · exact v2786_mg_checked.trans (by decide +kernel)
  upper_error := v2786_upper_checked
  lower_error := reuse_lower_error 34 84 Primitive.Addresses.material2786

def v2787_pa : Scalar.QComplex := ((999998792644233293190990661864 : Int)/10^30,(-1553933742379536148313330564 : Int)/10^30)
theorem v2787_pa_checked : Scalar.distance (sourceCoefficient 34 85 1 0) v2787_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2787_pb : Scalar.QComplex := ((-670487386043801217560523 : Int)/10^30,(-431476940258903315203759720 : Int)/10^30)
theorem v2787_pb_checked : Scalar.distance (sourceCoefficient 34 85 1 1) v2787_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2787_pg : Scalar.QComplex := ((-93086311058501547421484 : Int)/10^30,(144650134351616774797 : Int)/10^30)
theorem v2787_pg_checked : Scalar.distance (sourceCoefficient 34 85 1 2) v2787_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2787_mb : Scalar.QComplex := ((-1042832302834135775316496 : Int)/10^30,(-431476200999902461560835760 : Int)/10^30)
theorem v2787_mb_checked : Scalar.distance (sourceCoefficient 34 85 3 1) v2787_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2787_mg : Scalar.QComplex := ((-93086151571662540526713 : Int)/10^30,(224979374483428805507 : Int)/10^30)
theorem v2787_mg_checked : Scalar.distance (sourceCoefficient 34 85 3 2) v2787_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2787_upper : Scalar.QComplex := ((999994621314832180292412633230 : Int)/10^30,(-3279838624899902091373100346 : Int)/10^30)
theorem v2787_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 85 5) 1) 14) v2787_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2787 : Material (34 : Basis) (85 : Basis) where
  plus := ![v2787_pa,v2787_pb,v2787_pg]
  minus := ![(Primitive.Addresses.material2787 1).one,v2787_mb,v2787_mg]
  upper := v2787_upper
  lower := (Primitive.Addresses.material2787 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2787_pa_checked.trans (by decide +kernel)
    · exact v2787_pb_checked.trans (by decide +kernel)
    · exact v2787_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 85 Primitive.Addresses.material2787
    · exact v2787_mb_checked.trans (by decide +kernel)
    · exact v2787_mg_checked.trans (by decide +kernel)
  upper_error := v2787_upper_checked
  lower_error := reuse_lower_error 34 85 Primitive.Addresses.material2787

def v2788_pa : Scalar.QComplex := ((999998769874306912113227631024 : Int)/10^30,(-1568518368705496782963533255 : Int)/10^30)
theorem v2788_pa_checked : Scalar.distance (sourceCoefficient 34 86 1 0) v2788_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2788_pb : Scalar.QComplex := ((-676780320559361044818020 : Int)/10^30,(-431476928506134372222898566 : Int)/10^30)
theorem v2788_pb_checked : Scalar.distance (sourceCoefficient 34 86 1 1) v2788_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2788_pg : Scalar.QComplex := ((-93086308730952004475866 : Int)/10^30,(146007764727391861990 : Int)/10^30)
theorem v2788_pg_checked : Scalar.distance (sourceCoefficient 34 86 1 2) v2788_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2788_mb : Scalar.QComplex := ((-1049125224864438208387155 : Int)/10^30,(-431476183816618830994264475 : Int)/10^30)
theorem v2788_mb_checked : Scalar.distance (sourceCoefficient 34 86 3 1) v2788_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2788_mg : Scalar.QComplex := ((-93086148072539995342564 : Int)/10^30,(226337002345125630404 : Int)/10^30)
theorem v2788_mg_checked : Scalar.distance (sourceCoefficient 34 86 3 2) v2788_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2788_upper : Scalar.QComplex := ((999994573373197780701942106492 : Int)/10^30,(-3294423190204947781905999163 : Int)/10^30)
theorem v2788_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 86 5) 1) 14) v2788_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2788 : Material (34 : Basis) (86 : Basis) where
  plus := ![v2788_pa,v2788_pb,v2788_pg]
  minus := ![(Primitive.Addresses.material2788 1).one,v2788_mb,v2788_mg]
  upper := v2788_upper
  lower := (Primitive.Addresses.material2788 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2788_pa_checked.trans (by decide +kernel)
    · exact v2788_pb_checked.trans (by decide +kernel)
    · exact v2788_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 86 Primitive.Addresses.material2788
    · exact v2788_mb_checked.trans (by decide +kernel)
    · exact v2788_mg_checked.trans (by decide +kernel)
  upper_error := v2788_upper_checked
  lower_error := reuse_lower_error 34 86 Primitive.Addresses.material2788

def v2789_pa : Scalar.QComplex := ((999998768359033853448332978900 : Int)/10^30,(-1569484123957179072309346877 : Int)/10^30)
theorem v2789_pa_checked : Scalar.distance (sourceCoefficient 34 87 1 0) v2789_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2789_pb : Scalar.QComplex := ((-677197021979568177048992 : Int)/10^30,(-431476927723577277095345674 : Int)/10^30)
theorem v2789_pb_checked : Scalar.distance (sourceCoefficient 34 87 1 1) v2789_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2789_pg : Scalar.QComplex := ((-93086308576012371741621 : Int)/10^30,(146097663407697733798 : Int)/10^30)
theorem v2789_pg_checked : Scalar.distance (sourceCoefficient 34 87 1 2) v2789_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2789_mb : Scalar.QComplex := ((-1049541925454176829647433 : Int)/10^30,(-431476182674467469145010081 : Int)/10^30)
theorem v2789_mb_checked : Scalar.distance (sourceCoefficient 34 87 3 1) v2789_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2789_mg : Scalar.QComplex := ((-93086147840021908081717 : Int)/10^30,(226426900858252190134 : Int)/10^30)
theorem v2789_mg_checked : Scalar.distance (sourceCoefficient 34 87 3 2) v2789_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2789_upper : Scalar.QComplex := ((999994570191121027086680741953 : Int)/10^30,(-3295388941403027234694483003 : Int)/10^30)
theorem v2789_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 87 5) 1) 14) v2789_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2789 : Material (34 : Basis) (87 : Basis) where
  plus := ![v2789_pa,v2789_pb,v2789_pg]
  minus := ![(Primitive.Addresses.material2789 1).one,v2789_mb,v2789_mg]
  upper := v2789_upper
  lower := (Primitive.Addresses.material2789 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2789_pa_checked.trans (by decide +kernel)
    · exact v2789_pb_checked.trans (by decide +kernel)
    · exact v2789_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 87 Primitive.Addresses.material2789
    · exact v2789_mb_checked.trans (by decide +kernel)
    · exact v2789_mg_checked.trans (by decide +kernel)
  upper_error := v2789_upper_checked
  lower_error := reuse_lower_error 34 87 Primitive.Addresses.material2789

def v2790_pa : Scalar.QComplex := ((999998749833394529283646873088 : Int)/10^30,(-1581243702920233378179564050 : Int)/10^30)
theorem v2790_pa_checked : Scalar.distance (sourceCoefficient 34 88 1 0) v2790_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2790_pb : Scalar.QComplex := ((-682271012735203336069327 : Int)/10^30,(-431476918151676452865366500 : Int)/10^30)
theorem v2790_pb_checked : Scalar.distance (sourceCoefficient 34 88 1 1) v2790_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2790_pg : Scalar.QComplex := ((-93086306681254497477624 : Int)/10^30,(147192320282758721310 : Int)/10^30)
theorem v2790_pg_checked : Scalar.distance (sourceCoefficient 34 88 1 2) v2790_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2790_mb : Scalar.QComplex := ((-1054615906060414028610905 : Int)/10^30,(-431476168723944710918444939 : Int)/10^30)
theorem v2790_mb_checked : Scalar.distance (sourceCoefficient 34 88 3 1) v2790_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2790_mg : Scalar.QComplex := ((-93086145000625157660534 : Int)/10^30,(227521555690631686007 : Int)/10^30)
theorem v2790_mg_checked : Scalar.distance (sourceCoefficient 34 88 3 2) v2790_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2790_upper : Scalar.QComplex := ((999994531369542825123844128819 : Int)/10^30,(-3307148470877997211639622903 : Int)/10^30)
theorem v2790_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 88 5) 1) 14) v2790_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2790 : Material (34 : Basis) (88 : Basis) where
  plus := ![v2790_pa,v2790_pb,v2790_pg]
  minus := ![(Primitive.Addresses.material2790 1).one,v2790_mb,v2790_mg]
  upper := v2790_upper
  lower := (Primitive.Addresses.material2790 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2790_pa_checked.trans (by decide +kernel)
    · exact v2790_pb_checked.trans (by decide +kernel)
    · exact v2790_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 88 Primitive.Addresses.material2790
    · exact v2790_mb_checked.trans (by decide +kernel)
    · exact v2790_mg_checked.trans (by decide +kernel)
  upper_error := v2790_upper_checked
  lower_error := reuse_lower_error 34 88 Primitive.Addresses.material2790

def v2791_pa : Scalar.QComplex := ((999998724262562843850655390224 : Int)/10^30,(-1597333167127725463570474695 : Int)/10^30)
theorem v2791_pa_checked : Scalar.distance (sourceCoefficient 34 89 1 0) v2791_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2791_pb : Scalar.QComplex := ((-689213250343868070740000 : Int)/10^30,(-431476904926504813064142971 : Int)/10^30)
theorem v2791_pb_checked : Scalar.distance (sourceCoefficient 34 89 1 1) v2791_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2791_pg : Scalar.QComplex := ((-93086304064514642174475 : Int)/10^30,(148690030577024176043 : Int)/10^30)
theorem v2791_pg_checked : Scalar.distance (sourceCoefficient 34 89 1 2) v2791_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2791_mb : Scalar.QComplex := ((-1061558129671438940114252 : Int)/10^30,(-431476149507939605950535077 : Int)/10^30)
theorem v2791_mb_checked : Scalar.distance (sourceCoefficient 34 89 3 1) v2791_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2791_mg : Scalar.QComplex := ((-93086141091429747105766 : Int)/10^30,(229019263169102507905 : Int)/10^30)
theorem v2791_mg_checked : Scalar.distance (sourceCoefficient 34 89 3 2) v2791_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2791_upper : Scalar.QComplex := ((999994478029793627100488357772 : Int)/10^30,(-3323237866989186639874357780 : Int)/10^30)
theorem v2791_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 89 5) 1) 14) v2791_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2791 : Material (34 : Basis) (89 : Basis) where
  plus := ![v2791_pa,v2791_pb,v2791_pg]
  minus := ![(Primitive.Addresses.material2791 1).one,v2791_mb,v2791_mg]
  upper := v2791_upper
  lower := (Primitive.Addresses.material2791 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2791_pa_checked.trans (by decide +kernel)
    · exact v2791_pb_checked.trans (by decide +kernel)
    · exact v2791_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 89 Primitive.Addresses.material2791
    · exact v2791_mb_checked.trans (by decide +kernel)
    · exact v2791_mg_checked.trans (by decide +kernel)
  upper_error := v2791_upper_checked
  lower_error := reuse_lower_error 34 89 Primitive.Addresses.material2791

def v2792_pa : Scalar.QComplex := ((999998682064438386099784751024 : Int)/10^30,(-1623536074829769793973442433 : Int)/10^30)
theorem v2792_pa_checked : Scalar.distance (sourceCoefficient 34 90 1 0) v2792_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2792_pb : Scalar.QComplex := ((-700519208357684580844196 : Int)/10^30,(-431476883069542320662638413 : Int)/10^30)
theorem v2792_pb_checked : Scalar.distance (sourceCoefficient 34 90 1 1) v2792_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2792_pg : Scalar.QComplex := ((-93086299742781148530444 : Int)/10^30,(151129164883323112228 : Int)/10^30)
theorem v2792_pg_checked : Scalar.distance (sourceCoefficient 34 90 1 2) v2792_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2792_mb : Scalar.QComplex := ((-1072864064613956343972920 : Int)/10^30,(-431476117894452687417926838 : Int)/10^30)
theorem v2792_mb_checked : Scalar.distance (sourceCoefficient 34 90 3 1) v2792_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2792_mg : Scalar.QComplex := ((-93086134664834810835810 : Int)/10^30,(231458392837738906546 : Int)/10^30)
theorem v2792_mg_checked : Scalar.distance (sourceCoefficient 34 90 3 2) v2792_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2792_upper : Scalar.QComplex := ((999994390607890433988314645104 : Int)/10^30,(-3349440662834943327708042607 : Int)/10^30)
theorem v2792_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 90 5) 1) 14) v2792_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2792 : Material (34 : Basis) (90 : Basis) where
  plus := ![v2792_pa,v2792_pb,v2792_pg]
  minus := ![(Primitive.Addresses.material2792 1).one,v2792_mb,v2792_mg]
  upper := v2792_upper
  lower := (Primitive.Addresses.material2792 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2792_pa_checked.trans (by decide +kernel)
    · exact v2792_pb_checked.trans (by decide +kernel)
    · exact v2792_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 90 Primitive.Addresses.material2792
    · exact v2792_mb_checked.trans (by decide +kernel)
    · exact v2792_mg_checked.trans (by decide +kernel)
  upper_error := v2792_upper_checked
  lower_error := reuse_lower_error 34 90 Primitive.Addresses.material2792

def v2793_pa : Scalar.QComplex := ((999998657990362670263677083825 : Int)/10^30,(-1638297126186091422071903401 : Int)/10^30)
theorem v2793_pa_checked : Scalar.distance (sourceCoefficient 34 91 1 0) v2793_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2793_pb : Scalar.QComplex := ((-706888265742409747996176 : Int)/10^30,(-431476870582784909274578362 : Int)/10^30)
theorem v2793_pb_checked : Scalar.distance (sourceCoefficient 34 91 1 1) v2793_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2793_pg : Scalar.QComplex := ((-93086297275357416537259 : Int)/10^30,(152503217974310492893 : Int)/10^30)
theorem v2793_pg_checked : Scalar.distance (sourceCoefficient 34 91 1 2) v2793_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2793_mb : Scalar.QComplex := ((-1079233108851681103138867 : Int)/10^30,(-431476099911490254098677325 : Int)/10^30)
theorem v2793_mb_checked : Scalar.distance (sourceCoefficient 34 91 3 1) v2793_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2793_mg : Scalar.QComplex := ((-93086131011666065109075 : Int)/10^30,(232832443287827972038 : Int)/10^30)
theorem v2793_mg_checked : Scalar.distance (sourceCoefficient 34 91 3 2) v2793_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2793_upper : Scalar.QComplex := ((999994341057615044767391720151 : Int)/10^30,(-3364201650656742213016919325 : Int)/10^30)
theorem v2793_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 91 5) 1) 14) v2793_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2793 : Material (34 : Basis) (91 : Basis) where
  plus := ![v2793_pa,v2793_pb,v2793_pg]
  minus := ![(Primitive.Addresses.material2793 1).one,v2793_mb,v2793_mg]
  upper := v2793_upper
  lower := (Primitive.Addresses.material2793 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2793_pa_checked.trans (by decide +kernel)
    · exact v2793_pb_checked.trans (by decide +kernel)
    · exact v2793_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 91 Primitive.Addresses.material2793
    · exact v2793_mb_checked.trans (by decide +kernel)
    · exact v2793_mg_checked.trans (by decide +kernel)
  upper_error := v2793_upper_checked
  lower_error := reuse_lower_error 34 91 Primitive.Addresses.material2793

def v2794_pa : Scalar.QComplex := ((999998605126172658748887233596 : Int)/10^30,(-1670253187097545407315804757 : Int)/10^30)
theorem v2794_pa_checked : Scalar.distance (sourceCoefficient 34 92 1 0) v2794_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2794_pb : Scalar.QComplex := ((-720676577634344582352938 : Int)/10^30,(-431476843120886604798829699 : Int)/10^30)
theorem v2794_pb_checked : Scalar.distance (sourceCoefficient 34 92 1 1) v2794_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2794_pg : Scalar.QComplex := ((-93086291852589956810632 : Int)/10^30,(155477892513923647670 : Int)/10^30)
theorem v2794_pg_checked : Scalar.distance (sourceCoefficient 34 92 1 2) v2794_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2794_mb : Scalar.QComplex := ((-1093021391911215864367920 : Int)/10^30,(-431476060550910014717891913 : Int)/10^30)
theorem v2794_mb_checked : Scalar.distance (sourceCoefficient 34 92 3 1) v2794_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2794_mg : Scalar.QComplex := ((-93086123021890471208355 : Int)/10^30,(235807112040229761010 : Int)/10^30)
theorem v2794_mg_checked : Scalar.distance (sourceCoefficient 34 92 3 2) v2794_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2794_upper : Scalar.QComplex := ((999994233040241666284079659702 : Int)/10^30,(-3396157572734601135236994148 : Int)/10^30)
theorem v2794_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 92 5) 1) 14) v2794_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2794 : Material (34 : Basis) (92 : Basis) where
  plus := ![v2794_pa,v2794_pb,v2794_pg]
  minus := ![(Primitive.Addresses.material2794 1).one,v2794_mb,v2794_mg]
  upper := v2794_upper
  lower := (Primitive.Addresses.material2794 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2794_pa_checked.trans (by decide +kernel)
    · exact v2794_pb_checked.trans (by decide +kernel)
    · exact v2794_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 92 Primitive.Addresses.material2794
    · exact v2794_mb_checked.trans (by decide +kernel)
    · exact v2794_mg_checked.trans (by decide +kernel)
  upper_error := v2794_upper_checked
  lower_error := reuse_lower_error 34 92 Primitive.Addresses.material2794

def v2795_pa : Scalar.QComplex := ((999998541061623851231484351463 : Int)/10^30,(-1708178744685798867200160343 : Int)/10^30)
theorem v2795_pa_checked : Scalar.distance (sourceCoefficient 34 93 1 0) v2795_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2795_pb : Scalar.QComplex := ((-737040590565032912980926 : Int)/10^30,(-431476809766650656168885340 : Int)/10^30)
theorem v2795_pb_checked : Scalar.distance (sourceCoefficient 34 93 1 1) v2795_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2795_pg : Scalar.QComplex := ((-93086285272918946338304 : Int)/10^30,(159008245908190931522 : Int)/10^30)
theorem v2795_pg_checked : Scalar.distance (sourceCoefficient 34 93 1 2) v2795_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2795_mb : Scalar.QComplex := ((-1109385369965630903918560 : Int)/10^30,(-431476013075280333993709046 : Int)/10^30)
theorem v2795_mb_checked : Scalar.distance (sourceCoefficient 34 93 3 1) v2795_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2795_mg : Scalar.QComplex := ((-93086113395685932610059 : Int)/10^30,(239337458442025386400 : Int)/10^30)
theorem v2795_mg_checked : Scalar.distance (sourceCoefficient 34 93 3 2) v2795_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2795_upper : Scalar.QComplex := ((999994103519716457769175874693 : Int)/10^30,(-3434082963267592265055040818 : Int)/10^30)
theorem v2795_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 93 5) 1) 14) v2795_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2795 : Material (34 : Basis) (93 : Basis) where
  plus := ![v2795_pa,v2795_pb,v2795_pg]
  minus := ![(Primitive.Addresses.material2795 1).one,v2795_mb,v2795_mg]
  upper := v2795_upper
  lower := (Primitive.Addresses.material2795 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2795_pa_checked.trans (by decide +kernel)
    · exact v2795_pb_checked.trans (by decide +kernel)
    · exact v2795_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 93 Primitive.Addresses.material2795
    · exact v2795_mb_checked.trans (by decide +kernel)
    · exact v2795_mg_checked.trans (by decide +kernel)
  upper_error := v2795_upper_checked
  lower_error := reuse_lower_error 34 93 Primitive.Addresses.material2795

def v2796_pa : Scalar.QComplex := ((999998463534226255410466541057 : Int)/10^30,(-1752977235095226551344410864 : Int)/10^30)
theorem v2796_pa_checked : Scalar.distance (sourceCoefficient 34 94 1 0) v2796_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2796_pb : Scalar.QComplex := ((-756370116195442644697159 : Int)/10^30,(-431476769301889298325906733 : Int)/10^30)
theorem v2796_pb_checked : Scalar.distance (sourceCoefficient 34 94 1 1) v2796_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2796_pg : Scalar.QComplex := ((-93086277299635659991382 : Int)/10^30,(163178375724012186104 : Int)/10^30)
theorem v2796_pg_checked : Scalar.distance (sourceCoefficient 34 94 1 2) v2796_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2796_mb : Scalar.QComplex := ((-1128714853479508253850927 : Int)/10^30,(-431475955930023993504450540 : Int)/10^30)
theorem v2796_mb_checked : Scalar.distance (sourceCoefficient 34 94 3 1) v2796_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2796_mg : Scalar.QComplex := ((-93086101823771399702018 : Int)/10^30,(243507579824532353435 : Int)/10^30)
theorem v2796_mg_checked : Scalar.distance (sourceCoefficient 34 94 3 2) v2796_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2796_upper : Scalar.QComplex := ((999993948674303970530721840120 : Int)/10^30,(-3478881253149675864885943547 : Int)/10^30)
theorem v2796_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 94 5) 1) 14) v2796_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2796 : Material (34 : Basis) (94 : Basis) where
  plus := ![v2796_pa,v2796_pb,v2796_pg]
  minus := ![(Primitive.Addresses.material2796 1).one,v2796_mb,v2796_mg]
  upper := v2796_upper
  lower := (Primitive.Addresses.material2796 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2796_pa_checked.trans (by decide +kernel)
    · exact v2796_pb_checked.trans (by decide +kernel)
    · exact v2796_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 94 Primitive.Addresses.material2796
    · exact v2796_mb_checked.trans (by decide +kernel)
    · exact v2796_mg_checked.trans (by decide +kernel)
  upper_error := v2796_upper_checked
  lower_error := reuse_lower_error 34 94 Primitive.Addresses.material2796

def v2797_pa : Scalar.QComplex := ((999998384942418143840786898689 : Int)/10^30,(-1797251389010821077779144293 : Int)/10^30)
theorem v2797_pa_checked : Scalar.distance (sourceCoefficient 34 95 1 0) v2797_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2797_pb : Scalar.QComplex := ((-775473401474985619032812 : Int)/10^30,(-431476728176349733696893266 : Int)/10^30)
theorem v2797_pb_checked : Scalar.distance (sourceCoefficient 34 95 1 1) v2797_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2797_pg : Scalar.QComplex := ((-93086269205533544027279 : Int)/10^30,(167299696826124183517 : Int)/10^30)
theorem v2797_pg_checked : Scalar.distance (sourceCoefficient 34 95 1 2) v2797_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2797_mb : Scalar.QComplex := ((-1147818096156536636614563 : Int)/10^30,(-431475898319224925577942740 : Int)/10^30)
theorem v2797_mb_checked : Scalar.distance (sourceCoefficient 34 95 3 1) v2797_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2797_mg : Scalar.QComplex := ((-93086090173157803831395 : Int)/10^30,(247628892407242569602 : Int)/10^30)
theorem v2797_mg_checked : Scalar.distance (sourceCoefficient 34 95 3 2) v2797_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2797_upper : Scalar.QComplex := ((999993793669439773778920813235 : Int)/10^30,(-3523155205481787934066080336 : Int)/10^30)
theorem v2797_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 95 5) 1) 14) v2797_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2797 : Material (34 : Basis) (95 : Basis) where
  plus := ![v2797_pa,v2797_pb,v2797_pg]
  minus := ![(Primitive.Addresses.material2797 1).one,v2797_mb,v2797_mg]
  upper := v2797_upper
  lower := (Primitive.Addresses.material2797 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2797_pa_checked.trans (by decide +kernel)
    · exact v2797_pb_checked.trans (by decide +kernel)
    · exact v2797_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 95 Primitive.Addresses.material2797
    · exact v2797_mb_checked.trans (by decide +kernel)
    · exact v2797_mg_checked.trans (by decide +kernel)
  upper_error := v2797_upper_checked
  lower_error := reuse_lower_error 34 95 Primitive.Addresses.material2797

def v2798_pa : Scalar.QComplex := ((999998346499410370383641471121 : Int)/10^30,(-1818515450909074022643684766 : Int)/10^30)
theorem v2798_pa_checked : Scalar.distance (sourceCoefficient 34 96 1 0) v2798_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2798_pb : Scalar.QComplex := ((-784648357664884130355144 : Int)/10^30,(-431476708023634230283294443 : Int)/10^30)
theorem v2798_pb_checked : Scalar.distance (sourceCoefficient 34 96 1 1) v2798_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2798_pg : Scalar.QComplex := ((-93086265242411323226087 : Int)/10^30,(169279091513822922210 : Int)/10^30)
theorem v2798_pg_checked : Scalar.distance (sourceCoefficient 34 96 1 2) v2798_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2798_mb : Scalar.QComplex := ((-1156993031539293807392147 : Int)/10^30,(-431475870248942958746106760 : Int)/10^30)
theorem v2798_mb_checked : Scalar.distance (sourceCoefficient 34 96 3 1) v2798_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2798_mg : Scalar.QComplex := ((-93086084501908591825099 : Int)/10^30,(249608282937926219107 : Int)/10^30)
theorem v2798_mg_checked : Scalar.distance (sourceCoefficient 34 96 3 2) v2798_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2798_upper : Scalar.QComplex := ((999993718526647480907853056647 : Int)/10^30,(-3544419169360574639093118344 : Int)/10^30)
theorem v2798_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 96 5) 1) 14) v2798_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2798 : Material (34 : Basis) (96 : Basis) where
  plus := ![v2798_pa,v2798_pb,v2798_pg]
  minus := ![(Primitive.Addresses.material2798 1).one,v2798_mb,v2798_mg]
  upper := v2798_upper
  lower := (Primitive.Addresses.material2798 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2798_pa_checked.trans (by decide +kernel)
    · exact v2798_pb_checked.trans (by decide +kernel)
    · exact v2798_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 96 Primitive.Addresses.material2798
    · exact v2798_mb_checked.trans (by decide +kernel)
    · exact v2798_mg_checked.trans (by decide +kernel)
  upper_error := v2798_upper_checked
  lower_error := reuse_lower_error 34 96 Primitive.Addresses.material2798

def v2799_pa : Scalar.QComplex := ((999998210776425957683696268588 : Int)/10^30,(-1891677548305639403457485300 : Int)/10^30)
theorem v2799_pa_checked : Scalar.distance (sourceCoefficient 34 97 1 0) v2799_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2799_pb : Scalar.QComplex := ((-816216126653287512840975 : Int)/10^30,(-431476636698061571233357673 : Int)/10^30)
theorem v2799_pb_checked : Scalar.distance (sourceCoefficient 34 97 1 1) v2799_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2799_pg : Scalar.QComplex := ((-93086251231581554662965 : Int)/10^30,(176089486574181521317 : Int)/10^30)
theorem v2799_pg_checked : Scalar.distance (sourceCoefficient 34 97 1 2) v2799_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2799_mb : Scalar.QComplex := ((-1188560727222817256964046 : Int)/10^30,(-431475771681833980011534387 : Int)/10^30)
theorem v2799_mb_checked : Scalar.distance (sourceCoefficient 34 97 3 1) v2799_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2799_mg : Scalar.QComplex := ((-93086064614019831851966 : Int)/10^30,(256418663371748420889 : Int)/10^30)
theorem v2799_mg_checked : Scalar.distance (sourceCoefficient 34 97 3 2) v2799_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2799_upper : Scalar.QComplex := ((999993456532722318806950419545 : Int)/10^30,(-3617580923545231768038605903 : Int)/10^30)
theorem v2799_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 34 97 5) 1) 14) v2799_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2799 : Material (34 : Basis) (97 : Basis) where
  plus := ![v2799_pa,v2799_pb,v2799_pg]
  minus := ![(Primitive.Addresses.material2799 1).one,v2799_mb,v2799_mg]
  upper := v2799_upper
  lower := (Primitive.Addresses.material2799 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2799_pa_checked.trans (by decide +kernel)
    · exact v2799_pb_checked.trans (by decide +kernel)
    · exact v2799_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 34 97 Primitive.Addresses.material2799
    · exact v2799_mb_checked.trans (by decide +kernel)
    · exact v2799_mg_checked.trans (by decide +kernel)
  upper_error := v2799_upper_checked
  lower_error := reuse_lower_error 34 97 Primitive.Addresses.material2799

def v2800_pa : Scalar.QComplex := ((999999710483509610079877998911 : Int)/10^30,(-760942111438210545501955220 : Int)/10^30)
theorem v2800_pa_checked : Scalar.distance (sourceCoefficient 35 36 1 0) v2800_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v2800_pb : Scalar.QComplex := ((-328329415854097831518128 : Int)/10^30,(-431477396062050397637950040 : Int)/10^30)
theorem v2800_pb_checked : Scalar.distance (sourceCoefficient 35 36 1 1) v2800_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2800_pg : Scalar.QComplex := ((-93086402944897582822607 : Int)/10^30,(70833384510511312688 : Int)/10^30)
theorem v2800_pg_checked : Scalar.distance (sourceCoefficient 35 36 1 2) v2800_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2800_mb : Scalar.QComplex := ((-700674853383069403095167 : Int)/10^30,(-431476952069797878443176849 : Int)/10^30)
theorem v2800_mb_checked : Scalar.distance (sourceCoefficient 35 36 3 1) v2800_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v2800_mg : Scalar.QComplex := ((-93086307158554892298668 : Int)/10^30,(151162731421494270267 : Int)/10^30)
theorem v2800_mg_checked : Scalar.distance (sourceCoefficient 35 36 3 2) v2800_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v2800_upper : Scalar.QComplex := ((999996907784356849326813219190 : Int)/10^30,(-2486849759133784629409995247 : Int)/10^30)
theorem v2800_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 35 36 5) 1) 14) v2800_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material2800 : Material (35 : Basis) (36 : Basis) where
  plus := ![v2800_pa,v2800_pb,v2800_pg]
  minus := ![(Primitive.Addresses.material2800 1).one,v2800_mb,v2800_mg]
  upper := v2800_upper
  lower := (Primitive.Addresses.material2800 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v2800_pa_checked.trans (by decide +kernel)
    · exact v2800_pb_checked.trans (by decide +kernel)
    · exact v2800_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 35 36 Primitive.Addresses.material2800
    · exact v2800_mb_checked.trans (by decide +kernel)
    · exact v2800_mg_checked.trans (by decide +kernel)
  upper_error := v2800_upper_checked
  lower_error := reuse_lower_error 35 36 Primitive.Addresses.material2800

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
