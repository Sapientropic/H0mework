import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B030
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B031

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v737_pa : Scalar.QComplex := ((999999401827077253407308973457 : Int)/10^30,(-1093775794064917069671284449 : Int)/10^30)
theorem v737_pa_checked : Scalar.distance (sourceCoefficient 7 87 1 0) v737_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v737_pb : Scalar.QComplex := ((-471939513298691829279735 : Int)/10^30,(-431477121324229606648456186 : Int)/10^30)
theorem v737_pb_checked : Scalar.distance (sourceCoefficient 7 87 1 1) v737_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v737_pg : Scalar.QComplex := ((-93086358943234708094689 : Int)/10^30,(101815667073123591948 : Int)/10^30)
theorem v737_pg_checked : Scalar.distance (sourceCoefficient 7 87 1 2) v737_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v737_mb : Scalar.QComplex := ((-844284660268695206037297 : Int)/10^30,(-431476553403033248902874072 : Int)/10^30)
theorem v737_mb_checked : Scalar.distance (sourceCoefficient 7 87 3 1) v737_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v737_mg : Scalar.QComplex := ((-93086236420593940073718 : Int)/10^30,(182144964476533491643 : Int)/10^30)
theorem v737_mg_checked : Scalar.distance (sourceCoefficient 7 87 3 2) v737_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v737_upper : Scalar.QComplex := ((999996024687642422279353379170 : Int)/10^30,(-2819682413330817117097208429 : Int)/10^30)
theorem v737_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 87 5) 1) 14) v737_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material737 : Material (7 : Basis) (87 : Basis) where
  plus := ![v737_pa,v737_pb,v737_pg]
  minus := ![(Primitive.Addresses.material737 1).one,v737_mb,v737_mg]
  upper := v737_upper
  lower := (Primitive.Addresses.material737 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v737_pa_checked.trans (by decide +kernel)
    · exact v737_pb_checked.trans (by decide +kernel)
    · exact v737_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 87 Primitive.Addresses.material737
    · exact v737_mb_checked.trans (by decide +kernel)
    · exact v737_mg_checked.trans (by decide +kernel)
  upper_error := v737_upper_checked
  lower_error := reuse_lower_error 7 87 Primitive.Addresses.material737

def v738_pa : Scalar.QComplex := ((999999388895574495784735474037 : Int)/10^30,(-1105535380510190482531028073 : Int)/10^30)
theorem v738_pa_checked : Scalar.distance (sourceCoefficient 7 88 1 0) v738_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v738_pb : Scalar.QComplex := ((-477013506206599584028882 : Int)/10^30,(-431477113361491333933090840 : Int)/10^30)
theorem v738_pb_checked : Scalar.distance (sourceCoefficient 7 88 1 1) v738_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v738_pg : Scalar.QComplex := ((-93086357482425298471252 : Int)/10^30,(102910324528595418808 : Int)/10^30)
theorem v738_pg_checked : Scalar.distance (sourceCoefficient 7 88 1 2) v738_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v738_mb : Scalar.QComplex := ((-849358644415839007306283 : Int)/10^30,(-431476541061670585711847113 : Int)/10^30)
theorem v738_mb_checked : Scalar.distance (sourceCoefficient 7 88 3 1) v738_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v738_mg : Scalar.QComplex := ((-93086234015144991845835 : Int)/10^30,(183239620263801591422 : Int)/10^30)
theorem v738_mg_checked : Scalar.distance (sourceCoefficient 7 88 3 2) v738_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v738_upper : Scalar.QComplex := ((999995991460179541417949901278 : Int)/10^30,(-2831441959942967274892149791 : Int)/10^30)
theorem v738_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 88 5) 1) 14) v738_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material738 : Material (7 : Basis) (88 : Basis) where
  plus := ![v738_pa,v738_pb,v738_pg]
  minus := ![(Primitive.Addresses.material738 1).one,v738_mb,v738_mg]
  upper := v738_upper
  lower := (Primitive.Addresses.material738 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v738_pa_checked.trans (by decide +kernel)
    · exact v738_pb_checked.trans (by decide +kernel)
    · exact v738_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 88 Primitive.Addresses.material738
    · exact v738_mb_checked.trans (by decide +kernel)
    · exact v738_mg_checked.trans (by decide +kernel)
  upper_error := v738_upper_checked
  lower_error := reuse_lower_error 7 88 Primitive.Addresses.material738

def v739_pa : Scalar.QComplex := ((999999370978644420272007746606 : Int)/10^30,(-1121624855061437290520997547 : Int)/10^30)
theorem v739_pa_checked : Scalar.distance (sourceCoefficient 7 89 1 0) v739_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v739_pb : Scalar.QComplex := ((-483955746790662316948224 : Int)/10^30,(-431477102337977028867394272 : Int)/10^30)
theorem v739_pb_checked : Scalar.distance (sourceCoefficient 7 89 1 1) v739_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v739_pg : Scalar.QComplex := ((-93086355459414038472579 : Int)/10^30,(104408035625246805160 : Int)/10^30)
theorem v739_pg_checked : Scalar.distance (sourceCoefficient 7 89 1 2) v739_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v739_mb : Scalar.QComplex := ((-856300872902191930092997 : Int)/10^30,(-431476524047319428067352242 : Int)/10^30)
theorem v739_mb_checked : Scalar.distance (sourceCoefficient 7 89 3 1) v739_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v739_mg : Scalar.QComplex := ((-93086230699677263100332 : Int)/10^30,(184737329057019083378 : Int)/10^30)
theorem v739_mg_checked : Scalar.distance (sourceCoefficient 7 89 3 2) v739_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v739_upper : Scalar.QComplex := ((999995945774302701345227242442 : Int)/10^30,(-2847531379607835842110685796 : Int)/10^30)
theorem v739_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 89 5) 1) 14) v739_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material739 : Material (7 : Basis) (89 : Basis) where
  plus := ![v739_pa,v739_pb,v739_pg]
  minus := ![(Primitive.Addresses.material739 1).one,v739_mb,v739_mg]
  upper := v739_upper
  lower := (Primitive.Addresses.material739 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v739_pa_checked.trans (by decide +kernel)
    · exact v739_pb_checked.trans (by decide +kernel)
    · exact v739_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 89 Primitive.Addresses.material739
    · exact v739_mb_checked.trans (by decide +kernel)
    · exact v739_mg_checked.trans (by decide +kernel)
  upper_error := v739_upper_checked
  lower_error := reuse_lower_error 7 89 Primitive.Addresses.material739

def v740_pa : Scalar.QComplex := ((999999341245476897545462931382 : Int)/10^30,(-1147827779872654661737979346 : Int)/10^30)
theorem v740_pa_checked : Scalar.distance (sourceCoefficient 7 90 1 0) v740_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v740_pb : Scalar.QComplex := ((-495261709725960467423578 : Int)/10^30,(-431477084066579797550281493 : Int)/10^30)
theorem v740_pb_checked : Scalar.distance (sourceCoefficient 7 90 1 1) v740_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v740_pg : Scalar.QComplex := ((-93086352104612408637812 : Int)/10^30,(106847171258738823168 : Int)/10^30)
theorem v740_pg_checked : Scalar.distance (sourceCoefficient 7 90 1 2) v740_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v740_mb : Scalar.QComplex := ((-867606815860370474281469 : Int)/10^30,(-431476496019392188532320317 : Int)/10^30)
theorem v740_mb_checked : Scalar.distance (sourceCoefficient 7 90 3 1) v740_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v740_mg : Scalar.QComplex := ((-93086225240012685298860 : Int)/10^30,(187176460887266719141 : Int)/10^30)
theorem v740_mg_checked : Scalar.distance (sourceCoefficient 7 90 3 2) v740_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v740_upper : Scalar.QComplex := ((999995870817308349287724942305 : Int)/10^30,(-2873734214076124946447185048 : Int)/10^30)
theorem v740_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 90 5) 1) 14) v740_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material740 : Material (7 : Basis) (90 : Basis) where
  plus := ![v740_pa,v740_pb,v740_pg]
  minus := ![(Primitive.Addresses.material740 1).one,v740_mb,v740_mg]
  upper := v740_upper
  lower := (Primitive.Addresses.material740 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v740_pa_checked.trans (by decide +kernel)
    · exact v740_pb_checked.trans (by decide +kernel)
    · exact v740_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 90 Primitive.Addresses.material740
    · exact v740_mb_checked.trans (by decide +kernel)
    · exact v740_mg_checked.trans (by decide +kernel)
  upper_error := v740_upper_checked
  lower_error := reuse_lower_error 7 90 Primitive.Addresses.material740

def v741_pa : Scalar.QComplex := ((999999324193365021022402862835 : Int)/10^30,(-1162588841011020246694911002 : Int)/10^30)
theorem v741_pa_checked : Scalar.distance (sourceCoefficient 7 91 1 0) v741_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v741_pb : Scalar.QComplex := ((-501630769924506582267418 : Int)/10^30,(-431477073599701765827148405 : Int)/10^30)
theorem v741_pb_checked : Scalar.distance (sourceCoefficient 7 91 1 1) v741_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v741_pg : Scalar.QComplex := ((-93086350181896580398845 : Int)/10^30,(108221225108539093035 : Int)/10^30)
theorem v741_pg_checked : Scalar.distance (sourceCoefficient 7 91 1 2) v741_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v741_mb : Scalar.QComplex := ((-873975864654980066085750 : Int)/10^30,(-431476480056305954583843603 : Int)/10^30)
theorem v741_mb_checked : Scalar.distance (sourceCoefficient 7 91 3 1) v741_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v741_mg : Scalar.QComplex := ((-93086222131550985685348 : Int)/10^30,(188550512566226779500 : Int)/10^30)
theorem v741_mg_checked : Scalar.distance (sourceCoefficient 7 91 3 2) v741_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v741_upper : Scalar.QComplex := ((999995828288969458069119332789 : Int)/10^30,(-2888495223799225778480142386 : Int)/10^30)
theorem v741_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 91 5) 1) 14) v741_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material741 : Material (7 : Basis) (91 : Basis) where
  plus := ![v741_pa,v741_pb,v741_pg]
  minus := ![(Primitive.Addresses.material741 1).one,v741_mb,v741_mg]
  upper := v741_upper
  lower := (Primitive.Addresses.material741 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v741_pa_checked.trans (by decide +kernel)
    · exact v741_pb_checked.trans (by decide +kernel)
    · exact v741_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 91 Primitive.Addresses.material741
    · exact v741_mb_checked.trans (by decide +kernel)
    · exact v741_mg_checked.trans (by decide +kernel)
  upper_error := v741_upper_checked
  lower_error := reuse_lower_error 7 91 Primitive.Addresses.material741

def v742_pa : Scalar.QComplex := ((999999286530958405359002677259 : Int)/10^30,(-1194544923454621978023021683 : Int)/10^30)
theorem v742_pa_checked : Scalar.distance (sourceCoefficient 7 92 1 0) v742_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v742_pb : Scalar.QComplex := ((-515419088010198906648090 : Int)/10^30,(-431477050510621285569583600 : Int)/10^30)
theorem v742_pb_checked : Scalar.distance (sourceCoefficient 7 92 1 1) v742_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v742_pg : Scalar.QComplex := ((-93086345938362128359313 : Int)/10^30,(111195901318444393007 : Int)/10^30)
theorem v742_pg_checked : Scalar.distance (sourceCoefficient 7 92 1 2) v742_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v742_mb : Scalar.QComplex := ((-887764157681814849016140 : Int)/10^30,(-431476445068536566287561036 : Int)/10^30)
theorem v742_mb_checked : Scalar.distance (sourceCoefficient 7 92 3 1) v742_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v742_mg : Scalar.QComplex := ((-93086215321006519002487 : Int)/10^30,(191525184006545066693 : Int)/10^30)
theorem v742_mg_checked : Scalar.distance (sourceCoefficient 7 92 3 2) v742_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v742_upper : Scalar.QComplex := ((999995735473319671632927177700 : Int)/10^30,(-2920451193646099423402428488 : Int)/10^30)
theorem v742_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 92 5) 1) 14) v742_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material742 : Material (7 : Basis) (92 : Basis) where
  plus := ![v742_pa,v742_pb,v742_pg]
  minus := ![(Primitive.Addresses.material742 1).one,v742_mb,v742_mg]
  upper := v742_upper
  lower := (Primitive.Addresses.material742 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v742_pa_checked.trans (by decide +kernel)
    · exact v742_pb_checked.trans (by decide +kernel)
    · exact v742_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 92 Primitive.Addresses.material742
    · exact v742_mb_checked.trans (by decide +kernel)
    · exact v742_mg_checked.trans (by decide +kernel)
  upper_error := v742_upper_checked
  lower_error := reuse_lower_error 7 92 Primitive.Addresses.material742

def v743_pa : Scalar.QComplex := ((999999240507935992866665726433 : Int)/10^30,(-1232470507227686718056197231 : Int)/10^30)
theorem v743_pa_checked : Scalar.distance (sourceCoefficient 7 93 1 0) v743_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v743_pb : Scalar.QComplex := ((-531783108472990930200773 : Int)/10^30,(-431477022346059827283949438 : Int)/10^30)
theorem v743_pb_checked : Scalar.distance (sourceCoefficient 7 93 1 1) v743_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v743_pg : Scalar.QComplex := ((-93086340758208711774278 : Int)/10^30,(114726256743920309088 : Int)/10^30)
theorem v743_pg_checked : Scalar.distance (sourceCoefficient 7 93 1 2) v743_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v743_mb : Scalar.QComplex := ((-904128147746786127849755 : Int)/10^30,(-431476402782572943688442133 : Int)/10^30)
theorem v743_mb_checked : Scalar.distance (sourceCoefficient 7 93 3 1) v743_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v743_mg : Scalar.QComplex := ((-93086207094317300345555 : Int)/10^30,(195055533647269219591 : Int)/10^30)
theorem v743_mg_checked : Scalar.distance (sourceCoefficient 7 93 3 2) v743_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v743_upper : Scalar.QComplex := ((999995623994248794800028484029 : Int)/10^30,(-2958376641501900677492796416 : Int)/10^30)
theorem v743_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 93 5) 1) 14) v743_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material743 : Material (7 : Basis) (93 : Basis) where
  plus := ![v743_pa,v743_pb,v743_pg]
  minus := ![(Primitive.Addresses.material743 1).one,v743_mb,v743_mg]
  upper := v743_upper
  lower := (Primitive.Addresses.material743 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v743_pa_checked.trans (by decide +kernel)
    · exact v743_pb_checked.trans (by decide +kernel)
    · exact v743_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 93 Primitive.Addresses.material743
    · exact v743_mb_checked.trans (by decide +kernel)
    · exact v743_mg_checked.trans (by decide +kernel)
  upper_error := v743_upper_checked
  lower_error := reuse_lower_error 7 93 Primitive.Addresses.material743

def v744_pa : Scalar.QComplex := ((999999184291580515536196865267 : Int)/10^30,(-1277269029448652210773291063 : Int)/10^30)
theorem v744_pa_checked : Scalar.distance (sourceCoefficient 7 94 1 0) v744_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v744_pb : Scalar.QComplex := ((-551112643254041323546758 : Int)/10^30,(-431476988011454423450541138 : Int)/10^30)
theorem v744_pb_checked : Scalar.distance (sourceCoefficient 7 94 1 1) v744_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v744_pg : Scalar.QComplex := ((-93086334438065938180915 : Int)/10^30,(118896389027426707209 : Int)/10^30)
theorem v744_pg_checked : Scalar.distance (sourceCoefficient 7 94 1 2) v744_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v744_mb : Scalar.QComplex := ((-923457645701349228545257 : Int)/10^30,(-431476351767462378080768859 : Int)/10^30)
theorem v744_mb_checked : Scalar.distance (sourceCoefficient 7 94 3 1) v744_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v744_mg : Scalar.QComplex := ((-93086197175540535150170 : Int)/10^30,(199225658924046219155 : Int)/10^30)
theorem v744_mg_checked : Scalar.distance (sourceCoefficient 7 94 3 2) v744_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v744_upper : Scalar.QComplex := ((999995490459791781929921336167 : Int)/10^30,(-3003174999976400080223808005 : Int)/10^30)
theorem v744_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 94 5) 1) 14) v744_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material744 : Material (7 : Basis) (94 : Basis) where
  plus := ![v744_pa,v744_pb,v744_pg]
  minus := ![(Primitive.Addresses.material744 1).one,v744_mb,v744_mg]
  upper := v744_upper
  lower := (Primitive.Addresses.material744 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v744_pa_checked.trans (by decide +kernel)
    · exact v744_pb_checked.trans (by decide +kernel)
    · exact v744_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 94 Primitive.Addresses.material744
    · exact v744_mb_checked.trans (by decide +kernel)
    · exact v744_mg_checked.trans (by decide +kernel)
  upper_error := v744_upper_checked
  lower_error := reuse_lower_error 7 94 Primitive.Addresses.material744

def v745_pa : Scalar.QComplex := ((999999126761383191016481312744 : Int)/10^30,(-1321543215741462293141126287 : Int)/10^30)
theorem v745_pa_checked : Scalar.distance (sourceCoefficient 7 95 1 0) v745_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v745_pb : Scalar.QComplex := ((-570215937846942973096312 : Int)/10^30,(-431476952944321411560402522 : Int)/10^30)
theorem v745_pb_checked : Scalar.distance (sourceCoefficient 7 95 1 1) v745_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v745_pg : Scalar.QComplex := ((-93086327977755431814660 : Int)/10^30,(123017712641104593770 : Int)/10^30)
theorem v745_pg_checked : Scalar.distance (sourceCoefficient 7 95 1 2) v745_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v745_mb : Scalar.QComplex := ((-942560902919864813245290 : Int)/10^30,(-431476300215059570062414861 : Int)/10^30)
theorem v745_mb_checked : Scalar.distance (sourceCoefficient 7 95 3 1) v745_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v745_mg : Scalar.QComplex := ((-93086187158715773173865 : Int)/10^30,(203346975428209965140 : Int)/10^30)
theorem v745_mg_checked : Scalar.distance (sourceCoefficient 7 95 3 2) v745_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v745_upper : Scalar.QComplex := ((999995356516451123296076195489 : Int)/10^30,(-3047449021036109007320933382 : Int)/10^30)
theorem v745_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 95 5) 1) 14) v745_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material745 : Material (7 : Basis) (95 : Basis) where
  plus := ![v745_pa,v745_pb,v745_pg]
  minus := ![(Primitive.Addresses.material745 1).one,v745_mb,v745_mg]
  upper := v745_upper
  lower := (Primitive.Addresses.material745 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v745_pa_checked.trans (by decide +kernel)
    · exact v745_pb_checked.trans (by decide +kernel)
    · exact v745_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 95 Primitive.Addresses.material745
    · exact v745_mb_checked.trans (by decide +kernel)
    · exact v745_mg_checked.trans (by decide +kernel)
  upper_error := v745_upper_checked
  lower_error := reuse_lower_error 7 95 Primitive.Addresses.material745

def v746_pa : Scalar.QComplex := ((999999098433879822166821405310 : Int)/10^30,(-1342807293521373939025222433 : Int)/10^30)
theorem v746_pa_checked : Scalar.distance (sourceCoefficient 7 96 1 0) v746_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v746_pb : Scalar.QComplex := ((-579390898605226379840589 : Int)/10^30,(-431476935701347154072360725 : Int)/10^30)
theorem v746_pb_checked : Scalar.distance (sourceCoefficient 7 96 1 1) v746_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v746_pg : Scalar.QComplex := ((-93086324799313276567994 : Int)/10^30,(124997108560775611583 : Int)/10^30)
theorem v746_pg_checked : Scalar.distance (sourceCoefficient 7 96 1 2) v746_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v746_mb : Scalar.QComplex := ((-951735845381980823779174 : Int)/10^30,(-431476275054513823416075974 : Int)/10^30)
theorem v746_mb_checked : Scalar.distance (sourceCoefficient 7 96 3 1) v746_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v746_mg : Scalar.QComplex := ((-93086182272145271413254 : Int)/10^30,(205326367868008990940 : Int)/10^30)
theorem v746_mg_checked : Scalar.distance (sourceCoefficient 7 96 3 2) v746_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v746_upper : Scalar.QComplex := ((999995291489120758874788776507 : Int)/10^30,(-3068713018254973690463872108 : Int)/10^30)
theorem v746_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 96 5) 1) 14) v746_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material746 : Material (7 : Basis) (96 : Basis) where
  plus := ![v746_pa,v746_pb,v746_pg]
  minus := ![(Primitive.Addresses.material746 1).one,v746_mb,v746_mg]
  upper := v746_upper
  lower := (Primitive.Addresses.material746 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v746_pa_checked.trans (by decide +kernel)
    · exact v746_pb_checked.trans (by decide +kernel)
    · exact v746_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 96 Primitive.Addresses.material746
    · exact v746_mb_checked.trans (by decide +kernel)
    · exact v746_mg_checked.trans (by decide +kernel)
  upper_error := v746_upper_checked
  lower_error := reuse_lower_error 7 96 Primitive.Addresses.material746

def v747_pa : Scalar.QComplex := ((999998997514759803644776311139 : Int)/10^30,(-1415969447204300957205595845 : Int)/10^30)
theorem v747_pa_checked : Scalar.distance (sourceCoefficient 7 97 1 0) v747_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v747_pb : Scalar.QComplex := ((-610958683784492799450344 : Int)/10^30,(-431476874387162392815857436 : Int)/10^30)
theorem v747_pb_checked : Scalar.distance (sourceCoefficient 7 97 1 1) v747_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v747_pg : Scalar.QComplex := ((-93086313488289398102567 : Int)/10^30,(131807507987380707368 : Int)/10^30)
theorem v747_pg_checked : Scalar.distance (sourceCoefficient 7 97 1 2) v747_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v747_mb : Scalar.QComplex := ((-983303565895738141499599 : Int)/10^30,(-431476186498775042792088067 : Int)/10^30)
theorem v747_mb_checked : Scalar.distance (sourceCoefficient 7 97 3 1) v747_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v747_mg : Scalar.QComplex := ((-93086165084057628402617 : Int)/10^30,(212136754997886952059 : Int)/10^30)
theorem v747_mg_checked : Scalar.distance (sourceCoefficient 7 97 3 2) v747_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v747_upper : Scalar.QComplex := ((999995064298911009530192967518 : Int)/10^30,(-3141874888794221187289463934 : Int)/10^30)
theorem v747_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 7 97 5) 1) 14) v747_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material747 : Material (7 : Basis) (97 : Basis) where
  plus := ![v747_pa,v747_pb,v747_pg]
  minus := ![(Primitive.Addresses.material747 1).one,v747_mb,v747_mg]
  upper := v747_upper
  lower := (Primitive.Addresses.material747 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v747_pa_checked.trans (by decide +kernel)
    · exact v747_pb_checked.trans (by decide +kernel)
    · exact v747_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 7 97 Primitive.Addresses.material747
    · exact v747_mb_checked.trans (by decide +kernel)
    · exact v747_mg_checked.trans (by decide +kernel)
  upper_error := v747_upper_checked
  lower_error := reuse_lower_error 7 97 Primitive.Addresses.material747

def v748_pa : Scalar.QComplex := ((999999977629349058241472285008 : Int)/10^30,(211521396986382991957539679 : Int)/10^30)
theorem v748_pa_checked : Scalar.distance (sourceCoefficient 8 9 1 0) v748_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v748_pb : Scalar.QComplex := ((91266728003469401822672 : Int)/10^30,(-431477511316024070143462624 : Int)/10^30)
theorem v748_pb_checked : Scalar.distance (sourceCoefficient 8 9 1 1) v748_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v748_pg : Scalar.QComplex := ((-93086427811099100930660 : Int)/10^30,(-19689771691548784933 : Int)/10^30)
theorem v748_pg_checked : Scalar.distance (sourceCoefficient 8 9 1 2) v748_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v748_mb : Scalar.QComplex := ((-281078965219311452130139 : Int)/10^30,(-431477429416302876911451794 : Int)/10^30)
theorem v748_mb_checked : Scalar.distance (sourceCoefficient 8 9 3 1) v748_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v748_mg : Scalar.QComplex := ((-93086410142153942351763 : Int)/10^30,(60639630383754317274 : Int)/10^30)
theorem v748_mg_checked : Scalar.distance (sourceCoefficient 8 9 3 2) v748_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v748_upper : Scalar.QComplex := ((999998853313592755652068511878 : Int)/10^30,(-1514388160148836908498921431 : Int)/10^30)
theorem v748_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 9 5) 1) 14) v748_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material748 : Material (8 : Basis) (9 : Basis) where
  plus := ![v748_pa,v748_pb,v748_pg]
  minus := ![(Primitive.Addresses.material748 1).one,v748_mb,v748_mg]
  upper := v748_upper
  lower := (Primitive.Addresses.material748 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v748_pa_checked.trans (by decide +kernel)
    · exact v748_pb_checked.trans (by decide +kernel)
    · exact v748_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 9 Primitive.Addresses.material748
    · exact v748_mb_checked.trans (by decide +kernel)
    · exact v748_mg_checked.trans (by decide +kernel)
  upper_error := v748_upper_checked
  lower_error := reuse_lower_error 8 9 Primitive.Addresses.material748

def v749_pa : Scalar.QComplex := ((999999985610051661857339033378 : Int)/10^30,(169646386549241622091384358 : Int)/10^30)
theorem v749_pa_checked : Scalar.distance (sourceCoefficient 8 10 1 0) v749_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v749_pb : Scalar.QComplex := ((73198602266512101139719 : Int)/10^30,(-431477514505982969405154813 : Int)/10^30)
theorem v749_pb_checked : Scalar.distance (sourceCoefficient 8 10 1 1) v749_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v749_pg : Scalar.QComplex := ((-93086428526645563405596 : Int)/10^30,(-15791776463562513012 : Int)/10^30)
theorem v749_pg_checked : Scalar.distance (sourceCoefficient 8 10 1 2) v749_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v749_mb : Scalar.QComplex := ((-299147086981470646451942 : Int)/10^30,(-431477417014281835586576128 : Int)/10^30)
theorem v749_mb_checked : Scalar.distance (sourceCoefficient 8 10 3 1) v749_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v749_mg : Scalar.QComplex := ((-93086407493905815831901 : Int)/10^30,(64537624777823188733 : Int)/10^30)
theorem v749_mg_checked : Scalar.distance (sourceCoefficient 8 10 3 2) v749_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v749_upper : Scalar.QComplex := ((999998789021814329714585582800 : Int)/10^30,(-1556263121992037906665143766 : Int)/10^30)
theorem v749_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 10 5) 1) 14) v749_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material749 : Material (8 : Basis) (10 : Basis) where
  plus := ![v749_pa,v749_pb,v749_pg]
  minus := ![(Primitive.Addresses.material749 1).one,v749_mb,v749_mg]
  upper := v749_upper
  lower := (Primitive.Addresses.material749 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v749_pa_checked.trans (by decide +kernel)
    · exact v749_pb_checked.trans (by decide +kernel)
    · exact v749_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 10 Primitive.Addresses.material749
    · exact v749_mb_checked.trans (by decide +kernel)
    · exact v749_mg_checked.trans (by decide +kernel)
  upper_error := v749_upper_checked
  lower_error := reuse_lower_error 8 10 Primitive.Addresses.material749

def v750_pa : Scalar.QComplex := ((999999987098458213164080885788 : Int)/10^30,(160633381982768630715421524 : Int)/10^30)
theorem v750_pa_checked : Scalar.distance (sourceCoefficient 8 11 1 0) v750_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v750_pb : Scalar.QComplex := ((69309693387914136913150 : Int)/10^30,(-431477515060643993887852262 : Int)/10^30)
theorem v750_pb_checked : Scalar.distance (sourceCoefficient 8 11 1 1) v750_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v750_pg : Scalar.QComplex := ((-93086428655751733284868 : Int)/10^30,(-14952788044585127829 : Int)/10^30)
theorem v750_pg_checked : Scalar.distance (sourceCoefficient 8 11 1 2) v750_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v750_mb : Scalar.QComplex := ((-303035994890697586383966 : Int)/10^30,(-431477414212989441267601910 : Int)/10^30)
theorem v750_mb_checked : Scalar.distance (sourceCoefficient 8 11 3 1) v750_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v750_mg : Scalar.QComplex := ((-93086406899002718697247 : Int)/10^30,(65376612995819651745 : Int)/10^30)
theorem v750_mg_checked : Scalar.distance (sourceCoefficient 8 11 3 2) v750_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v750_upper : Scalar.QComplex := ((999998774954590435869339350893 : Int)/10^30,(-1565276115703554018536401566 : Int)/10^30)
theorem v750_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 11 5) 1) 14) v750_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material750 : Material (8 : Basis) (11 : Basis) where
  plus := ![v750_pa,v750_pb,v750_pg]
  minus := ![(Primitive.Addresses.material750 1).one,v750_mb,v750_mg]
  upper := v750_upper
  lower := (Primitive.Addresses.material750 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v750_pa_checked.trans (by decide +kernel)
    · exact v750_pb_checked.trans (by decide +kernel)
    · exact v750_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 11 Primitive.Addresses.material750
    · exact v750_mb_checked.trans (by decide +kernel)
    · exact v750_mg_checked.trans (by decide +kernel)
  upper_error := v750_upper_checked
  lower_error := reuse_lower_error 8 11 Primitive.Addresses.material750

def v751_pa : Scalar.QComplex := ((999999987876873347378038231992 : Int)/10^30,(155712084175486276549055070 : Int)/10^30)
theorem v751_pa_checked : Scalar.distance (sourceCoefficient 8 12 1 0) v751_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v751_pb : Scalar.QComplex := ((67186264003547211865783 : Int)/10^30,(-431477515343775383880725652 : Int)/10^30)
theorem v751_pb_checked : Scalar.distance (sourceCoefficient 8 12 1 1) v751_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v751_pg : Scalar.QComplex := ((-93086428722522885237029 : Int)/10^30,(-14494682000557752654 : Int)/10^30)
theorem v751_pg_checked : Scalar.distance (sourceCoefficient 8 12 1 2) v751_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v751_mb : Scalar.QComplex := ((-305159423728744343913928 : Int)/10^30,(-431477412663696802838370225 : Int)/10^30)
theorem v751_mb_checked : Scalar.distance (sourceCoefficient 8 12 3 1) v751_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v751_mg : Scalar.QComplex := ((-93086406570448962122148 : Int)/10^30,(65834718926893707122 : Int)/10^30)
theorem v751_mg_checked : Scalar.distance (sourceCoefficient 8 12 3 2) v751_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v751_upper : Scalar.QComplex := ((999998767239290852005598757987 : Int)/10^30,(-1570197407524615289389137849 : Int)/10^30)
theorem v751_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 12 5) 1) 14) v751_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material751 : Material (8 : Basis) (12 : Basis) where
  plus := ![v751_pa,v751_pb,v751_pg]
  minus := ![(Primitive.Addresses.material751 1).one,v751_mb,v751_mg]
  upper := v751_upper
  lower := (Primitive.Addresses.material751 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v751_pa_checked.trans (by decide +kernel)
    · exact v751_pb_checked.trans (by decide +kernel)
    · exact v751_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 12 Primitive.Addresses.material751
    · exact v751_mb_checked.trans (by decide +kernel)
    · exact v751_mg_checked.trans (by decide +kernel)
  upper_error := v751_upper_checked
  lower_error := reuse_lower_error 8 12 Primitive.Addresses.material751

def v752_pa : Scalar.QComplex := ((999999994571502981217977497172 : Int)/10^30,(104196900184676631879759734 : Int)/10^30)
theorem v752_pa_checked : Scalar.distance (sourceCoefficient 8 13 1 0) v752_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v752_pb : Scalar.QComplex := ((44958620063940536631254 : Int)/10^30,(-431477517471239422546837215 : Int)/10^30)
theorem v752_pb_checked : Scalar.distance (sourceCoefficient 8 13 1 1) v752_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v752_pg : Scalar.QComplex := ((-93086429263600710055460 : Int)/10^30,(-9699317431180080815 : Int)/10^30)
theorem v752_pg_checked : Scalar.distance (sourceCoefficient 8 13 1 2) v752_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v752_mb : Scalar.QComplex := ((-327387061227888974866133 : Int)/10^30,(-431477395609704425392442032 : Int)/10^30)
theorem v752_mb_checked : Scalar.distance (sourceCoefficient 8 13 3 1) v752_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v752_mg : Scalar.QComplex := ((-93086402973342937302473 : Int)/10^30,(70630082177663784372 : Int)/10^30)
theorem v752_mg_checked : Scalar.distance (sourceCoefficient 8 13 3 2) v752_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v752_upper : Scalar.QComplex := ((999998685023376367828543107576 : Int)/10^30,(-1621712526343933194298165512 : Int)/10^30)
theorem v752_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 8 13 5) 1) 14) v752_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material752 : Material (8 : Basis) (13 : Basis) where
  plus := ![v752_pa,v752_pb,v752_pg]
  minus := ![(Primitive.Addresses.material752 1).one,v752_mb,v752_mg]
  upper := v752_upper
  lower := (Primitive.Addresses.material752 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v752_pa_checked.trans (by decide +kernel)
    · exact v752_pb_checked.trans (by decide +kernel)
    · exact v752_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 8 13 Primitive.Addresses.material752
    · exact v752_mb_checked.trans (by decide +kernel)
    · exact v752_mg_checked.trans (by decide +kernel)
  upper_error := v752_upper_checked
  lower_error := reuse_lower_error 8 13 Primitive.Addresses.material752

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
