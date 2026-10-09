import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Material
import H0mework.Versions.R9c73a630.ReleaseMaterials.SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule.LAlanine40K2025.Thermal.Recovery.Reservoir.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.Primitive.Addresses.B074

set_option autoImplicit false
set_option maxRecDepth 8192
namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
open Propagation.Interface

def v1777_pa : Scalar.QComplex := ((999999783075733713036246793458 : Int)/10^30,(-658671758554889160715786479 : Int)/10^30)
theorem v1777_pa_checked : Scalar.distance (sourceCoefficient 20 48 1 0) v1777_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1777_pb : Scalar.QComplex := ((-284202048044369519614770 : Int)/10^30,(-431477412994875409206394422 : Int)/10^30)
theorem v1777_pb_checked : Scalar.distance (sourceCoefficient 20 48 1 1) v1777_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1777_pg : Scalar.QComplex := ((-93086408150106506989110 : Int)/10^30,(61313401454153443739 : Int)/10^30)
theorem v1777_pg_checked : Scalar.distance (sourceCoefficient 20 48 1 2) v1777_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1777_mb : Scalar.QComplex := ((-656547516616242205945629 : Int)/10^30,(-431477007082547582072988917 : Int)/10^30)
theorem v1777_mb_checked : Scalar.distance (sourceCoefficient 20 48 3 1) v1777_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1777_mg : Scalar.QComplex := ((-93086320579078491844454 : Int)/10^30,(141642756401722045568 : Int)/10^30)
theorem v1777_mg_checked : Scalar.distance (sourceCoefficient 20 48 3 2) v1777_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1777_upper : Scalar.QComplex := ((999997156885824017366727678247 : Int)/10^30,(-2384579683857733631352926744 : Int)/10^30)
theorem v1777_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 48 5) 1) 14) v1777_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1777 : Material (20 : Basis) (48 : Basis) where
  plus := ![v1777_pa,v1777_pb,v1777_pg]
  minus := ![(Primitive.Addresses.material1777 1).one,v1777_mb,v1777_mg]
  upper := v1777_upper
  lower := (Primitive.Addresses.material1777 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1777_pa_checked.trans (by decide +kernel)
    · exact v1777_pb_checked.trans (by decide +kernel)
    · exact v1777_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 48 Primitive.Addresses.material1777
    · exact v1777_mb_checked.trans (by decide +kernel)
    · exact v1777_mg_checked.trans (by decide +kernel)
  upper_error := v1777_upper_checked
  lower_error := reuse_lower_error 20 48 Primitive.Addresses.material1777

def v1778_pa : Scalar.QComplex := ((999999768316827392609690856844 : Int)/10^30,(-680710137678063487837211066 : Int)/10^30)
theorem v1778_pa_checked : Scalar.distance (sourceCoefficient 20 49 1 0) v1778_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1778_pb : Scalar.QComplex := ((-293711111928236117687093 : Int)/10^30,(-431477405173040344828078689 : Int)/10^30)
theorem v1778_pb_checked : Scalar.distance (sourceCoefficient 20 49 1 1) v1778_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1778_pg : Scalar.QComplex := ((-93086406619443017988823 : Int)/10^30,(63364875346452609319 : Int)/10^30)
theorem v1778_pg_checked : Scalar.distance (sourceCoefficient 20 49 1 2) v1778_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1778_mb : Scalar.QComplex := ((-666056570209558356181433 : Int)/10^30,(-431476991054821570683581860 : Int)/10^30)
theorem v1778_mb_checked : Scalar.distance (sourceCoefficient 20 49 3 1) v1778_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1778_mg : Scalar.QComplex := ((-93086317278085998680206 : Int)/10^30,(143694228209270071574 : Int)/10^30)
theorem v1778_mg_checked : Scalar.distance (sourceCoefficient 20 49 3 2) v1778_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1778_upper : Scalar.QComplex := ((999997104090696618134876396439 : Int)/10^30,(-2406618004684797672838077467 : Int)/10^30)
theorem v1778_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 49 5) 1) 14) v1778_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1778 : Material (20 : Basis) (49 : Basis) where
  plus := ![v1778_pa,v1778_pb,v1778_pg]
  minus := ![(Primitive.Addresses.material1778 1).one,v1778_mb,v1778_mg]
  upper := v1778_upper
  lower := (Primitive.Addresses.material1778 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1778_pa_checked.trans (by decide +kernel)
    · exact v1778_pb_checked.trans (by decide +kernel)
    · exact v1778_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 49 Primitive.Addresses.material1778
    · exact v1778_mb_checked.trans (by decide +kernel)
    · exact v1778_mg_checked.trans (by decide +kernel)
  upper_error := v1778_upper_checked
  lower_error := reuse_lower_error 20 49 Primitive.Addresses.material1778

def v1779_pa : Scalar.QComplex := ((999999766560491404710198705924 : Int)/10^30,(-683285418179383826207741289 : Int)/10^30)
theorem v1779_pa_checked : Scalar.distance (sourceCoefficient 20 50 1 0) v1779_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1779_pb : Scalar.QComplex := ((-294822287414794138970501 : Int)/10^30,(-431477404240791472922618382 : Int)/10^30)
theorem v1779_pb_checked : Scalar.distance (sourceCoefficient 20 50 1 1) v1779_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1779_pg : Scalar.QComplex := ((-93086406437136381886510 : Int)/10^30,(63604598997041153445 : Int)/10^30)
theorem v1779_pg_checked : Scalar.distance (sourceCoefficient 20 50 1 2) v1779_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1779_mb : Scalar.QComplex := ((-667167744477886171066962 : Int)/10^30,(-431476989163678646483548876 : Int)/10^30)
theorem v1779_mb_checked : Scalar.distance (sourceCoefficient 20 50 3 1) v1779_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1779_mg : Scalar.QComplex := ((-93086316888908716753500 : Int)/10^30,(143933951613276128503 : Int)/10^30)
theorem v1779_mg_checked : Scalar.distance (sourceCoefficient 20 50 3 2) v1779_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1779_upper : Scalar.QComplex := ((999997097889662728434701426791 : Int)/10^30,(-2409193278319263636631730390 : Int)/10^30)
theorem v1779_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 50 5) 1) 14) v1779_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1779 : Material (20 : Basis) (50 : Basis) where
  plus := ![v1779_pa,v1779_pb,v1779_pg]
  minus := ![(Primitive.Addresses.material1779 1).one,v1779_mb,v1779_mg]
  upper := v1779_upper
  lower := (Primitive.Addresses.material1779 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1779_pa_checked.trans (by decide +kernel)
    · exact v1779_pb_checked.trans (by decide +kernel)
    · exact v1779_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 50 Primitive.Addresses.material1779
    · exact v1779_mb_checked.trans (by decide +kernel)
    · exact v1779_mg_checked.trans (by decide +kernel)
  upper_error := v1779_upper_checked
  lower_error := reuse_lower_error 20 50 Primitive.Addresses.material1779

def v1780_pa : Scalar.QComplex := ((999999758776041778040334043898 : Int)/10^30,(-694584666009062794111826340 : Int)/10^30)
theorem v1780_pa_checked : Scalar.distance (sourceCoefficient 20 51 1 0) v1780_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1780_pb : Scalar.QComplex := ((-299697658136909348112009 : Int)/10^30,(-431477400105379797765326132 : Int)/10^30)
theorem v1780_pb_checked : Scalar.distance (sourceCoefficient 20 51 1 1) v1780_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1780_pg : Scalar.QComplex := ((-93086405628738754558076 : Int)/10^30,(64656405560295724424 : Int)/10^30)
theorem v1780_pg_checked : Scalar.distance (sourceCoefficient 20 51 1 2) v1780_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1780_mb : Scalar.QComplex := ((-672043109816004021282776 : Int)/10^30,(-431476980821043156489780736 : Int)/10^30)
theorem v1780_mb_checked : Scalar.distance (sourceCoefficient 20 51 3 1) v1780_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1780_mg : Scalar.QComplex := ((-93086315172849697948846 : Int)/10^30,(144985757087284302541 : Int)/10^30)
theorem v1780_mg_checked : Scalar.distance (sourceCoefficient 20 51 3 2) v1780_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1780_upper : Scalar.QComplex := ((999997070603748001518012492079 : Int)/10^30,(-2420492495884786409238424733 : Int)/10^30)
theorem v1780_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 51 5) 1) 14) v1780_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1780 : Material (20 : Basis) (51 : Basis) where
  plus := ![v1780_pa,v1780_pb,v1780_pg]
  minus := ![(Primitive.Addresses.material1780 1).one,v1780_mb,v1780_mg]
  upper := v1780_upper
  lower := (Primitive.Addresses.material1780 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1780_pa_checked.trans (by decide +kernel)
    · exact v1780_pb_checked.trans (by decide +kernel)
    · exact v1780_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 51 Primitive.Addresses.material1780
    · exact v1780_mb_checked.trans (by decide +kernel)
    · exact v1780_mg_checked.trans (by decide +kernel)
  upper_error := v1780_upper_checked
  lower_error := reuse_lower_error 20 51 Primitive.Addresses.material1780

def v1781_pa : Scalar.QComplex := ((999999741682228299670646751075 : Int)/10^30,(-718773592080696527779405664 : Int)/10^30)
theorem v1781_pa_checked : Scalar.distance (sourceCoefficient 20 52 1 0) v1781_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1781_pb : Scalar.QComplex := ((-310134634347952998871880 : Int)/10^30,(-431477391005548517345598363 : Int)/10^30)
theorem v1781_pb_checked : Scalar.distance (sourceCoefficient 20 52 1 1) v1781_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1781_pg : Scalar.QComplex := ((-93086403851544513466095 : Int)/10^30,(66908066153791591892 : Int)/10^30)
theorem v1781_pg_checked : Scalar.distance (sourceCoefficient 20 52 1 2) v1781_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1781_mb : Scalar.QComplex := ((-682480074288139881478925 : Int)/10^30,(-431476962714574858181401920 : Int)/10^30)
theorem v1781_mb_checked : Scalar.distance (sourceCoefficient 20 52 3 1) v1781_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1781_mg : Scalar.QComplex := ((-93086311452574437429145 : Int)/10^30,(147237415308745436873 : Int)/10^30)
theorem v1781_mg_checked : Scalar.distance (sourceCoefficient 20 52 3 2) v1781_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1781_upper : Scalar.QComplex := ((999997011762067984967185627029 : Int)/10^30,(-2444681356427484865042534948 : Int)/10^30)
theorem v1781_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 52 5) 1) 14) v1781_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1781 : Material (20 : Basis) (52 : Basis) where
  plus := ![v1781_pa,v1781_pb,v1781_pg]
  minus := ![(Primitive.Addresses.material1781 1).one,v1781_mb,v1781_mg]
  upper := v1781_upper
  lower := (Primitive.Addresses.material1781 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1781_pa_checked.trans (by decide +kernel)
    · exact v1781_pb_checked.trans (by decide +kernel)
    · exact v1781_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 52 Primitive.Addresses.material1781
    · exact v1781_mb_checked.trans (by decide +kernel)
    · exact v1781_mg_checked.trans (by decide +kernel)
  upper_error := v1781_upper_checked
  lower_error := reuse_lower_error 20 52 Primitive.Addresses.material1781

def v1782_pa : Scalar.QComplex := ((999999739013977641479699072940 : Int)/10^30,(-722476280997055802536479768 : Int)/10^30)
theorem v1782_pa_checked : Scalar.distance (sourceCoefficient 20 53 1 0) v1782_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1782_pb : Scalar.QComplex := ((-311732261117931747031546 : Int)/10^30,(-431477389582896537569374617 : Int)/10^30)
theorem v1782_pb_checked : Scalar.distance (sourceCoefficient 20 53 1 1) v1782_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1782_pg : Scalar.QComplex := ((-93086403573894955051920 : Int)/10^30,(67252736217482789185 : Int)/10^30)
theorem v1782_pg_checked : Scalar.distance (sourceCoefficient 20 53 1 2) v1782_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1782_mb : Scalar.QComplex := ((-684077699235564583344848 : Int)/10^30,(-431476959913243460070514516 : Int)/10^30)
theorem v1782_mb_checked : Scalar.distance (sourceCoefficient 20 53 3 1) v1782_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1782_mg : Scalar.QComplex := ((-93086310877490240794501 : Int)/10^30,(147582085004501153214 : Int)/10^30)
theorem v1782_mg_checked : Scalar.distance (sourceCoefficient 20 53 3 2) v1782_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1782_upper : Scalar.QComplex := ((999997002703316136500594147953 : Int)/10^30,(-2448384035223965373047295387 : Int)/10^30)
theorem v1782_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 53 5) 1) 14) v1782_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1782 : Material (20 : Basis) (53 : Basis) where
  plus := ![v1782_pa,v1782_pb,v1782_pg]
  minus := ![(Primitive.Addresses.material1782 1).one,v1782_mb,v1782_mg]
  upper := v1782_upper
  lower := (Primitive.Addresses.material1782 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1782_pa_checked.trans (by decide +kernel)
    · exact v1782_pb_checked.trans (by decide +kernel)
    · exact v1782_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 53 Primitive.Addresses.material1782
    · exact v1782_mb_checked.trans (by decide +kernel)
    · exact v1782_mg_checked.trans (by decide +kernel)
  upper_error := v1782_upper_checked
  lower_error := reuse_lower_error 20 53 Primitive.Addresses.material1782

def v1783_pa : Scalar.QComplex := ((999999737652165869382541732430 : Int)/10^30,(-724358750506162411410761328 : Int)/10^30)
theorem v1783_pa_checked : Scalar.distance (sourceCoefficient 20 54 1 0) v1783_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1783_pb : Scalar.QComplex := ((-312544504259192903401867 : Int)/10^30,(-431477388856587300094319924 : Int)/10^30)
theorem v1783_pb_checked : Scalar.distance (sourceCoefficient 20 54 1 1) v1783_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1783_pg : Scalar.QComplex := ((-93086403432165326069275 : Int)/10^30,(67427968568817337672 : Int)/10^30)
theorem v1783_pg_checked : Scalar.distance (sourceCoefficient 20 54 1 2) v1783_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1783_mb : Scalar.QComplex := ((-684889941447618336691020 : Int)/10^30,(-431476958486005244198296976 : Int)/10^30)
theorem v1783_mb_checked : Scalar.distance (sourceCoefficient 20 54 3 1) v1783_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1783_mg : Scalar.QComplex := ((-93086310584543037554692 : Int)/10^30,(147757317168282402239 : Int)/10^30)
theorem v1783_mg_checked : Scalar.distance (sourceCoefficient 20 54 3 2) v1783_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1783_upper : Scalar.QComplex := ((999996998092534796243929687878 : Int)/10^30,(-2450266499578991202468595478 : Int)/10^30)
theorem v1783_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 54 5) 1) 14) v1783_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1783 : Material (20 : Basis) (54 : Basis) where
  plus := ![v1783_pa,v1783_pb,v1783_pg]
  minus := ![(Primitive.Addresses.material1783 1).one,v1783_mb,v1783_mg]
  upper := v1783_upper
  lower := (Primitive.Addresses.material1783 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1783_pa_checked.trans (by decide +kernel)
    · exact v1783_pb_checked.trans (by decide +kernel)
    · exact v1783_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 54 Primitive.Addresses.material1783
    · exact v1783_mb_checked.trans (by decide +kernel)
    · exact v1783_mg_checked.trans (by decide +kernel)
  upper_error := v1783_upper_checked
  lower_error := reuse_lower_error 20 54 Primitive.Addresses.material1783

def v1784_pa : Scalar.QComplex := ((999999726420184882410700337036 : Int)/10^30,(-739702342425156417424744689 : Int)/10^30)
theorem v1784_pa_checked : Scalar.distance (sourceCoefficient 20 55 1 0) v1784_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1784_pb : Scalar.QComplex := ((-319164918122520777179390 : Int)/10^30,(-431477382860572458350853079 : Int)/10^30)
theorem v1784_pb_checked : Scalar.distance (sourceCoefficient 20 55 1 1) v1784_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1784_pg : Scalar.QComplex := ((-93086402262606385674373 : Int)/10^30,(68856248639260096224 : Int)/10^30)
theorem v1784_pg_checked : Scalar.distance (sourceCoefficient 20 55 1 2) v1784_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1784_mb : Scalar.QComplex := ((-691510347671572803349981 : Int)/10^30,(-431476946776873643364957619 : Int)/10^30)
theorem v1784_mb_checked : Scalar.distance (sourceCoefficient 20 55 3 1) v1784_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1784_mg : Scalar.QComplex := ((-93086308182443159194364 : Int)/10^30,(149185595697634524359 : Int)/10^30)
theorem v1784_mg_checked : Scalar.distance (sourceCoefficient 20 55 3 2) v1784_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1784_upper : Scalar.QComplex := ((999996960378922845590210843537 : Int)/10^30,(-2465610049260127203900528624 : Int)/10^30)
theorem v1784_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 55 5) 1) 14) v1784_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1784 : Material (20 : Basis) (55 : Basis) where
  plus := ![v1784_pa,v1784_pb,v1784_pg]
  minus := ![(Primitive.Addresses.material1784 1).one,v1784_mb,v1784_mg]
  upper := v1784_upper
  lower := (Primitive.Addresses.material1784 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1784_pa_checked.trans (by decide +kernel)
    · exact v1784_pb_checked.trans (by decide +kernel)
    · exact v1784_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 55 Primitive.Addresses.material1784
    · exact v1784_mb_checked.trans (by decide +kernel)
    · exact v1784_mg_checked.trans (by decide +kernel)
  upper_error := v1784_upper_checked
  lower_error := reuse_lower_error 20 55 Primitive.Addresses.material1784

def v1785_pa : Scalar.QComplex := ((999999723719955359601104275145 : Int)/10^30,(-743343805348598250460553803 : Int)/10^30)
theorem v1785_pa_checked : Scalar.distance (sourceCoefficient 20 56 1 0) v1785_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1785_pb : Scalar.QComplex := ((-320736127237846701549611 : Int)/10^30,(-431477381417664320499940913 : Int)/10^30)
theorem v1785_pb_checked : Scalar.distance (sourceCoefficient 20 56 1 1) v1785_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1785_pg : Scalar.QComplex := ((-93086401981283408749724 : Int)/10^30,(69195219392234807305 : Int)/10^30)
theorem v1785_pg_checked : Scalar.distance (sourceCoefficient 20 56 1 2) v1785_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1785_mb : Scalar.QComplex := ((-693081554956701029485204 : Int)/10^30,(-431476943978083340880064277 : Int)/10^30)
theorem v1785_mb_checked : Scalar.distance (sourceCoefficient 20 56 3 1) v1785_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1785_mg : Scalar.QComplex := ((-93086307608603793877929 : Int)/10^30,(149524566081625873609 : Int)/10^30)
theorem v1785_mg_checked : Scalar.distance (sourceCoefficient 20 56 3 2) v1785_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1785_upper : Scalar.QComplex := ((999996951393862689530548694686 : Int)/10^30,(-2469251502099686575292356184 : Int)/10^30)
theorem v1785_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 56 5) 1) 14) v1785_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1785 : Material (20 : Basis) (56 : Basis) where
  plus := ![v1785_pa,v1785_pb,v1785_pg]
  minus := ![(Primitive.Addresses.material1785 1).one,v1785_mb,v1785_mg]
  upper := v1785_upper
  lower := (Primitive.Addresses.material1785 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1785_pa_checked.trans (by decide +kernel)
    · exact v1785_pb_checked.trans (by decide +kernel)
    · exact v1785_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 56 Primitive.Addresses.material1785
    · exact v1785_mb_checked.trans (by decide +kernel)
    · exact v1785_mg_checked.trans (by decide +kernel)
  upper_error := v1785_upper_checked
  lower_error := reuse_lower_error 20 56 Primitive.Addresses.material1785

def v1786_pa : Scalar.QComplex := ((999999714895599867663443338276 : Int)/10^30,(-755121658396946086763156113 : Int)/10^30)
theorem v1786_pa_checked : Scalar.distance (sourceCoefficient 20 57 1 0) v1786_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1786_pb : Scalar.QComplex := ((-325818005145497389064286 : Int)/10^30,(-431477376698520311193878953 : Int)/10^30)
theorem v1786_pb_checked : Scalar.distance (sourceCoefficient 20 57 1 1) v1786_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1786_pg : Scalar.QComplex := ((-93086401061518370984518 : Int)/10^30,(70291577584215056431 : Int)/10^30)
theorem v1786_pg_checked : Scalar.distance (sourceCoefficient 20 57 1 2) v1786_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1786_mb : Scalar.QComplex := ((-698163426899727581012707 : Int)/10^30,(-431476934873509333709011359 : Int)/10^30)
theorem v1786_mb_checked : Scalar.distance (sourceCoefficient 20 57 3 1) v1786_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1786_mg : Scalar.QComplex := ((-93086305742731357044291 : Int)/10^30,(150620923071666058905 : Int)/10^30)
theorem v1786_mg_checked : Scalar.distance (sourceCoefficient 20 57 3 2) v1786_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1786_upper : Scalar.QComplex := ((999996922242014457467496184899 : Int)/10^30,(-2481029322376268780079518071 : Int)/10^30)
theorem v1786_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 57 5) 1) 14) v1786_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1786 : Material (20 : Basis) (57 : Basis) where
  plus := ![v1786_pa,v1786_pb,v1786_pg]
  minus := ![(Primitive.Addresses.material1786 1).one,v1786_mb,v1786_mg]
  upper := v1786_upper
  lower := (Primitive.Addresses.material1786 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1786_pa_checked.trans (by decide +kernel)
    · exact v1786_pb_checked.trans (by decide +kernel)
    · exact v1786_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 57 Primitive.Addresses.material1786
    · exact v1786_mb_checked.trans (by decide +kernel)
    · exact v1786_mg_checked.trans (by decide +kernel)
  upper_error := v1786_upper_checked
  lower_error := reuse_lower_error 20 57 Primitive.Addresses.material1786

def v1787_pa : Scalar.QComplex := ((999999710049537373827002903812 : Int)/10^30,(-761512206849683544231114934 : Int)/10^30)
theorem v1787_pa_checked : Scalar.distance (sourceCoefficient 20 58 1 0) v1787_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1787_pb : Scalar.QComplex := ((-328575382630654624149649 : Int)/10^30,(-431477374104560575270458540 : Int)/10^30)
theorem v1787_pb_checked : Scalar.distance (sourceCoefficient 20 58 1 1) v1787_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1787_pg : Scalar.QComplex := ((-93086400556158200512347 : Int)/10^30,(70886450868772864230 : Int)/10^30)
theorem v1787_pg_checked : Scalar.distance (sourceCoefficient 20 58 1 2) v1787_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1787_mb : Scalar.QComplex := ((-700920801119716735505275 : Int)/10^30,(-431476929900057981616524972 : Int)/10^30)
theorem v1787_mb_checked : Scalar.distance (sourceCoefficient 20 58 3 1) v1787_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1787_mg : Scalar.QComplex := ((-93086304724022522265587 : Int)/10^30,(151215795698622289270 : Int)/10^30)
theorem v1787_mg_checked : Scalar.distance (sourceCoefficient 20 58 3 2) v1787_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1787_upper : Scalar.QComplex := ((999996906366452297873935150598 : Int)/10^30,(-2487419852947170770742679803 : Int)/10^30)
theorem v1787_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 58 5) 1) 14) v1787_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1787 : Material (20 : Basis) (58 : Basis) where
  plus := ![v1787_pa,v1787_pb,v1787_pg]
  minus := ![(Primitive.Addresses.material1787 1).one,v1787_mb,v1787_mg]
  upper := v1787_upper
  lower := (Primitive.Addresses.material1787 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1787_pa_checked.trans (by decide +kernel)
    · exact v1787_pb_checked.trans (by decide +kernel)
    · exact v1787_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 58 Primitive.Addresses.material1787
    · exact v1787_mb_checked.trans (by decide +kernel)
    · exact v1787_mg_checked.trans (by decide +kernel)
  upper_error := v1787_upper_checked
  lower_error := reuse_lower_error 20 58 Primitive.Addresses.material1787

def v1788_pa : Scalar.QComplex := ((999999696518588670831970362864 : Int)/10^30,(-779078128660642761937571390 : Int)/10^30)
theorem v1788_pa_checked : Scalar.distance (sourceCoefficient 20 59 1 0) v1788_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1788_pb : Scalar.QComplex := ((-336154681544269367832921 : Int)/10^30,(-431477366853404705669565386 : Int)/10^30)
theorem v1788_pb_checked : Scalar.distance (sourceCoefficient 20 59 1 1) v1788_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1788_pg : Scalar.QComplex := ((-93086399144206620245171 : Int)/10^30,(72521599657983567629 : Int)/10^30)
theorem v1788_pg_checked : Scalar.distance (sourceCoefficient 20 59 1 2) v1788_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1788_mb : Scalar.QComplex := ((-708500090953791167048938 : Int)/10^30,(-431476916108311208454061760 : Int)/10^30)
theorem v1788_mb_checked : Scalar.distance (sourceCoefficient 20 59 3 1) v1788_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1788_mg : Scalar.QComplex := ((-93086301901011707011334 : Int)/10^30,(152850942660541746623 : Int)/10^30)
theorem v1788_mg_checked : Scalar.distance (sourceCoefficient 20 59 3 2) v1788_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1788_upper : Scalar.QComplex := ((999996862518336269900349385333 : Int)/10^30,(-2504985725242562945857983833 : Int)/10^30)
theorem v1788_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 59 5) 1) 14) v1788_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1788 : Material (20 : Basis) (59 : Basis) where
  plus := ![v1788_pa,v1788_pb,v1788_pg]
  minus := ![(Primitive.Addresses.material1788 1).one,v1788_mb,v1788_mg]
  upper := v1788_upper
  lower := (Primitive.Addresses.material1788 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1788_pa_checked.trans (by decide +kernel)
    · exact v1788_pb_checked.trans (by decide +kernel)
    · exact v1788_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 59 Primitive.Addresses.material1788
    · exact v1788_mb_checked.trans (by decide +kernel)
    · exact v1788_mg_checked.trans (by decide +kernel)
  upper_error := v1788_upper_checked
  lower_error := reuse_lower_error 20 59 Primitive.Addresses.material1788

def v1789_pa : Scalar.QComplex := ((999999680526090481075897488260 : Int)/10^30,(-799342052549638690481202061 : Int)/10^30)
theorem v1789_pa_checked : Scalar.distance (sourceCoefficient 20 60 1 0) v1789_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1789_pb : Scalar.QComplex := ((-344898107372596718586045 : Int)/10^30,(-431477358268013804451003341 : Int)/10^30)
theorem v1789_pb_checked : Scalar.distance (sourceCoefficient 20 60 1 1) v1789_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1789_pg : Scalar.QComplex := ((-93086397473763500278706 : Int)/10^30,(74407895792510985995 : Int)/10^30)
theorem v1789_pg_checked : Scalar.distance (sourceCoefficient 20 60 1 2) v1789_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1789_mb : Scalar.QComplex := ((-717243506117735811515722 : Int)/10^30,(-431476899977740803403562902 : Int)/10^30)
theorem v1789_mb_checked : Scalar.distance (sourceCoefficient 20 60 3 1) v1789_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1789_mg : Scalar.QComplex := ((-93086298602780600554222 : Int)/10^30,(154737236651197727546 : Int)/10^30)
theorem v1789_mg_checked : Scalar.distance (sourceCoefficient 20 60 3 2) v1789_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1789_upper : Scalar.QComplex := ((999996811552167595499719758265 : Int)/10^30,(-2525249591349223562037437876 : Int)/10^30)
theorem v1789_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 60 5) 1) 14) v1789_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1789 : Material (20 : Basis) (60 : Basis) where
  plus := ![v1789_pa,v1789_pb,v1789_pg]
  minus := ![(Primitive.Addresses.material1789 1).one,v1789_mb,v1789_mg]
  upper := v1789_upper
  lower := (Primitive.Addresses.material1789 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1789_pa_checked.trans (by decide +kernel)
    · exact v1789_pb_checked.trans (by decide +kernel)
    · exact v1789_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 60 Primitive.Addresses.material1789
    · exact v1789_mb_checked.trans (by decide +kernel)
    · exact v1789_mg_checked.trans (by decide +kernel)
  upper_error := v1789_upper_checked
  lower_error := reuse_lower_error 20 60 Primitive.Addresses.material1789

def v1790_pa : Scalar.QComplex := ((999999675825311245761769794288 : Int)/10^30,(-805201386250202398087769964 : Int)/10^30)
theorem v1790_pa_checked : Scalar.distance (sourceCoefficient 20 61 1 0) v1790_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1790_pb : Scalar.QComplex := ((-347426277605441073785812 : Int)/10^30,(-431477355741510108219422117 : Int)/10^30)
theorem v1790_pb_checked : Scalar.distance (sourceCoefficient 20 61 1 1) v1790_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1790_pg : Scalar.QComplex := ((-93086396982441721181419 : Int)/10^30,(74953320189267974767 : Int)/10^30)
theorem v1790_pg_checked : Scalar.distance (sourceCoefficient 20 61 1 2) v1790_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1790_mb : Scalar.QComplex := ((-719771673228967945594509 : Int)/10^30,(-431476895269541001520532312 : Int)/10^30)
theorem v1790_mb_checked : Scalar.distance (sourceCoefficient 20 61 3 1) v1790_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1790_mg : Scalar.QComplex := ((-93086297640782315000141 : Int)/10^30,(155282660420879719230 : Int)/10^30)
theorem v1790_mg_checked : Scalar.distance (sourceCoefficient 20 61 3 2) v1790_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1790_upper : Scalar.QComplex := ((999996796738716948872149883881 : Int)/10^30,(-2531108908209879499549051976 : Int)/10^30)
theorem v1790_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 61 5) 1) 14) v1790_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1790 : Material (20 : Basis) (61 : Basis) where
  plus := ![v1790_pa,v1790_pb,v1790_pg]
  minus := ![(Primitive.Addresses.material1790 1).one,v1790_mb,v1790_mg]
  upper := v1790_upper
  lower := (Primitive.Addresses.material1790 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1790_pa_checked.trans (by decide +kernel)
    · exact v1790_pb_checked.trans (by decide +kernel)
    · exact v1790_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 61 Primitive.Addresses.material1790
    · exact v1790_mb_checked.trans (by decide +kernel)
    · exact v1790_mg_checked.trans (by decide +kernel)
  upper_error := v1790_upper_checked
  lower_error := reuse_lower_error 20 61 Primitive.Addresses.material1790

def v1791_pa : Scalar.QComplex := ((999999668934100695893020239003 : Int)/10^30,(-813714746704018064451575259 : Int)/10^30)
theorem v1791_pa_checked : Scalar.distance (sourceCoefficient 20 62 1 0) v1791_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1791_pb : Scalar.QComplex := ((-351099600457120341625608 : Int)/10^30,(-431477352035411584813224627 : Int)/10^30)
theorem v1791_pb_checked : Scalar.distance (sourceCoefficient 20 62 1 1) v1791_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1791_pg : Scalar.QComplex := ((-93086396261928057623239 : Int)/10^30,(75745798432715520037 : Int)/10^30)
theorem v1791_pg_checked : Scalar.distance (sourceCoefficient 20 62 1 2) v1791_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1791_mb : Scalar.QComplex := ((-723444991514705127388108 : Int)/10^30,(-431476888393531677384790293 : Int)/10^30)
theorem v1791_mb_checked : Scalar.distance (sourceCoefficient 20 62 3 1) v1791_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1791_mg : Scalar.QComplex := ((-93086296236395887522036 : Int)/10^30,(156075137747480555499 : Int)/10^30)
theorem v1791_mg_checked : Scalar.distance (sourceCoefficient 20 62 3 2) v1791_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1791_upper : Scalar.QComplex := ((999996775154228845393466076594 : Int)/10^30,(-2539622244090440576187073700 : Int)/10^30)
theorem v1791_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 62 5) 1) 14) v1791_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1791 : Material (20 : Basis) (62 : Basis) where
  plus := ![v1791_pa,v1791_pb,v1791_pg]
  minus := ![(Primitive.Addresses.material1791 1).one,v1791_mb,v1791_mg]
  upper := v1791_upper
  lower := (Primitive.Addresses.material1791 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1791_pa_checked.trans (by decide +kernel)
    · exact v1791_pb_checked.trans (by decide +kernel)
    · exact v1791_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 62 Primitive.Addresses.material1791
    · exact v1791_mb_checked.trans (by decide +kernel)
    · exact v1791_mg_checked.trans (by decide +kernel)
  upper_error := v1791_upper_checked
  lower_error := reuse_lower_error 20 62 Primitive.Addresses.material1791

def v1792_pa : Scalar.QComplex := ((999999648450501886946737790722 : Int)/10^30,(-838509912069652818173284565 : Int)/10^30)
theorem v1792_pa_checked : Scalar.distance (sourceCoefficient 20 63 1 0) v1792_pa ≤ (1/10^30 : ℚ) := by decide +kernel
def v1792_pb : Scalar.QComplex := ((-361798154455128206683558 : Int)/10^30,(-431477341003829394178324577 : Int)/10^30)
theorem v1792_pb_checked : Scalar.distance (sourceCoefficient 20 63 1 1) v1792_pb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1792_pg : Scalar.QComplex := ((-93086394118585525090140 : Int)/10^30,(78053891587062609094 : Int)/10^30)
theorem v1792_pg_checked : Scalar.distance (sourceCoefficient 20 63 1 2) v1792_pg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1792_mb : Scalar.QComplex := ((-734143532009393804415727 : Int)/10^30,(-431476868129583339016464127 : Int)/10^30)
theorem v1792_mb_checked : Scalar.distance (sourceCoefficient 20 63 3 1) v1792_mb ≤ (1/10^30 : ℚ) := by decide +kernel
def v1792_mg : Scalar.QComplex := ((-93086292101273713508547 : Int)/10^30,(158383228192811005113 : Int)/10^30)
theorem v1792_mg_checked : Scalar.distance (sourceCoefficient 20 63 3 2) v1792_mg ≤ (1/10^30 : ℚ) := by decide +kernel
def v1792_upper : Scalar.QComplex := ((999996711876454523106475284923 : Int)/10^30,(-2564417337173755875848550081 : Int)/10^30)
theorem v1792_upper_checked : Scalar.distance (Scalar.polynomial (Primitive.scalarSeed (sourceSum 20 63 5) 1) 14) v1792_upper ≤ (1/10^30 : ℚ) := by decide +kernel

def material1792 : Material (20 : Basis) (63 : Basis) where
  plus := ![v1792_pa,v1792_pb,v1792_pg]
  minus := ![(Primitive.Addresses.material1792 1).one,v1792_mb,v1792_mg]
  upper := v1792_upper
  lower := (Primitive.Addresses.material1792 0).one
  plus_error := by
    intro k
    fin_cases k
    · exact v1792_pa_checked.trans (by decide +kernel)
    · exact v1792_pb_checked.trans (by decide +kernel)
    · exact v1792_pg_checked.trans (by decide +kernel)
  minus_error := by
    intro k
    fin_cases k
    · exact reuse_minus_zero_error 20 63 Primitive.Addresses.material1792
    · exact v1792_mb_checked.trans (by decide +kernel)
    · exact v1792_mg_checked.trans (by decide +kernel)
  upper_error := v1792_upper_checked
  lower_error := reuse_lower_error 20 63 Primitive.Addresses.material1792

end LAlanine40K2025.Thermal.Recovery.Reservoir.Pointer.Feedback.Renewal.Direction.Blocks.EnergyFrame.Inverse.Scaled.Finite.Evaluation.LoadPrimitive.Values
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
