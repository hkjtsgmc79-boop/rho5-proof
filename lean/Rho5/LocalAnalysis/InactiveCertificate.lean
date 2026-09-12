import Rho5.LocalAnalysis.Inactive.Row00
import Rho5.LocalAnalysis.Inactive.Row01
import Rho5.LocalAnalysis.Inactive.Row02
import Rho5.LocalAnalysis.Inactive.Row03
import Rho5.LocalAnalysis.Inactive.Row04
import Rho5.LocalAnalysis.Inactive.Row05
import Rho5.LocalAnalysis.Inactive.Row06
import Rho5.LocalAnalysis.Inactive.Row07
import Rho5.LocalAnalysis.Inactive.Row08
import Rho5.LocalAnalysis.Inactive.Row09
import Rho5.LocalAnalysis.Inactive.Row10
import Rho5.LocalAnalysis.Inactive.Row11
import Rho5.LocalAnalysis.Inactive.Row12
import Rho5.LocalAnalysis.Inactive.Row13
import Rho5.LocalAnalysis.Inactive.Row14
import Rho5.LocalAnalysis.Inactive.Row15
import Rho5.LocalAnalysis.Inactive.Row16
import Rho5.LocalAnalysis.Inactive.Row17
import Rho5.LocalAnalysis.Inactive.Row18
import Rho5.LocalAnalysis.Inactive.Row19
import Rho5.LocalAnalysis.Inactive.Row20
import Rho5.LocalAnalysis.Inactive.Row21
import Rho5.LocalAnalysis.Inactive.Row22
import Rho5.LocalAnalysis.Inactive.Row23
import Rho5.LocalAnalysis.Inactive.Row24
import Rho5.LocalAnalysis.Inactive.Row25
import Rho5.LocalAnalysis.Inactive.Row26
import Rho5.LocalAnalysis.Inactive.Row27
import Rho5.LocalAnalysis.Inactive.Row28
import Rho5.LocalAnalysis.Inactive.Row29
import Rho5.LocalAnalysis.Inactive.Row30
import Rho5.LocalAnalysis.Inactive.Row31
import Rho5.LocalAnalysis.Inactive.Row32
import Rho5.LocalAnalysis.Inactive.Row33
import Rho5.LocalAnalysis.Inactive.Row34
import Rho5.LocalAnalysis.Inactive.Row35
import Rho5.LocalAnalysis.Inactive.Row36
import Rho5.LocalAnalysis.Inactive.Row37
import Rho5.LocalAnalysis.Inactive.Row38
import Rho5.LocalAnalysis.Inactive.Row39
import Rho5.LocalAnalysis.Inactive.Row40
import Rho5.LocalAnalysis.Inactive.Row41
import Rho5.LocalAnalysis.Inactive.Row42
import Rho5.LocalAnalysis.Inactive.Row43
import Rho5.LocalAnalysis.Inactive.Row44
import Rho5.LocalAnalysis.Inactive.Row45
import Rho5.LocalAnalysis.Inactive.Row46
import Rho5.LocalAnalysis.Inactive.Row47
import Rho5.LocalAnalysis.Inactive.Row48
import Rho5.LocalAnalysis.Inactive.Row49
import Rho5.LocalAnalysis.Inactive.Row50
import Rho5.LocalAnalysis.Inactive.Row51
import Rho5.LocalAnalysis.Inactive.Row52
import Rho5.LocalAnalysis.Inactive.Row53
import Rho5.LocalAnalysis.Inactive.Row54
import Rho5.LocalAnalysis.Inactive.Row55
import Rho5.LocalAnalysis.Inactive.Row56
import Rho5.LocalAnalysis.Inactive.Row57
import Rho5.LocalAnalysis.Inactive.Row58
import Rho5.LocalAnalysis.Inactive.Row59
import Rho5.LocalAnalysis.Inactive.Row60
import Rho5.LocalAnalysis.Inactive.Row61
import Rho5.LocalAnalysis.Inactive.Row62
import Rho5.LocalAnalysis.Inactive.Row63
import Rho5.LocalAnalysis.Inactive.Row64
import Rho5.LocalAnalysis.Inactive.Row65
import Rho5.LocalAnalysis.Inactive.Row66
import Rho5.LocalAnalysis.Inactive.Row67
import Rho5.LocalAnalysis.Inactive.Row68
import Rho5.LocalAnalysis.Inactive.Row69
import Rho5.LocalAnalysis.Inactive.Row70
import Rho5.LocalAnalysis.Inactive.Row71
import Rho5.LocalAnalysis.Inactive.Row72
import Rho5.LocalAnalysis.Inactive.Row73
import Rho5.LocalAnalysis.Inactive.Row74
import Rho5.LocalAnalysis.Inactive.Row75
import Rho5.LocalAnalysis.Inactive.Row76
import Rho5.LocalAnalysis.Inactive.Row77

namespace Rho5.LocalAnalysis.V43
noncomputable section
set_option maxRecDepth 10000

/-- All 78 actual frozen inequalities are strictly positive on the whole cube. -/
theorem inactiveBox_verified : InactiveBox := by
  intro z hz i
  fin_cases i
  · exact inactive_00 z hz
  · exact inactive_01 z hz
  · exact inactive_02 z hz
  · exact inactive_03 z hz
  · exact inactive_04 z hz
  · exact inactive_05 z hz
  · exact inactive_06 z hz
  · exact inactive_07 z hz
  · exact inactive_08 z hz
  · exact inactive_09 z hz
  · exact inactive_10 z hz
  · exact inactive_11 z hz
  · exact inactive_12 z hz
  · exact inactive_13 z hz
  · exact inactive_14 z hz
  · exact inactive_15 z hz
  · exact inactive_16 z hz
  · exact inactive_17 z hz
  · exact inactive_18 z hz
  · exact inactive_19 z hz
  · exact inactive_20 z hz
  · exact inactive_21 z hz
  · exact inactive_22 z hz
  · exact inactive_23 z hz
  · exact inactive_24 z hz
  · exact inactive_25 z hz
  · exact inactive_26 z hz
  · exact inactive_27 z hz
  · exact inactive_28 z hz
  · exact inactive_29 z hz
  · exact inactive_30 z hz
  · exact inactive_31 z hz
  · exact inactive_32 z hz
  · exact inactive_33 z hz
  · exact inactive_34 z hz
  · exact inactive_35 z hz
  · exact inactive_36 z hz
  · exact inactive_37 z hz
  · exact inactive_38 z hz
  · exact inactive_39 z hz
  · exact inactive_40 z hz
  · exact inactive_41 z hz
  · exact inactive_42 z hz
  · exact inactive_43 z hz
  · exact inactive_44 z hz
  · exact inactive_45 z hz
  · exact inactive_46 z hz
  · exact inactive_47 z hz
  · exact inactive_48 z hz
  · exact inactive_49 z hz
  · exact inactive_50 z hz
  · exact inactive_51 z hz
  · exact inactive_52 z hz
  · exact inactive_53 z hz
  · exact inactive_54 z hz
  · exact inactive_55 z hz
  · exact inactive_56 z hz
  · exact inactive_57 z hz
  · exact inactive_58 z hz
  · exact inactive_59 z hz
  · exact inactive_60 z hz
  · exact inactive_61 z hz
  · exact inactive_62 z hz
  · exact inactive_63 z hz
  · exact inactive_64 z hz
  · exact inactive_65 z hz
  · exact inactive_66 z hz
  · exact inactive_67 z hz
  · exact inactive_68 z hz
  · exact inactive_69 z hz
  · exact inactive_70 z hz
  · exact inactive_71 z hz
  · exact inactive_72 z hz
  · exact inactive_73 z hz
  · exact inactive_74 z hz
  · exact inactive_75 z hz
  · exact inactive_76 z hz
  · exact inactive_77 z hz

end
end Rho5.LocalAnalysis.V43
