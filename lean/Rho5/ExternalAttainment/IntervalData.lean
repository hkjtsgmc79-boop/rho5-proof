import Rho5.ExternalAttainment.Formulas
import Rho5.ExternalAttainment.Box

/-! Generated finite exact interval proofs. See tools/generate.py.
Python chooses outward endpoints only. Lean proves every enclosure and all
rational side conditions. This file does not use a Boolean external checker. -/
noncomputable section
namespace Rho5.ExternalAttainment

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

structure Numerics (x y z : ℝ) : Prop where
  denomT_bound : Bounds ((-412997:ℝ)/500000) ((-825993:ℝ)/1000000) (denomT x y z)
  denomR_bound : Bounds ((-804157:ℝ)/1000000) ((-201039:ℝ)/250000) (denomR x y z)
  corePivot_bound : Bounds ((518617:ℝ)/250000) ((2074469:ℝ)/1000000) (corePivot x y z)
  pivotTwo_bound : Bounds ((181653:ℝ)/125000) ((58129:ℝ)/40000) (pivotTwo x y z)
  headEntry_bound : Bounds ((-319057:ℝ)/500000) ((-638113:ℝ)/1000000) (headEntry x y z)
  ratioRD_bound : Bounds ((973563:ℝ)/1000000) ((243391:ℝ)/250000) (ratioRD x y z)
  topRight_bound : Bounds ((-97353:ℝ)/500000) ((-38941:ℝ)/200000) (topRight x y z)
  halfHeight_bound : Bounds ((1033129:ℝ)/500000) ((2066259:ℝ)/1000000) (halfHeight x y z)
  coreArm_bound : Bounds ((-5417:ℝ)/31250) ((-173343:ℝ)/1000000) (coreArm x y z)
  coreBottom_bound : Bounds ((393:ℝ)/4000) ((98251:ℝ)/1000000) (coreBottom x y z)
  coreCorner_bound : Bounds ((246001:ℝ)/125000) ((1968009:ℝ)/1000000) (coreCorner x y z)
  reducedT_bound : Bounds ((127131:ℝ)/200000) ((79457:ℝ)/125000) (reducedT x y z)
  reducedB23_bound : Bounds ((-997327:ℝ)/1000000) ((-498663:ℝ)/500000) (reducedB23 x y z)
  reducedB33_bound : Bounds ((106833:ℝ)/125000) ((170933:ℝ)/200000) (reducedB33 x y z)
  yMinusT_bound : Bounds ((-1414807:ℝ)/1000000) ((-707403:ℝ)/500000) (yMinusT x y z)
  xPlusOne_bound : Bounds ((382467:ℝ)/1000000) ((95617:ℝ)/250000) (xPlusOne x y z)
  a02_bound : Bounds ((58169:ℝ)/100000) ((581691:ℝ)/1000000) ((-z) / y)
  a03_bound : Bounds ((-18129:ℝ)/40000) ((-56653:ℝ)/125000) (-z)
  a04_bound : Bounds ((-97353:ℝ)/500000) ((-38941:ℝ)/200000) (topRight x y z)
  a10_bound : Bounds ((-617533:ℝ)/1000000) ((-154383:ℝ)/250000) x
  a11_bound : Bounds ((208923:ℝ)/250000) ((835693:ℝ)/1000000) ((x + z) + (1:ℝ))
  a12_bound : Bounds ((-997327:ℝ)/1000000) ((-498663:ℝ)/500000) (reducedB23 x y z)
  a21_bound : Bounds ((56653:ℝ)/125000) ((18129:ℝ)/40000) z
  a22_bound : Bounds ((106833:ℝ)/125000) ((170933:ℝ)/200000) (reducedB33 x y z)
  a30_bound : Bounds ((-779151:ℝ)/1000000) ((-15583:ℝ)/20000) y
  a31_bound : Bounds ((127131:ℝ)/200000) ((79457:ℝ)/125000) (reducedT x y z)
  a40_bound : Bounds ((56653:ℝ)/125000) ((18129:ℝ)/40000) z
  f01_bound : Bounds ((-319057:ℝ)/500000) ((-638113:ℝ)/1000000) (headEntry x y z)
  f02_bound : Bounds ((-639941:ℝ)/500000) ((-1279881:ℝ)/1000000) ((x * z) - (1:ℝ))
  f03_bound : Bounds ((879763:ℝ)/1000000) ((219941:ℝ)/250000) ((1:ℝ) - (x * (topRight x y z)))
  f11_bound : Bounds ((287271:ℝ)/200000) ((359089:ℝ)/250000) ((corePivot x y z) + (headEntry x y z))
  f13_bound : Bounds ((-597353:ℝ)/500000) ((-238941:ℝ)/200000) ((topRight x y z) - (1:ℝ))
  f20_bound : Bounds ((707403:ℝ)/500000) ((1414807:ℝ)/1000000) ((pivotTwo x y z) * (ratioRD x y z))
  f22_bound : Bounds ((646869:ℝ)/1000000) ((64687:ℝ)/100000) ((1:ℝ) + (y * z))
  f23_bound : Bounds ((169659:ℝ)/200000) ((106037:ℝ)/125000) ((1:ℝ) - (y * (topRight x y z)))
  f31_bound : Bounds ((736363:ℝ)/1000000) ((184091:ℝ)/250000) ((1:ℝ) + ((z ^ 2) / y))
  f32_bound : Bounds ((-198647:ℝ)/250000) ((-794587:ℝ)/1000000) ((z ^ 2) - (1:ℝ))
  f33_bound : Bounds ((217649:ℝ)/200000) ((544123:ℝ)/500000) ((1:ℝ) - (z * (topRight x y z)))
  g01_bound : Bounds ((-5417:ℝ)/31250) ((-173343:ℝ)/1000000) (coreArm x y z)
  g11_bound : Bounds ((946457:ℝ)/500000) ((378583:ℝ)/200000) ((halfHeight x y z) + (coreArm x y z))
  g12_bound : Bounds ((-821:ℝ)/100000) ((-8209:ℝ)/1000000) ((halfHeight x y z) - (corePivot x y z))
  g20_bound : Bounds ((393:ℝ)/4000) ((98251:ℝ)/1000000) (coreBottom x y z)
  g22_bound : Bounds ((246001:ℝ)/125000) ((1968009:ℝ)/1000000) (coreCorner x y z)

theorem numerics_of_candidateBox {x y z g : ℝ}
    (box : Rho5.Algebraic.CandidateBox x y z g) : Numerics x y z := by
  have nb := narrowBox_of_candidateBox box
  have hx := nb.xb
  have hy := nb.yb
  have hz := nb.zb
  have iv008 : Bounds (2:ℝ) (2:ℝ) (2:ℝ) := by norm_num [Bounds]

  have iv009 : Bounds ((381346605927:ℝ)/1000000000000) ((381346607163:ℝ)/1000000000000) (x ^ 2) := by
    have hm : Bounds ((381346605927:ℝ)/1000000000000) ((381346607163:ℝ)/1000000000000) (x * x) :=
      Bounds.mul hx hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [pow_two] using hm

  have iv007 : Bounds ((381346605927:ℝ)/500000000000) ((381346607163:ℝ)/500000000000) ((2:ℝ) * (x ^ 2)) := Bounds.mul iv008 iv009 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv006 : Bounds ((345671561537:ℝ)/1000000000000) ((345671563421:ℝ)/1000000000000) (((2:ℝ) * (x ^ 2)) * z) := Bounds.mul iv007 hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv011 : Bounds ((102706409069:ℝ)/500000000000) ((41082563809:ℝ)/200000000000) (z ^ 2) := by
    have hm : Bounds ((102706409069:ℝ)/500000000000) ((41082563809:ℝ)/200000000000) (z * z) :=
      Bounds.mul hz hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [pow_two] using hm

  have iv010 : Bounds ((-25369825607:ℝ)/200000000000) ((-126849127269:ℝ)/1000000000000) (x * (z ^ 2)) := Bounds.mul hx iv011 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv005 : Bounds ((109411216751:ℝ)/500000000000) ((27352804519:ℝ)/125000000000) ((((2:ℝ) * (x ^ 2)) * z) + (x * (z ^ 2))) := Bounds.add iv006 iv010 (by norm_num) (by norm_num)

  have iv012 : Bounds ((-69970297989:ℝ)/250000000000) ((-69970297721:ℝ)/250000000000) (x * z) := Bounds.mul hx hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv004 : Bounds ((-30529379227:ℝ)/500000000000) ((-15264688683:ℝ)/250000000000) (((((2:ℝ) * (x ^ 2)) * z) + (x * (z ^ 2))) + (x * z)) := Bounds.add iv005 iv012 (by norm_num) (by norm_num)

  have iv013 : Bounds ((-617532677:ℝ)/500000000) ((-154383169:ℝ)/125000000) ((2:ℝ) * x) := Bounds.mul iv008 hx (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv003 : Bounds ((587003296773:ℝ)/500000000000) ((293501649817:ℝ)/250000000000) ((((((2:ℝ) * (x ^ 2)) * z) + (x * (z ^ 2))) + (x * z)) - ((2:ℝ) * x)) := Bounds.sub iv004 iv013 (by norm_num) (by norm_num)

  have iv002 : Bounds ((-412996703227:ℝ)/500000000000) ((-206498350183:ℝ)/250000000000) (((((((2:ℝ) * (x ^ 2)) * z) + (x * (z ^ 2))) + (x * z)) - ((2:ℝ) * x)) - (2:ℝ)) := Bounds.sub iv003 iv008 (by norm_num) (by norm_num)

  have iv001 : Bounds ((-412996703227:ℝ)/500000000000) ((-206498350183:ℝ)/250000000000) (denomT x y z) := by
    simpa only [denomT] using iv002

  have iv019 : Bounds ((-156368089:ℝ)/200000000) ((-390920221:ℝ)/500000000) (((2:ℝ) * x) + z) := Bounds.add iv013 hz (by norm_num) (by norm_num)

  have iv020 : Bounds (1:ℝ) (1:ℝ) (1:ℝ) := by norm_num [Bounds]

  have iv018 : Bounds ((43631911:ℝ)/200000000) ((109079779:ℝ)/500000000) ((((2:ℝ) * x) + z) + (1:ℝ)) := Bounds.add iv019 iv020 (by norm_num) (by norm_num)

  have iv017 : Bounds ((49437672231:ℝ)/500000000000) ((98875346041:ℝ)/1000000000000) (z * ((((2:ℝ) * x) + z) + (1:ℝ))) := Bounds.mul hz iv018 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv021 : Bounds ((220849257:ℝ)/1000000000) ((110424629:ℝ)/500000000) (y + (1:ℝ)) := Bounds.add hy iv020 (by norm_num) (by norm_num)

  have iv016 : Bounds ((545913659:ℝ)/25000000000) ((2729568351:ℝ)/125000000000) ((z * ((((2:ℝ) * x) + z) + (1:ℝ))) * (y + (1:ℝ))) := Bounds.mul iv017 iv021 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv015 : Bounds ((-402078430047:ℝ)/500000000000) ((-201039213481:ℝ)/250000000000) ((denomT x y z) + ((z * ((((2:ℝ) * x) + z) + (1:ℝ))) * (y + (1:ℝ)))) := Bounds.add iv001 iv016 (by norm_num) (by norm_num)

  have iv014 : Bounds ((-402078430047:ℝ)/500000000000) ((-201039213481:ℝ)/250000000000) (denomR x y z) := by
    simpa only [denomR] using iv015

  have iv024 : Bounds ((569970297721:ℝ)/250000000000) ((569970297989:ℝ)/250000000000) ((2:ℝ) - (x * z)) := Bounds.sub iv008 iv012 (by norm_num) (by norm_num)

  have iv023 : Bounds ((2074468371839:ℝ)/1000000000000) ((1037234186909:ℝ)/500000000000) (((2:ℝ) - (x * z)) - (z ^ 2)) := Bounds.sub iv024 iv011 (by norm_num) (by norm_num)

  have iv022 : Bounds ((2074468371839:ℝ)/1000000000000) ((1037234186909:ℝ)/500000000000) (corePivot x y z) := by
    simpa only [corePivot] using iv023

  have iv026 : Bounds ((1453224909:ℝ)/1000000000) ((145322491:ℝ)/100000000) ((1:ℝ) + z) := Bounds.add iv020 hz (by norm_num) (by norm_num)

  have iv025 : Bounds ((1453224909:ℝ)/1000000000) ((145322491:ℝ)/100000000) (pivotTwo x y z) := by
    simpa only [pivotTwo] using iv026

  have iv032 : Bounds ((-37234186909:ℝ)/500000000000) ((-74468371839:ℝ)/1000000000000) ((x * z) + (z ^ 2)) := Bounds.add iv012 iv011 (by norm_num) (by norm_num)

  have iv031 : Bounds ((189378267591:ℝ)/500000000000) ((378756538161:ℝ)/1000000000000) (((x * z) + (z ^ 2)) + z) := Bounds.add iv032 hz (by norm_num) (by norm_num)

  have iv030 : Bounds ((-310621732409:ℝ)/500000000000) ((-621243461839:ℝ)/1000000000000) ((((x * z) + (z ^ 2)) + z) - (1:ℝ)) := Bounds.sub iv031 iv020 (by norm_num) (by norm_num)

  have iv029 : Bounds ((256571499863:ℝ)/500000000000) ((513143005743:ℝ)/1000000000000) (((((x * z) + (z ^ 2)) + z) - (1:ℝ)) * (denomT x y z)) := Bounds.mul iv030 iv001 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv028 : Bounds ((-638113078611:ℝ)/1000000000000) ((-638113066231:ℝ)/1000000000000) ((((((x * z) + (z ^ 2)) + z) - (1:ℝ)) * (denomT x y z)) / (denomR x y z)) := by
    have hr : Bounds ((-248707698037:ℝ)/200000000000) ((-1243538480643:ℝ)/1000000000000) (1 / (denomR x y z)) :=
      Bounds.recip_neg iv014 (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((-638113078611:ℝ)/1000000000000) ((-638113066231:ℝ)/1000000000000) ((((((x * z) + (z ^ 2)) + z) - (1:ℝ)) * (denomT x y z)) * (1 / (denomR x y z))) :=
      Bounds.mul iv029 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv027 : Bounds ((-638113078611:ℝ)/1000000000000) ((-638113066231:ℝ)/1000000000000) (headEntry x y z) := by
    simpa only [headEntry] using iv028

  have iv034 : Bounds ((486781642347:ℝ)/500000000000) ((97356329891:ℝ)/100000000000) ((denomR x y z) / (denomT x y z)) := by
    have hr : Bounds ((-2364577003:ℝ)/1953125000) ((-302665854287:ℝ)/250000000000) (1 / (denomT x y z)) :=
      Bounds.recip_neg iv001 (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((486781642347:ℝ)/500000000000) ((97356329891:ℝ)/100000000000) ((denomR x y z) * (1 / (denomT x y z))) :=
      Bounds.mul iv014 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv033 : Bounds ((486781642347:ℝ)/500000000000) ((97356329891:ℝ)/100000000000) (ratioRD x y z) := by
    simpa only [ratioRD] using iv034

  have iv038 : Bounds ((-20538471:ℝ)/125000000) ((-82153883:ℝ)/500000000) (x + z) := Bounds.add hx hz (by norm_num) (by norm_num)

  have iv037 : Bounds ((-14893674673:ℝ)/200000000000) ((-74468372293:ℝ)/1000000000000) (z * (x + z)) := Bounds.mul hz iv038 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv039 : Bounds ((382467323:ℝ)/1000000000) ((95616831:ℝ)/250000000) (x + (1:ℝ)) := Bounds.add hx iv020 (by norm_num) (by norm_num)

  have iv036 : Bounds ((-38941038299:ℝ)/200000000000) ((-97352594091:ℝ)/500000000000) ((z * (x + z)) / (x + (1:ℝ))) := by
    have hr : Bounds ((2614602443789:ℝ)/1000000000000) ((1307301225313:ℝ)/500000000000) (1 / (x + (1:ℝ))) :=
      Bounds.recip_pos iv039 (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((-38941038299:ℝ)/200000000000) ((-97352594091:ℝ)/500000000000) ((z * (x + z)) * (1 / (x + (1:ℝ)))) :=
      Bounds.mul iv037 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv035 : Bounds ((-38941038299:ℝ)/200000000000) ((-97352594091:ℝ)/500000000000) (topRight x y z) := by
    simpa only [topRight] using iv036

  have iv045 : Bounds ((-546775091:ℝ)/1000000000) ((-54677509:ℝ)/100000000) (z - (1:ℝ)) := Bounds.sub hz iv020 (by norm_num) (by norm_num)

  have iv044 : Bounds ((-247812091409:ℝ)/1000000000000) ((-30976511301:ℝ)/125000000000) (z * (z - (1:ℝ))) := Bounds.mul hz iv045 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv043 : Bounds ((-1710284891:ℝ)/31250000000) ((-27364558021:ℝ)/500000000000) ((z * (z - (1:ℝ))) * (y + (1:ℝ))) := Bounds.mul iv044 iv021 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv042 : Bounds ((16564634661:ℝ)/250000000000) ((66258539673:ℝ)/1000000000000) (((z * (z - (1:ℝ))) * (y + (1:ℝ))) / (denomT x y z)) := by
    have hr : Bounds ((-2364577003:ℝ)/1953125000) ((-302665854287:ℝ)/250000000000) (1 / (denomT x y z)) :=
      Bounds.recip_neg iv001 (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((16564634661:ℝ)/250000000000) ((66258539673:ℝ)/1000000000000) (((z * (z - (1:ℝ))) * (y + (1:ℝ))) * (1 / (denomT x y z))) :=
      Bounds.mul iv043 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv041 : Bounds ((516564634661:ℝ)/250000000000) ((2066258539673:ℝ)/1000000000000) ((2:ℝ) + (((z * (z - (1:ℝ))) * (y + (1:ℝ))) / (denomT x y z))) := Bounds.add iv008 iv042 (by norm_num) (by norm_num)

  have iv040 : Bounds ((516564634661:ℝ)/250000000000) ((2066258539673:ℝ)/1000000000000) (halfHeight x y z) := by
    simpa only [halfHeight] using iv041

  have iv048 : Bounds ((-45322491:ℝ)/100000000) ((-453224909:ℝ)/1000000000) (-z) := Bounds.widen (Bounds.neg hz) (by norm_num) (by norm_num)

  have iv047 : Bounds ((-86671859249:ℝ)/500000000000) ((-86671858831:ℝ)/500000000000) ((-z) * (x + (1:ℝ))) := Bounds.mul iv048 iv039 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv046 : Bounds ((-86671859249:ℝ)/500000000000) ((-86671858831:ℝ)/500000000000) (coreArm x y z) := by
    simpa only [coreArm] using iv047

  have iv052 : Bounds ((-131818406871:ℝ)/500000000000) ((-131818406119:ℝ)/500000000000) ((z ^ 2) / y) := by
    have hr : Bounds ((-641724345557:ℝ)/500000000000) ((-641724344733:ℝ)/500000000000) (1 / y) :=
      Bounds.recip_neg hy (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((-131818406871:ℝ)/500000000000) ((-131818406119:ℝ)/500000000000) ((z ^ 2) * (1 / y)) :=
      Bounds.mul iv011 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv051 : Bounds ((368181593129:ℝ)/500000000000) ((368181593881:ℝ)/500000000000) ((1:ℝ) + ((z ^ 2) / y)) := Bounds.add iv020 iv052 (by norm_num) (by norm_num)

  have iv050 : Bounds ((98250107647:ℝ)/1000000000000) ((98250121531:ℝ)/1000000000000) (((1:ℝ) + ((z ^ 2) / y)) + (headEntry x y z)) := Bounds.add iv051 iv027 (by norm_num) (by norm_num)

  have iv049 : Bounds ((98250107647:ℝ)/1000000000000) ((98250121531:ℝ)/1000000000000) (coreBottom x y z) := by
    simpa only [coreBottom] using iv050

  have iv057 : Bounds ((26997041967:ℝ)/1000000000000) ((13498521313:ℝ)/500000000000) ((x + z) ^ 2) := by
    have hm : Bounds ((26997041967:ℝ)/1000000000000) ((13498521313:ℝ)/500000000000) ((x + z) * (x + z)) :=
      Bounds.mul iv038 iv038 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [pow_two] using hm

  have iv056 : Bounds ((764733243:ℝ)/62500000000) ((2447146443:ℝ)/200000000000) (z * ((x + z) ^ 2)) := Bounds.mul hz iv057 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv055 : Bounds ((6398314899:ℝ)/200000000000) ((6398315087:ℝ)/200000000000) ((z * ((x + z) ^ 2)) / (x + (1:ℝ))) := by
    have hr : Bounds ((2614602443789:ℝ)/1000000000000) ((1307301225313:ℝ)/500000000000) (1 / (x + (1:ℝ))) :=
      Bounds.recip_pos iv039 (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((6398314899:ℝ)/200000000000) ((6398315087:ℝ)/200000000000) ((z * ((x + z) ^ 2)) * (1 / (x + (1:ℝ)))) :=
      Bounds.mul iv056 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv054 : Bounds ((393601684913:ℝ)/200000000000) ((393601685101:ℝ)/200000000000) ((2:ℝ) - ((z * ((x + z) ^ 2)) / (x + (1:ℝ)))) := Bounds.sub iv008 iv055 (by norm_num) (by norm_num)

  have iv053 : Bounds ((393601684913:ℝ)/200000000000) ((393601685101:ℝ)/200000000000) (coreCorner x y z) := by
    simpa only [coreCorner] using iv054

  have iv060 : Bounds ((282961283161:ℝ)/200000000000) ((707403218719:ℝ)/500000000000) ((pivotTwo x y z) * (ratioRD x y z)) := Bounds.mul iv025 iv033 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv059 : Bounds ((127131134561:ℝ)/200000000000) ((317827847719:ℝ)/500000000000) (y + ((pivotTwo x y z) * (ratioRD x y z))) := Bounds.add hy iv060 (by norm_num) (by norm_num)

  have iv058 : Bounds ((127131134561:ℝ)/200000000000) ((317827847719:ℝ)/500000000000) (reducedT x y z) := by
    simpa only [reducedT] using iv059

  have iv063 : Bounds ((179606573823:ℝ)/500000000000) ((89803287371:ℝ)/250000000000) ((x * z) / y) := by
    have hr : Bounds ((-641724345557:ℝ)/500000000000) ((-641724344733:ℝ)/500000000000) (1 / y) :=
      Bounds.recip_neg hy (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((179606573823:ℝ)/500000000000) ((89803287371:ℝ)/250000000000) ((x * z) * (1 / y)) :=
      Bounds.mul iv012 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv062 : Bounds ((-199465245619:ℝ)/200000000000) ((-997326213877:ℝ)/1000000000000) ((headEntry x y z) - ((x * z) / y)) := Bounds.sub iv027 iv063 (by norm_num) (by norm_num)

  have iv061 : Bounds ((-199465245619:ℝ)/200000000000) ((-997326213877:ℝ)/1000000000000) (reducedB23 x y z) := by
    simpa only [reducedB23] using iv062

  have iv066 : Bounds ((359088823307:ℝ)/250000000000) ((1436355307587:ℝ)/1000000000000) ((corePivot x y z) + (headEntry x y z)) := Bounds.add iv022 iv027 (by norm_num) (by norm_num)

  have iv067 : Bounds ((-7271136469:ℝ)/12500000000) ((-581690915489:ℝ)/1000000000000) (z / y) := by
    have hr : Bounds ((-641724345557:ℝ)/500000000000) ((-641724344733:ℝ)/500000000000) (1 / y) :=
      Bounds.recip_neg hy (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((-7271136469:ℝ)/12500000000) ((-581690915489:ℝ)/1000000000000) (z * (1 / y)) :=
      Bounds.mul hz hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv065 : Bounds ((213666093927:ℝ)/250000000000) ((427332196049:ℝ)/500000000000) (((corePivot x y z) + (headEntry x y z)) + (z / y)) := Bounds.add iv066 iv067 (by norm_num) (by norm_num)

  have iv064 : Bounds ((213666093927:ℝ)/250000000000) ((427332196049:ℝ)/500000000000) (reducedB33 x y z) := by
    simpa only [reducedB33] using iv065

  have iv069 : Bounds ((-707403219219:ℝ)/500000000000) ((-282961282961:ℝ)/200000000000) (y - (reducedT x y z)) := Bounds.sub hy iv058 (by norm_num) (by norm_num)

  have iv068 : Bounds ((-707403219219:ℝ)/500000000000) ((-282961282961:ℝ)/200000000000) (yMinusT x y z) := by
    simpa only [yMinusT] using iv069

  have iv070 : Bounds ((382467323:ℝ)/1000000000) ((95616831:ℝ)/250000000) (xPlusOne x y z) := by
    simpa only [xPlusOne] using iv039

  have iv071 : Bounds ((581690915489:ℝ)/1000000000000) ((7271136469:ℝ)/12500000000) ((-z) / y) := by
    have hr : Bounds ((-641724345557:ℝ)/500000000000) ((-641724344733:ℝ)/500000000000) (1 / y) :=
      Bounds.recip_neg hy (by norm_num) (by norm_num) (by norm_num)
    have hm : Bounds ((581690915489:ℝ)/1000000000000) ((7271136469:ℝ)/12500000000) ((-z) * (1 / y)) :=
      Bounds.mul iv048 hr (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    simpa only [div_eq_mul_inv, one_div, one_mul] using hm

  have iv072 : Bounds ((104461529:ℝ)/125000000) ((417846117:ℝ)/500000000) ((x + z) + (1:ℝ)) := Bounds.add iv038 iv020 (by norm_num) (by norm_num)

  have iv073 : Bounds ((-319970297989:ℝ)/250000000000) ((-319970297721:ℝ)/250000000000) ((x * z) - (1:ℝ)) := Bounds.sub iv012 iv020 (by norm_num) (by norm_num)

  have iv075 : Bounds ((120236815889:ℝ)/1000000000000) ((12023681813:ℝ)/100000000000) (x * (topRight x y z)) := Bounds.mul hx iv035 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv074 : Bounds ((87976318187:ℝ)/100000000000) ((879763184111:ℝ)/1000000000000) ((1:ℝ) - (x * (topRight x y z))) := Bounds.sub iv020 iv075 (by norm_num) (by norm_num)

  have iv076 : Bounds ((-238941038299:ℝ)/200000000000) ((-597352594091:ℝ)/500000000000) ((topRight x y z) - (1:ℝ)) := Bounds.sub iv035 iv020 (by norm_num) (by norm_num)

  have iv078 : Bounds ((-353130525373:ℝ)/1000000000000) ((-17656526207:ℝ)/50000000000) (y * z) := Bounds.mul hy hz (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv077 : Bounds ((646869474627:ℝ)/1000000000000) ((32343473793:ℝ)/50000000000) ((1:ℝ) + (y * z)) := Bounds.add iv020 iv078 (by norm_num) (by norm_num)

  have iv080 : Bounds ((151704691843:ℝ)/1000000000000) ((7585234731:ℝ)/50000000000) (y * (topRight x y z)) := Bounds.mul hy iv035 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv079 : Bounds ((42414765269:ℝ)/50000000000) ((848295308157:ℝ)/1000000000000) ((1:ℝ) - (y * (topRight x y z))) := Bounds.sub iv020 iv080 (by norm_num) (by norm_num)

  have iv081 : Bounds ((-397293590931:ℝ)/500000000000) ((-158917436191:ℝ)/200000000000) ((z ^ 2) - (1:ℝ)) := Bounds.sub iv011 iv020 (by norm_num) (by norm_num)

  have iv083 : Bounds ((-22061310723:ℝ)/250000000000) ((-17649048239:ℝ)/200000000000) (z * (topRight x y z)) := Bounds.mul hz iv035 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

  have iv082 : Bounds ((217649048239:ℝ)/200000000000) ((272061310723:ℝ)/250000000000) ((1:ℝ) - (z * (topRight x y z))) := Bounds.sub iv020 iv083 (by norm_num) (by norm_num)

  have iv084 : Bounds ((946457410073:ℝ)/500000000000) ((1892914822011:ℝ)/1000000000000) ((halfHeight x y z) + (coreArm x y z)) := Bounds.add iv040 iv046 (by norm_num) (by norm_num)

  have iv085 : Bounds ((-4104917587:ℝ)/500000000000) ((-4104916083:ℝ)/500000000000) ((halfHeight x y z) - (corePivot x y z)) := Bounds.sub iv040 iv022 (by norm_num) (by norm_num)
  exact {
    denomT_bound := Bounds.widen iv001 (by norm_num) (by norm_num)
    denomR_bound := Bounds.widen iv014 (by norm_num) (by norm_num)
    corePivot_bound := Bounds.widen iv022 (by norm_num) (by norm_num)
    pivotTwo_bound := Bounds.widen iv025 (by norm_num) (by norm_num)
    headEntry_bound := Bounds.widen iv027 (by norm_num) (by norm_num)
    ratioRD_bound := Bounds.widen iv033 (by norm_num) (by norm_num)
    topRight_bound := Bounds.widen iv035 (by norm_num) (by norm_num)
    halfHeight_bound := Bounds.widen iv040 (by norm_num) (by norm_num)
    coreArm_bound := Bounds.widen iv046 (by norm_num) (by norm_num)
    coreBottom_bound := Bounds.widen iv049 (by norm_num) (by norm_num)
    coreCorner_bound := Bounds.widen iv053 (by norm_num) (by norm_num)
    reducedT_bound := Bounds.widen iv058 (by norm_num) (by norm_num)
    reducedB23_bound := Bounds.widen iv061 (by norm_num) (by norm_num)
    reducedB33_bound := Bounds.widen iv064 (by norm_num) (by norm_num)
    yMinusT_bound := Bounds.widen iv068 (by norm_num) (by norm_num)
    xPlusOne_bound := Bounds.widen iv070 (by norm_num) (by norm_num)
    a02_bound := Bounds.widen iv071 (by norm_num) (by norm_num)
    a03_bound := Bounds.widen iv048 (by norm_num) (by norm_num)
    a04_bound := Bounds.widen iv035 (by norm_num) (by norm_num)
    a10_bound := Bounds.widen hx (by norm_num) (by norm_num)
    a11_bound := Bounds.widen iv072 (by norm_num) (by norm_num)
    a12_bound := Bounds.widen iv061 (by norm_num) (by norm_num)
    a21_bound := Bounds.widen hz (by norm_num) (by norm_num)
    a22_bound := Bounds.widen iv064 (by norm_num) (by norm_num)
    a30_bound := Bounds.widen hy (by norm_num) (by norm_num)
    a31_bound := Bounds.widen iv058 (by norm_num) (by norm_num)
    a40_bound := Bounds.widen hz (by norm_num) (by norm_num)
    f01_bound := Bounds.widen iv027 (by norm_num) (by norm_num)
    f02_bound := Bounds.widen iv073 (by norm_num) (by norm_num)
    f03_bound := Bounds.widen iv074 (by norm_num) (by norm_num)
    f11_bound := Bounds.widen iv066 (by norm_num) (by norm_num)
    f13_bound := Bounds.widen iv076 (by norm_num) (by norm_num)
    f20_bound := Bounds.widen iv060 (by norm_num) (by norm_num)
    f22_bound := Bounds.widen iv077 (by norm_num) (by norm_num)
    f23_bound := Bounds.widen iv079 (by norm_num) (by norm_num)
    f31_bound := Bounds.widen iv051 (by norm_num) (by norm_num)
    f32_bound := Bounds.widen iv081 (by norm_num) (by norm_num)
    f33_bound := Bounds.widen iv082 (by norm_num) (by norm_num)
    g01_bound := Bounds.widen iv046 (by norm_num) (by norm_num)
    g11_bound := Bounds.widen iv084 (by norm_num) (by norm_num)
    g12_bound := Bounds.widen iv085 (by norm_num) (by norm_num)
    g20_bound := Bounds.widen iv049 (by norm_num) (by norm_num)
    g22_bound := Bounds.widen iv053 (by norm_num) (by norm_num)
  }

end Rho5.ExternalAttainment
