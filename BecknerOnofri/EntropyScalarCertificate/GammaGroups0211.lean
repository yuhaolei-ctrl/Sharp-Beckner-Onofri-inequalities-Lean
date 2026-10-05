module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0263
public import BecknerOnofri.EntropyScalarCertificate.Bessel0264
public import BecknerOnofri.EntropyScalarCertificate.Bessel0265
public import BecknerOnofri.EntropyScalarCertificate.Bessel0620
public import BecknerOnofri.EntropyScalarCertificate.Bessel0621
public import BecknerOnofri.EntropyScalarCertificate.Brackets0105
public import BecknerOnofri.EntropyScalarCertificate.Brackets0106
public import BecknerOnofri.EntropyScalarCertificate.Logs0211
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1688
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (4919499653315685198612849073031383991201/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4919499653315685198612849073031383991201/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (393810739652249239711013665947059628963/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (393810739652249239711013665947059628963/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (19684267797937601390001039794739258706477/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19684267797937601390001039794739258706477/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨7,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨15,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1688 BracketBatch0105.bracket1689 (19684267797937601390001039794739258706477/10000000000000000000000000000000000000000) (49056938400593692889271683894993977233/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1688 BracketBatch0105.bracket1689
  (19684267797937601390001039794739258706477/10000000000000000000000000000000000000000) (49056938400593692889271683894993977233/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1688
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1689
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (19690536982612461985550683297352981448147/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19690536982612461985550683297352981448147/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (19703093701918904347077711751854015597089/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19703093701918904347077711751854015597089/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (9848407671132841583157098762301749261309/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9848407671132841583157098762301749261309/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨23,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨31,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1689 BracketBatch0105.bracket1690 (9848407671132841583157098762301749261309/5000000000000000000000000000000000000000) (785557697817382164266737775769043205673/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1689 BracketBatch0105.bracket1690
  (9848407671132841583157098762301749261309/5000000000000000000000000000000000000000) (785557697817382164266737775769043205673/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1689
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1690
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (9851546850959452173538855875927007798543/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9851546850959452173538855875927007798543/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1232229300798346389094562358214583166991/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1232229300798346389094562358214583166991/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (19709381257346223286295354741643673134471/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19709381257346223286295354741643673134471/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨39,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨47,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1690 BracketBatch0105.bracket1691 (19709381257346223286295354741643673134471/10000000000000000000000000000000000000000) (19655127859708241638519701622270929563/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1690 BracketBatch0105.bracket1691
  (19709381257346223286295354741643673134471/10000000000000000000000000000000000000000) (19655127859708241638519701622270929563/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1690
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1691
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (19715668812773542225512997731433330671853/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19715668812773542225512997731433330671853/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (19728262356887549305488847049871638221003/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19728262356887549305488847049871638221003/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (4930491396207636441375230597663121111607/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4930491396207636441375230597663121111607/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨55,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨63,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1691 BracketBatch0105.bracket1692 (4930491396207636441375230597663121111607/2500000000000000000000000000000000000000) (78685326530391212954410858962076572331/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1691 BracketBatch0105.bracket1692
  (4930491396207636441375230597663121111607/2500000000000000000000000000000000000000) (78685326530391212954410858962076572331/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1691
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1692
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (19728262356887549305488847049871638221/10000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19728262356887549305488847049871638221/10000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (3948174875218442938271440176487970718813/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3948174875218442938271440176487970718813/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (7893827346595952799369209586462298363013/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7893827346595952799369209586462298363013/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨71,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨79,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1692 BracketBatch0105.bracket1693 (7893827346595952799369209586462298363013/4000000000000000000000000000000000000000) (196875537936993255637194700109492206887/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1692 BracketBatch0105.bracket1693
  (7893827346595952799369209586462298363013/4000000000000000000000000000000000000000) (196875537936993255637194700109492206887/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1692
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1693
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (9870437188046107345678600441219926797031/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9870437188046107345678600441219926797031/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (987675245616968036534961085616682051709/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (987675245616968036534961085616682051709/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (19747189644215787711028211297386747314121/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19747189644215787711028211297386747314121/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨87,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨95,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1693 BracketBatch0105.bracket1694 (19747189644215787711028211297386747314121/10000000000000000000000000000000000000000) (788151774906633612068223628517027291607/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1693 BracketBatch0105.bracket1694
  (19747189644215787711028211297386747314121/10000000000000000000000000000000000000000) (788151774906633612068223628517027291607/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1693
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1694
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (19753504912339360730699221712333641034177/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19753504912339360730699221712333641034177/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (19766154007701762588634812192471356569891/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19766154007701762588634812192471356569891/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (9879914730010280829833508476201249401017/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9879914730010280829833508476201249401017/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨103,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨111,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1694 BracketBatch0105.bracket1695 (9879914730010280829833508476201249401017/5000000000000000000000000000000000000000) (788802135968297856492300638897954035873/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1694 BracketBatch0105.bracket1695
  (9879914730010280829833508476201249401017/5000000000000000000000000000000000000000) (788802135968297856492300638897954035873/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1694
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1695
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0264.rows BesselBatch0264.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (617692312740680080894837881014729892809/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (617692312740680080894837881014729892809/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0265.rows BesselBatch0265.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (9889410852186784790922001922119665847047/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9889410852186784790922001922119665847047/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0621.rows BesselBatch0621.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (19772487856037666085239408018355344131991/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19772487856037666085239408018355344131991/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨119,by decide⟩
noncomputable def wholeH := identityFunctionEnclosure leftPoint.argument rightPoint.argument
noncomputable def wholeT := (firstMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeSecond := (secondMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeThird := (thirdMomentEnclosure leftPoint rightPoint).round
noncomputable def wholeOne : FunctionEnclosure leftPoint.argument rightPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const leftPoint.argument rightPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def wholeZ := logBesselEndpoints leftPoint rightPoint whole_zl whole_zu (by decide +kernel)
noncomputable def wholePlus := logCompose (wholeOne.radd wholeT) whole_pl whole_pu (by decide +kernel)
noncomputable def wholeMinus := logCompose (wholeOne.rsub wholeT) whole_ml whole_mu (by decide +kernel)
noncomputable def wholeW1lower := checkedWeightOfLog 1 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW1upper := checkedWeightOfLog 1 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW1 := (weightCompose wholeT 1 (by omega)
  wholeW1lower wholeW1upper (by decide +kernel)).round
noncomputable def wholeW2lower := checkedWeightOfLog 2 wholeT.value.lower whole_wl (by decide +kernel)
noncomputable def wholeW2upper := checkedWeightOfLog 2 wholeT.value.upper whole_wu (by decide +kernel)
noncomputable def wholeW2 := (weightCompose wholeT 2 (by omega)
  wholeW2lower wholeW2upper (by decide +kernel)).round
noncomputable def wholeBase := gammaBaseFunctionEnclosure wholeH wholeT wholeZ wholePlus wholeMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def wholeData : GammaEnclosureData leftPoint.argument rightPoint.argument :=
  ⟨wholeBase,wholeT,wholeSecond,wholeThird,wholeW1,wholeW2⟩
theorem wholeDataAccepted : wholeData.check=true := by decide +kernel
noncomputable def wholeGamma := wholeData.enclosure wholeDataAccepted
def point_wl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0211.rows ScalarLogs0211.accepted ⟨127,by decide⟩
noncomputable def pointH := identityFunctionEnclosure midPoint.argument midPoint.argument
noncomputable def pointT := (firstMomentEnclosure midPoint midPoint).round
noncomputable def pointSecond := (secondMomentEnclosure midPoint midPoint).round
noncomputable def pointThird := (thirdMomentEnclosure midPoint midPoint).round
noncomputable def pointOne : FunctionEnclosure midPoint.argument midPoint.argument (fun _ => (1 : ℝ)) :=
  (FunctionEnclosure.const midPoint.argument midPoint.argument 1).congr (fun _ => Rat.cast_one)
noncomputable def pointZ := logBesselEndpoints midPoint midPoint point_zl point_zu (by decide +kernel)
noncomputable def pointPlus := logCompose (pointOne.radd pointT) point_pl point_pu (by decide +kernel)
noncomputable def pointMinus := logCompose (pointOne.rsub pointT) point_ml point_mu (by decide +kernel)
noncomputable def pointW1lower := checkedWeightOfLog 1 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW1upper := checkedWeightOfLog 1 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW1 := (weightCompose pointT 1 (by omega)
  pointW1lower pointW1upper (by decide +kernel)).round
noncomputable def pointW2lower := checkedWeightOfLog 2 pointT.value.lower point_wl (by decide +kernel)
noncomputable def pointW2upper := checkedWeightOfLog 2 pointT.value.upper point_wu (by decide +kernel)
noncomputable def pointW2 := (weightCompose pointT 2 (by omega)
  pointW2lower pointW2upper (by decide +kernel)).round
noncomputable def pointBase := gammaBaseFunctionEnclosure pointH pointT pointZ pointPlus pointMinus
  (by decide +kernel) (by decide +kernel)
noncomputable def pointData : GammaEnclosureData midPoint.argument midPoint.argument :=
  ⟨pointBase,pointT,pointSecond,pointThird,pointW1,pointW2⟩
theorem pointDataAccepted : pointData.check=true := by decide +kernel
noncomputable def pointGamma := pointData.enclosure pointDataAccepted
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1695 BracketBatch0106.bracket1696 (19772487856037666085239408018355344131991/10000000000000000000000000000000000000000) (789453236123657309986150002957804798309/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1695 BracketBatch0106.bracket1696
  (19772487856037666085239408018355344131991/10000000000000000000000000000000000000000) (789453236123657309986150002957804798309/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1695
