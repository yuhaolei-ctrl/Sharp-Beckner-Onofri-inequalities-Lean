import BecknerOnofri.EntropyScalarCertificate.Bessel0262
import BecknerOnofri.EntropyScalarCertificate.Bessel0263
import BecknerOnofri.EntropyScalarCertificate.Bessel0620
import BecknerOnofri.EntropyScalarCertificate.Brackets0105
import BecknerOnofri.EntropyScalarCertificate.Logs0210
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1680
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (9789173652552107962066009019699759543813/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9789173652552107962066009019699759543813/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (4897685089466316491244445729261795565767/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4897685089466316491244445729261795565767/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (19584543831484740944554900478223350675347/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19584543831484740944554900478223350675347/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1680 BracketBatch0105.bracket1681 (19584543831484740944554900478223350675347/10000000000000000000000000000000000000000) (779763799974519947300422660782138121079/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1680 BracketBatch0105.bracket1681
  (19584543831484740944554900478223350675347/10000000000000000000000000000000000000000) (779763799974519947300422660782138121079/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1680
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1681
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (3918148071573053192995556583409436452613/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3918148071573053192995556583409436452613/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (19603151432111056705790881345321991744901/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19603151432111056705790881345321991744901/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (19596945894988161335384332131184587003983/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19596945894988161335384332131184587003983/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1681 BracketBatch0105.bracket1682 (19596945894988161335384332131184587003983/10000000000000000000000000000000000000000) (390202330171636279428479646385651874697/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1681 BracketBatch0105.bracket1682
  (19596945894988161335384332131184587003983/10000000000000000000000000000000000000000) (390202330171636279428479646385651874697/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1681
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1682
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (9801575716055528352895440672660995872449/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9801575716055528352895440672660995872449/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (980779028424512028626686627373568285593/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (980779028424512028626686627373568285593/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (19609366000300648639162306946396678728379/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19609366000300648639162306946396678728379/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1682 BracketBatch0105.bracket1683 (19609366000300648639162306946396678728379/10000000000000000000000000000000000000000) (781046244503770641705294234840155794621/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1682 BracketBatch0105.bracket1683
  (19609366000300648639162306946396678728379/10000000000000000000000000000000000000000) (781046244503770641705294234840155794621/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1682
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1683
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (19615580568490240572533732547471365711857/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19615580568490240572533732547471365711857/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (19628027807767902341145035464752181184019/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19628027807767902341145035464752181184019/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (9810902094064535728419692003055886723969/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9810902094064535728419692003055886723969/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1683 BracketBatch0105.bracket1684 (9810902094064535728419692003055886723969/5000000000000000000000000000000000000000) (781688553619575010766181042602002849847/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1683 BracketBatch0105.bracket1684
  (9810902094064535728419692003055886723969/5000000000000000000000000000000000000000) (781688553619575010766181042602002849847/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1683
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1684
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1226751737985493896321564716547011324001/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1226751737985493896321564716547011324001/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (4910123297706490399034766633316855818373/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4910123297706490399034766633316855818373/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (9817130249648465984321025499504901114377/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9817130249648465984321025499504901114377/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1684 BracketBatch0105.bracket1685 (9817130249648465984321025499504901114377/5000000000000000000000000000000000000000) (782331588856480947480289528358529080381/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1684 BracketBatch0105.bracket1685
  (9817130249648465984321025499504901114377/5000000000000000000000000000000000000000) (782331588856480947480289528358529080381/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1684
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1685
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (19640493190825961596139066533267423273489/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19640493190825961596139066533267423273489/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (9826488379331788431086267072321049297473/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9826488379331788431086267072321049297473/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (7858693989897907691662320135581904373687/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7858693989897907691662320135581904373687/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1685 BracketBatch0105.bracket1686 (7858693989897907691662320135581904373687/4000000000000000000000000000000000000000) (195743837845630739026356344455877082023/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1685 BracketBatch0105.bracket1686
  (7858693989897907691662320135581904373687/4000000000000000000000000000000000000000) (195743837845630739026356344455877082023/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1685
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1686
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (19652976758663576862172534144642098594943/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19652976758663576862172534144642098594943/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (1229092409524846963563762762848451791879/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1229092409524846963563762762848451791879/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (39318455311061128279192738350217327265007/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39318455311061128279192738350217327265007/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1686 BracketBatch0105.bracket1687 (39318455311061128279192738350217327265007/20000000000000000000000000000000000000000) (391809921183989767239298708319611886913/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1686 BracketBatch0105.bracket1687
  (39318455311061128279192738350217327265007/20000000000000000000000000000000000000000) (391809921183989767239298708319611886913/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1686
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1687
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (19665478552397551417020204205575228670061/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19665478552397551417020204205575228670061/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0263.rows BesselBatch0263.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (19677998613262740794451396292125535964807/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19677998613262740794451396292125535964807/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (9835869291415073052867900124425191158717/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9835869291415073052867900124425191158717/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0210.rows ScalarLogs0210.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0105.bracket1687 BracketBatch0105.bracket1688 (9835869291415073052867900124425191158717/5000000000000000000000000000000000000000) (784265062985377959328961925951404091073/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0105.bracket1687 BracketBatch0105.bracket1688
  (9835869291415073052867900124425191158717/5000000000000000000000000000000000000000) (784265062985377959328961925951404091073/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1687
