import BecknerOnofri.EntropyScalarCertificate.Bessel0481
import BecknerOnofri.EntropyScalarCertificate.Bessel0482
import BecknerOnofri.EntropyScalarCertificate.Bessel0729
import BecknerOnofri.EntropyScalarCertificate.Bessel0730
import BecknerOnofri.EntropyScalarCertificate.Brackets0192
import BecknerOnofri.EntropyScalarCertificate.Brackets0193
import BecknerOnofri.EntropyScalarCertificate.Logs0385
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3080
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (100869068224941816042329720900968190784103/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (100869068224941816042329720900968190784103/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (158245610998677407455409980550126790031/781250000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (158245610998677407455409980550126790031/781250000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (202146259264095356813792108453049336403943/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (202146259264095356813792108453049336403943/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3080 BracketBatch0192.bracket3081 (202146259264095356813792108453049336403943/1000000000000000000000000000000000000000) (7185895162442533337078738377765956682277/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3080 BracketBatch0192.bracket3081
  (202146259264095356813792108453049336403943/1000000000000000000000000000000000000000) (7185895162442533337078738377765956682277/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3080
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3081
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (2025543820783070815429247751041622912396797/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2025543820783070815429247751041622912396797/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (127110789911090155136504309371446818663989/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (127110789911090155136504309371446818663989/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (4059316459360513297613316700984772011020621/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4059316459360513297613316700984772011020621/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3081 BracketBatch0192.bracket3082 (4059316459360513297613316700984772011020621/20000000000000000000000000000000000000000) (7191910942024776524436557451920336435681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3081 BracketBatch0192.bracket3082
  (4059316459360513297613316700984772011020621/20000000000000000000000000000000000000000) (7191910942024776524436557451920336435681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3081
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3082
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (2033772638577442482184068949943149098623821/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2033772638577442482184068949943149098623821/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2042068630471868445061709130151874131457201/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2042068630471868445061709130151874131457201/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (2037920634524655463622889040047511615040511/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2037920634524655463622889040047511615040511/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3082 BracketBatch0192.bracket3083 (2037920634524655463622889040047511615040511/10000000000000000000000000000000000000000) (7197947403054958504552831717473532877039/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3082 BracketBatch0192.bracket3083
  (2037920634524655463622889040047511615040511/10000000000000000000000000000000000000000) (7197947403054958504552831717473532877039/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3082
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3083
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1021034315235934222530854565075937065728599/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1021034315235934222530854565075937065728599/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (10252163111887060052962631261660461161999/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10252163111887060052962631261660461161999/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (2046250626424640227827117691241983181928499/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2046250626424640227827117691241983181928499/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3083 BracketBatch0192.bracket3084 (2046250626424640227827117691241983181928499/10000000000000000000000000000000000000000) (1440800929414497973410334470138752078579/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3083 BracketBatch0192.bracket3084
  (2046250626424640227827117691241983181928499/10000000000000000000000000000000000000000) (1440800929414497973410334470138752078579/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3083
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3084
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0481.rows BesselBatch0481.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (2050432622377412010592526252332092232399797/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2050432622377412010592526252332092232399797/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (514716363450095081491082310229470565805057/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (514716363450095081491082310229470565805057/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (164371923047111693462274219729998979824801/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (164371923047111693462274219729998979824801/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3084 BracketBatch0192.bracket3085 (164371923047111693462274219729998979824801/800000000000000000000000000000000000000) (1802520693876806646517959481623863873673/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3084 BracketBatch0192.bracket3085
  (164371923047111693462274219729998979824801/800000000000000000000000000000000000000) (1802520693876806646517959481623863873673/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3084
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3085
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (82354618152015213038573169636715290528809/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (82354618152015213038573169636715290528809/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (413473595624643569360905797356419027629449/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (413473595624643569360905797356419027629449/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0729.rows BesselBatch0729.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (412623343192359817276885822769997740136747/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (412623343192359817276885822769997740136747/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3085 BracketBatch0192.bracket3086 (412623343192359817276885822769997740136747/2000000000000000000000000000000000000000) (7216181889644563417404329841757927126703/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3085 BracketBatch0192.bracket3086
  (412623343192359817276885822769997740136747/2000000000000000000000000000000000000000) (7216181889644563417404329841757927126703/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3085
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3086
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1033683989061608923402264493391047569073621/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1033683989061608923402264493391047569073621/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2075941062892393003330309712002019158453607/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2075941062892393003330309712002019158453607/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (4143309041015610850134838698784114296600849/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4143309041015610850134838698784114296600849/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3086 BracketBatch0192.bracket3087 (4143309041015610850134838698784114296600849/20000000000000000000000000000000000000000) (451393880661803559662912083158951241643/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3086 BracketBatch0192.bracket3087
  (4143309041015610850134838698784114296600849/20000000000000000000000000000000000000000) (451393880661803559662912083158951241643/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3086
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3087
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (518985265723098250832577428000504789613401/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (518985265723098250832577428000504789613401/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0482.rows BesselBatch0482.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (521146397528370508288138655987051707100247/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (521146397528370508288138655987051707100247/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0730.rows BesselBatch0730.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (65008228953216797445044755249222281044603/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (65008228953216797445044755249222281044603/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0385.rows ScalarLogs0385.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0192.bracket3087 BracketBatch0193.bracket3088 (65008228953216797445044755249222281044603/312500000000000000000000000000000000000) (7228443479225105431124309835229900775093/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0192.bracket3087 BracketBatch0193.bracket3088
  (65008228953216797445044755249222281044603/312500000000000000000000000000000000000) (7228443479225105431124309835229900775093/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3087
