import BecknerOnofri.EntropyScalarCertificate.Bessel0340
import BecknerOnofri.EntropyScalarCertificate.Bessel0341
import BecknerOnofri.EntropyScalarCertificate.Bessel0658
import BecknerOnofri.EntropyScalarCertificate.Bessel0659
import BecknerOnofri.EntropyScalarCertificate.Brackets0136
import BecknerOnofri.EntropyScalarCertificate.Logs0272
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2176
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (84092922969888380164064251264310238958027/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (84092922969888380164064251264310238958027/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (84367722692157929921155230990894138858837/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (84367722692157929921155230990894138858837/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (5264395176938947190163108820475136806777/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5264395176938947190163108820475136806777/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2176 BracketBatch0136.bracket2177 (5264395176938947190163108820475136806777/625000000000000000000000000000000000000) (63401051029749236975817835778931365317/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2176 BracketBatch0136.bracket2177
  (5264395176938947190163108820475136806777/625000000000000000000000000000000000000) (63401051029749236975817835778931365317/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2176
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2177
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (42183861346078964960577615495447069429417/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (42183861346078964960577615495447069429417/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (8464435602944233814512452766825516342257/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8464435602944233814512452766825516342257/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (42253019680400067016569939664787325570351/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42253019680400067016569939664787325570351/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2177 BracketBatch0136.bracket2178 (42253019680400067016569939664787325570351/5000000000000000000000000000000000000000) (2540311015332495171888037041998542426431/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2177 BracketBatch0136.bracket2178
  (42253019680400067016569939664787325570351/5000000000000000000000000000000000000000) (2540311015332495171888037041998542426431/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2177
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2178
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (84644356029442338145124527668255163422567/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (84644356029442338145124527668255163422567/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (84922841377609186638683003654645816373501/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (84922841377609186638683003654645816373501/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (42391799351762881195951882830725244949017/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42391799351762881195951882830725244949017/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2178 BracketBatch0136.bracket2179 (42391799351762881195951882830725244949017/5000000000000000000000000000000000000000) (636148870460514537355051211938413494819/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2178 BracketBatch0136.bracket2179
  (42391799351762881195951882830725244949017/5000000000000000000000000000000000000000) (636148870460514537355051211938413494819/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2178
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2179
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (42461420688804593319341501827322908186749/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (42461420688804593319341501827322908186749/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (21300799344863508110290998753327894007701/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21300799344863508110290998753327894007701/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (85063019378531609539923499333978696202151/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (85063019378531609539923499333978696202151/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2179 BracketBatch0136.bracket2180 (85063019378531609539923499333978696202151/10000000000000000000000000000000000000000) (637223886591582954536655292807124172641/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2179 BracketBatch0136.bracket2180
  (85063019378531609539923499333978696202151/10000000000000000000000000000000000000000) (637223886591582954536655292807124172641/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2179
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2180
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (85203197379454032441163995013311576030801/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (85203197379454032441163995013311576030801/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (4274272146442871461587116561239768242731/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4274272146442871461587116561239768242731/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (170688640308311461672906326238106940885421/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (170688640308311461672906326238106940885421/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2180 BracketBatch0136.bracket2181 (170688640308311461672906326238106940885421/20000000000000000000000000000000000000000) (2553211315615825574307457545473744362877/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2180 BracketBatch0136.bracket2181
  (170688640308311461672906326238106940885421/20000000000000000000000000000000000000000) (2553211315615825574307457545473744362877/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2180
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2181
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (85485442928857429231742331224795364854617/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (85485442928857429231742331224795364854617/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (85769597175026212794616704868943387697649/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (85769597175026212794616704868943387697649/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (85627520051941821013179518046869376276133/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (85627520051941821013179518046869376276133/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2181 BracketBatch0136.bracket2182 (85627520051941821013179518046869376276133/10000000000000000000000000000000000000000) (2557542897377798744829102624469232187073/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2181 BracketBatch0136.bracket2182
  (85627520051941821013179518046869376276133/10000000000000000000000000000000000000000) (2557542897377798744829102624469232187073/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2181
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2182
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (42884798587513106397308352434471693848823/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (42884798587513106397308352434471693848823/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (43027839763410525015472005642197798056497/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (43027839763410525015472005642197798056497/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (2147815958773090785319508951916737297633/250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2147815958773090785319508951916737297633/250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2182 BracketBatch0136.bracket2183 (2147815958773090785319508951916737297633/250000000000000000000000000000000000000) (2561890400530397580848715341085891836821/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2182 BracketBatch0136.bracket2183
  (2147815958773090785319508951916737297633/250000000000000000000000000000000000000) (2561890400530397580848715341085891836821/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2182
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2183
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (86055679526821050030944011284395596112991/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (86055679526821050030944011284395596112991/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0341.rows BesselBatch0341.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (674560231696658636016300520565687606369/78125000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (674560231696658636016300520565687606369/78125000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0659.rows BesselBatch0659.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (172399389183993355441030477916803609728223/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (172399389183993355441030477916803609728223/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0272.rows ScalarLogs0272.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0136.bracket2183 BracketBatch0136.bracket2184 (172399389183993355441030477916803609728223/20000000000000000000000000000000000000000) (2566253935057019499817786146798454665633/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0136.bracket2183 BracketBatch0136.bracket2184
  (172399389183993355441030477916803609728223/20000000000000000000000000000000000000000) (2566253935057019499817786146798454665633/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2183
