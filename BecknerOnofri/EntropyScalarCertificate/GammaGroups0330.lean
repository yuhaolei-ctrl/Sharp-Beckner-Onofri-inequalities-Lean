import BecknerOnofri.EntropyScalarCertificate.Bessel0412
import BecknerOnofri.EntropyScalarCertificate.Bessel0413
import BecknerOnofri.EntropyScalarCertificate.Bessel0695
import BecknerOnofri.EntropyScalarCertificate.Brackets0165
import BecknerOnofri.EntropyScalarCertificate.Logs0330
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2640
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (526469117156877505046357238596180249459163/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (526469117156877505046357238596180249459163/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (132171288761487874531501036358142116151449/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (132171288761487874531501036358142116151449/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1055154272202829003172361384028748714064959/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1055154272202829003172361384028748714064959/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2640 BracketBatch0165.bracket2641 (1055154272202829003172361384028748714064959/20000000000000000000000000000000000000000) (2560547612080427431615700115896720052259/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2640 BracketBatch0165.bracket2641
  (1055154272202829003172361384028748714064959/20000000000000000000000000000000000000000) (2560547612080427431615700115896720052259/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2640
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2641
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (528685155045951498126004145432568464605793/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (528685155045951498126004145432568464605793/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (132729993311660747667772642894856664944173/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (132729993311660747667772642894856664944173/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (211921025658518897759418943402399024876497/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (211921025658518897759418943402399024876497/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2641 BracketBatch0165.bracket2642 (211921025658518897759418943402399024876497/4000000000000000000000000000000000000000) (5127279076491356125256254323770671950791/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2641 BracketBatch0165.bracket2642
  (211921025658518897759418943402399024876497/4000000000000000000000000000000000000000) (5127279076491356125256254323770671950791/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2641
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2642
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (530919973246642990671090571579426659776689/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (530919973246642990671090571579426659776689/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (266586905753779749212469770262253696004909/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (266586905753779749212469770262253696004909/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (1064093784754202489096030112103934051786507/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1064093784754202489096030112103934051786507/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2642 BracketBatch0165.bracket2643 (1064093784754202489096030112103934051786507/20000000000000000000000000000000000000000) (5133488820933131333169464707033711329983/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2642 BracketBatch0165.bracket2643
  (1064093784754202489096030112103934051786507/20000000000000000000000000000000000000000) (5133488820933131333169464707033711329983/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2642
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2643
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (106634762301511899684987908104901478401963/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (106634762301511899684987908104901478401963/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (133861728418893837078619071421001555403299/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (133861728418893837078619071421001555403299/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (1068620725183134846739415826208513613623011/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1068620725183134846739415826208513613623011/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2643 BracketBatch0165.bracket2644 (1068620725183134846739415826208513613623011/20000000000000000000000000000000000000000) (5139724651012500683258525138776610785773/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2643 BracketBatch0165.bracket2644
  (1068620725183134846739415826208513613623011/20000000000000000000000000000000000000000) (5139724651012500683258525138776610785773/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2643
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2644
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (535446913675575348314476285684006221613193/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (535446913675575348314476285684006221613193/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (537739527783777318166772999911818785231409/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (537739527783777318166772999911818785231409/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (536593220729676333240624642797912503422301/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (536593220729676333240624642797912503422301/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2644 BracketBatch0165.bracket2645 (536593220729676333240624642797912503422301/10000000000000000000000000000000000000000) (160812086317591426706655526751247344419/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2644 BracketBatch0165.bracket2645
  (536593220729676333240624642797912503422301/10000000000000000000000000000000000000000) (160812086317591426706655526751247344419/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2644
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2645
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (268869763891888659083386499955909392615703/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (268869763891888659083386499955909392615703/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (540051906141684732625166024954987380809111/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (540051906141684732625166024954987380809111/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (1077791433925462050791939024866806166040517/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1077791433925462050791939024866806166040517/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2645 BracketBatch0165.bracket2646 (1077791433925462050791939024866806166040517/20000000000000000000000000000000000000000) (2576137675871652622881413604757473897181/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2645 BracketBatch0165.bracket2646
  (1077791433925462050791939024866806166040517/20000000000000000000000000000000000000000) (2576137675871652622881413604757473897181/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2645
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2646
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (135012976535421183156291506238746845202277/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (135012976535421183156291506238746845202277/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (135596076356953234545021008100392673342541/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (135596076356953234545021008100392673342541/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (135304526446187208850656257169569759272409/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (135304526446187208850656257169569759272409/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2646 BracketBatch0165.bracket2647 (135304526446187208850656257169569759272409/2500000000000000000000000000000000000000) (5158590619056239487991155249798430598399/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2646 BracketBatch0165.bracket2647
  (135304526446187208850656257169569759272409/2500000000000000000000000000000000000000) (5158590619056239487991155249798430598399/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2646
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2647
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (542384305427812938180084032401570693370161/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (542384305427812938180084032401570693370161/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0413.rows BesselBatch0413.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (544736986784651477548513175557486205210649/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (544736986784651477548513175557486205210649/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (108712129221246441572859720795905689858081/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (108712129221246441572859720795905689858081/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0330.rows ScalarLogs0330.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0165.bracket2647 BracketBatch0165.bracket2648 (108712129221246441572859720795905689858081/2000000000000000000000000000000000000000) (5164932765366244834060186601232845443613/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0165.bracket2647 BracketBatch0165.bracket2648
  (108712129221246441572859720795905689858081/2000000000000000000000000000000000000000) (5164932765366244834060186601232845443613/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2647
