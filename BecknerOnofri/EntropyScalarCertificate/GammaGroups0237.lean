import BecknerOnofri.EntropyScalarCertificate.Bessel0296
import BecknerOnofri.EntropyScalarCertificate.Bessel0297
import BecknerOnofri.EntropyScalarCertificate.Bessel0637
import BecknerOnofri.EntropyScalarCertificate.Brackets0118
import BecknerOnofri.EntropyScalarCertificate.Brackets0119
import BecknerOnofri.EntropyScalarCertificate.Logs0237
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1896
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (5791952061907672735633957150316100206389/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5791952061907672735633957150316100206389/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (14554805765983612976879250655285093055887/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14554805765983612976879250655285093055887/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨6,by decide⟩
]
theorem midAccepted : besselPointCheck (58069371841505589631928287062150687143719/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (58069371841505589631928287062150687143719/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1896 BracketBatch0118.bracket1897 (58069371841505589631928287062150687143719/20000000000000000000000000000000000000000) (1203085347523912734849142079450938631269/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1896 BracketBatch0118.bracket1897
  (58069371841505589631928287062150687143719/20000000000000000000000000000000000000000) (1203085347523912734849142079450938631269/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1896
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1897
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (29109611531967225953758501310570186111771/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29109611531967225953758501310570186111771/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (29261158377220160323966533938113159649923/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29261158377220160323966533938113159649923/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨11,by decide⟩
]
theorem midAccepted : besselPointCheck (29185384954593693138862517624341672880847/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29185384954593693138862517624341672880847/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1897 BracketBatch0118.bracket1898 (29185384954593693138862517624341672880847/10000000000000000000000000000000000000000) (241805128992095563530134502243787386091/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1897 BracketBatch0118.bracket1898
  (29185384954593693138862517624341672880847/10000000000000000000000000000000000000000) (241805128992095563530134502243787386091/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1897
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1898
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (45720559964406500506197709278301811953/15625000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (45720559964406500506197709278301811953/15625000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (5882885835875490317434737422842527890073/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5882885835875490317434737422842527890073/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨16,by decide⟩
]
theorem midAccepted : besselPointCheck (11735117511319522382228044210465159820057/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (11735117511319522382228044210465159820057/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1898 BracketBatch0118.bracket1899 (11735117511319522382228044210465159820057/4000000000000000000000000000000000000000) (1215008734284553562889654023479766342447/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1898 BracketBatch0118.bracket1899
  (11735117511319522382228044210465159820057/4000000000000000000000000000000000000000) (1215008734284553562889654023479766342447/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1898
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1899
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (14707214589688725793586843557106319725181/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14707214589688725793586843557106319725181/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (29569452903014115946002852078509122247909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29569452903014115946002852078509122247909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨21,by decide⟩
]
theorem midAccepted : besselPointCheck (58983882082391567533176539192721761698271/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (58983882082391567533176539192721761698271/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1899 BracketBatch0118.bracket1900 (58983882082391567533176539192721761698271/20000000000000000000000000000000000000000) (30525876313517442423069611059738263627/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1899 BracketBatch0118.bracket1900
  (58983882082391567533176539192721761698271/20000000000000000000000000000000000000000) (30525876313517442423069611059738263627/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1899
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1900
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0296.rows BesselBatch0296.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (14784726451507057973001426039254561123953/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14784726451507057973001426039254561123953/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (14863129580560679833082097836440129149413/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14863129580560679833082097836440129149413/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨26,by decide⟩
]
theorem midAccepted : besselPointCheck (14823928016033868903041761937847345136683/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14823928016033868903041761937847345136683/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1900 BracketBatch0118.bracket1901 (14823928016033868903041761937847345136683/5000000000000000000000000000000000000000) (1227105043374815325876008391596441593947/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1900 BracketBatch0118.bracket1901
  (14823928016033868903041761937847345136683/5000000000000000000000000000000000000000) (1227105043374815325876008391596441593947/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1900
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1901
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (29726259161121359666164195672880258298823/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29726259161121359666164195672880258298823/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (29884878233644609628248984340699835509143/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29884878233644609628248984340699835509143/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨31,by decide⟩
]
theorem midAccepted : besselPointCheck (29805568697382984647206590006790046903983/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29805568697382984647206590006790046903983/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1901 BracketBatch0118.bracket1902 (29805568697382984647206590006790046903983/10000000000000000000000000000000000000000) (1233219157189511257956944804267407582193/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1901 BracketBatch0118.bracket1902
  (29805568697382984647206590006790046903983/10000000000000000000000000000000000000000) (1233219157189511257956944804267407582193/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1901
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1902
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (1494243911682230481412449217034991775457/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1494243911682230481412449217034991775457/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (15022670543331341328665790732704272994493/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15022670543331341328665790732704272994493/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨36,by decide⟩
]
theorem midAccepted : besselPointCheck (29965109660153646142790282903054190749063/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29965109660153646142790282903054190749063/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1902 BracketBatch0118.bracket1903 (29965109660153646142790282903054190749063/10000000000000000000000000000000000000000) (1239377851303941480864517368980828119437/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1902 BracketBatch0118.bracket1903
  (29965109660153646142790282903054190749063/10000000000000000000000000000000000000000) (1239377851303941480864517368980828119437/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1902
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1903
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (30045341086662682657331581465408545988983/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30045341086662682657331581465408545988983/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0297.rows BesselBatch0297.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (6041535878446755586618399938417999501629/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6041535878446755586618399938417999501629/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0637.rows BesselBatch0637.accepted ⟨41,by decide⟩
]
theorem midAccepted : besselPointCheck (7531627559862057573802947644687317937141/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7531627559862057573802947644687317937141/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0237.rows ScalarLogs0237.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0118.bracket1903 BracketBatch0119.bracket1904 (7531627559862057573802947644687317937141/2500000000000000000000000000000000000000) (311395397529573734672044874426562492097/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0118.bracket1903 BracketBatch0119.bracket1904
  (7531627559862057573802947644687317937141/2500000000000000000000000000000000000000) (311395397529573734672044874426562492097/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1903
