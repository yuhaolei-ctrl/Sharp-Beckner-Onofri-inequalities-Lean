import BecknerOnofri.EntropyScalarCertificate.Bessel0207
import BecknerOnofri.EntropyScalarCertificate.Bessel0208
import BecknerOnofri.EntropyScalarCertificate.Bessel0592
import BecknerOnofri.EntropyScalarCertificate.Bessel0593
import BecknerOnofri.EntropyScalarCertificate.Brackets0083
import BecknerOnofri.EntropyScalarCertificate.Logs0166
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1328
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (7335483776166568965241586155684129153191/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7335483776166568965241586155684129153191/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (7351625930053987736446447615346955080629/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7351625930053987736446447615346955080629/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (734355485311027835084401688551554211691/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (734355485311027835084401688551554211691/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1328 BracketBatch0083.bracket1329 (734355485311027835084401688551554211691/500000000000000000000000000000000000000) (509757717184368532532373833137583147451/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1328 BracketBatch0083.bracket1329
  (734355485311027835084401688551554211691/500000000000000000000000000000000000000) (509757717184368532532373833137583147451/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1328
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1329
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (2940650372021595094578579046138782032251/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2940650372021595094578579046138782032251/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (3683923068049965951019413492497267451987/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3683923068049965951019413492497267451987/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (29438944132307839276970549200682979969203/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29438944132307839276970549200682979969203/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1329 BracketBatch0083.bracket1330 (29438944132307839276970549200682979969203/20000000000000000000000000000000000000000) (511605440705742015399777388472039583061/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1329 BracketBatch0083.bracket1330
  (29438944132307839276970549200682979969203/20000000000000000000000000000000000000000) (511605440705742015399777388472039583061/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1329
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1330
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (2947138454439972760815530793997813961589/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2947138454439972760815530793997813961589/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (14768290091117021471233382439880773531843/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14768290091117021471233382439880773531843/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (7375995590829221318827759102467460834947/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7375995590829221318827759102467460834947/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1330 BracketBatch0083.bracket1331 (7375995590829221318827759102467460834947/5000000000000000000000000000000000000000) (32091328654296821133695477440317849719/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1330 BracketBatch0083.bracket1331
  (7375995590829221318827759102467460834947/5000000000000000000000000000000000000000) (32091328654296821133695477440317849719/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1330
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1331
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0207.rows BesselBatch0207.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (46150906534740692097604320124627417287/31250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (46150906534740692097604320124627417287/31250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (7400523316846741491556303750548712539387/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7400523316846741491556303750548712539387/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (14784668362405252227172994970489099305307/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14784668362405252227172994970489099305307/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1331 BracketBatch0083.bracket1332 (14784668362405252227172994970489099305307/10000000000000000000000000000000000000000) (257662611523663591644026808022667982963/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1331 BracketBatch0083.bracket1332
  (14784668362405252227172994970489099305307/10000000000000000000000000000000000000000) (257662611523663591644026808022667982963/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1331
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1332
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (14801046633693482983112607501097425078771/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14801046633693482983112607501097425078771/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (14833963231279559489131428593124373796957/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14833963231279559489131428593124373796957/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0592.rows BesselBatch0592.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (1852188116560815154515252255888862429733/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1852188116560815154515252255888862429733/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1332 BracketBatch0083.bracket1333 (1852188116560815154515252255888862429733/1250000000000000000000000000000000000000) (258598693742011272450069365351500253481/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1332 BracketBatch0083.bracket1333
  (1852188116560815154515252255888862429733/1250000000000000000000000000000000000000) (258598693742011272450069365351500253481/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1332
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1333
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (7416981615639779744565714296562186898477/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7416981615639779744565714296562186898477/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (3716760307483804995836011222468036957151/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3716760307483804995836011222468036957151/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (14850502230607389736237736741498260812779/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14850502230607389736237736741498260812779/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1333 BracketBatch0083.bracket1334 (14850502230607389736237736741498260812779/10000000000000000000000000000000000000000) (8110590707730287559373267280725046163/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1333 BracketBatch0083.bracket1334
  (14850502230607389736237736741498260812779/10000000000000000000000000000000000000000) (8110590707730287559373267280725046163/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1333
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1334
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (14867041229935219983344044889872147828601/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14867041229935219983344044889872147828601/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (3725070497656610883008750673088894297793/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3725070497656610883008750673088894297793/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (29767323220561663515379047582227725019773/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29767323220561663515379047582227725019773/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1334 BracketBatch0083.bracket1335 (29767323220561663515379047582227725019773/20000000000000000000000000000000000000000) (26048326523676502823665888989789329701/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1334 BracketBatch0083.bracket1335
  (29767323220561663515379047582227725019773/20000000000000000000000000000000000000000) (26048326523676502823665888989789329701/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1334
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1335
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (14900281990626443532035002692355577191169/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14900281990626443532035002692355577191169/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (3733421722356148501617966362634725460491/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3733421722356148501617966362634725460491/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (29833968880051037538506868142894479033133/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29833968880051037538506868142894479033133/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0166.rows ScalarLogs0166.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1335 BracketBatch0083.bracket1336 (29833968880051037538506868142894479033133/20000000000000000000000000000000000000000) (522863617497448295863315392294707334151/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1335 BracketBatch0083.bracket1336
  (29833968880051037538506868142894479033133/20000000000000000000000000000000000000000) (522863617497448295863315392294707334151/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1335
