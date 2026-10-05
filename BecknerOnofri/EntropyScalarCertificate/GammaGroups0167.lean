import BecknerOnofri.EntropyScalarCertificate.Bessel0208
import BecknerOnofri.EntropyScalarCertificate.Bessel0209
import BecknerOnofri.EntropyScalarCertificate.Bessel0210
import BecknerOnofri.EntropyScalarCertificate.Bessel0593
import BecknerOnofri.EntropyScalarCertificate.Brackets0083
import BecknerOnofri.EntropyScalarCertificate.Brackets0084
import BecknerOnofri.EntropyScalarCertificate.Logs0167
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1336
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (14933686889424594006471865450538901841961/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14933686889424594006471865450538901841961/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (1870907164713608725884908632231532907467/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1870907164713608725884908632231532907467/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (29900944207133463813551134508391165101697/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (29900944207133463813551134508391165101697/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1336 BracketBatch0083.bracket1337 (29900944207133463813551134508391165101697/20000000000000000000000000000000000000000) (20990764853257249760560185695367351747/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1336 BracketBatch0083.bracket1337
  (29900944207133463813551134508391165101697/20000000000000000000000000000000000000000) (20990764853257249760560185695367351747/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1336
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1337
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0208.rows BesselBatch0208.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (14967257317708869807079269057852263259733/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14967257317708869807079269057852263259733/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (120007957458975056740125011562267155971/80000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (120007957458975056740125011562267155971/80000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (7492063000020187974898723875783914439027/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7492063000020187974898723875783914439027/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1337 BracketBatch0083.bracket1338 (7492063000020187974898723875783914439027/5000000000000000000000000000000000000000) (526683097433245038196678660292409529601/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1337 BracketBatch0083.bracket1338
  (7492063000020187974898723875783914439027/5000000000000000000000000000000000000000) (526683097433245038196678660292409529601/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1337
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1338
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (3750248670592970523128906611320848624093/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3750248670592970523128906611320848624093/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (15034900406028416077450386594615897458959/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15034900406028416077450386594615897458959/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (30035895088400298169966013039899291955331/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30035895088400298169966013039899291955331/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1338 BracketBatch0083.bracket1339 (30035895088400298169966013039899291955331/20000000000000000000000000000000000000000) (528605601758473773855199981897948646379/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1338 BracketBatch0083.bracket1339
  (30035895088400298169966013039899291955331/20000000000000000000000000000000000000000) (528605601758473773855199981897948646379/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1338
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1339
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (3758725101507104019362596648653974364739/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3758725101507104019362596648653974364739/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1883621990903428879608208234740238702427/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1883621990903428879608208234740238702427/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (7525969083313961778579013118134451769593/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7525969083313961778579013118134451769593/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1339 BracketBatch0083.bracket1340 (7525969083313961778579013118134451769593/5000000000000000000000000000000000000000) (66317086345694888679332057761050056397/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1339 BracketBatch0083.bracket1340
  (7525969083313961778579013118134451769593/5000000000000000000000000000000000000000) (66317086345694888679332057761050056397/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1339
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1340
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (15068975927227431036865665877921909619413/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15068975927227431036865665877921909619413/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (7551611350333677876536745013310527241367/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7551611350333677876536745013310527241367/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (30172198627894786789939155904542964102147/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30172198627894786789939155904542964102147/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1340 BracketBatch0083.bracket1341 (30172198627894786789939155904542964102147/20000000000000000000000000000000000000000) (266238210710444969953844397715847389357/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1340 BracketBatch0083.bracket1341
  (30172198627894786789939155904542964102147/20000000000000000000000000000000000000000) (266238210710444969953844397715847389357/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1340
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1341
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (15103222700667355753073490026621054482731/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15103222700667355753073490026621054482731/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (7568821098707368632500524764732757763717/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7568821098707368632500524764732757763717/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (6048172979616418603614907911217314002033/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6048172979616418603614907911217314002033/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1341 BracketBatch0083.bracket1342 (6048172979616418603614907911217314002033/4000000000000000000000000000000000000000) (534424851203942547592577825720396821039/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1341 BracketBatch0083.bracket1342
  (6048172979616418603614907911217314002033/4000000000000000000000000000000000000000) (534424851203942547592577825720396821039/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1341
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1342
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (15137642197414737265001049529465515527431/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15137642197414737265001049529465515527431/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1896529488140787741040530093080628460661/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1896529488140787741040530093080628460661/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (30309878102541039193325290274110543212719/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (30309878102541039193325290274110543212719/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1342 BracketBatch0083.bracket1343 (30309878102541039193325290274110543212719/20000000000000000000000000000000000000000) (268191019056235820335290664022285502327/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1342 BracketBatch0083.bracket1343
  (30309878102541039193325290274110543212719/20000000000000000000000000000000000000000) (268191019056235820335290664022285502327/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1342
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1343
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0209.rows BesselBatch0209.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (3034447181025260385664848148929005537057/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3034447181025260385664848148929005537057/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0210.rows BesselBatch0210.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (15207005328274488970418776852740088674459/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15207005328274488970418776852740088674459/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0593.rows BesselBatch0593.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (474675644271887357792859649959142443121/312500000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (474675644271887357792859649959142443121/312500000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0167.rows ScalarLogs0167.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0083.bracket1343 BracketBatch0084.bracket1344 (474675644271887357792859649959142443121/312500000000000000000000000000000000000) (134587010166938172915536144060606404087/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0083.bracket1343 BracketBatch0084.bracket1344
  (474675644271887357792859649959142443121/312500000000000000000000000000000000000) (134587010166938172915536144060606404087/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1343
