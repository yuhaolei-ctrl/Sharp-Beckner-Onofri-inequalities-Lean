import BecknerOnofri.EntropyScalarCertificate.Bessel0078
import BecknerOnofri.EntropyScalarCertificate.Bessel0079
import BecknerOnofri.EntropyScalarCertificate.Bessel0080
import BecknerOnofri.EntropyScalarCertificate.Bessel0528
import BecknerOnofri.EntropyScalarCertificate.Brackets0031
import BecknerOnofri.EntropyScalarCertificate.Brackets0032
import BecknerOnofri.EntropyScalarCertificate.Logs0063
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0504
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1592871536137492647393000792824292373343/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1592871536137492647393000792824292373343/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (318989700986475227706280002674295364177/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (318989700986475227706280002674295364177/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (796955010267467196481100201548942298557/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (796955010267467196481100201548942298557/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0504 BracketBatch0031.bracket0505 (796955010267467196481100201548942298557/5000000000000000000000000000000000000000) (240669070866715910138530515514352239/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0504 BracketBatch0031.bracket0505
  (796955010267467196481100201548942298557/5000000000000000000000000000000000000000) (240669070866715910138530515514352239/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0504
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0505
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0078.rows BesselBatch0078.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (797474252466188069265700006685738410441/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (797474252466188069265700006685738410441/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (798512838211837317897031294150487649151/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (798512838211837317897031294150487649151/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (199498386334753173395341412604528257449/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (199498386334753173395341412604528257449/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0505 BracketBatch0031.bracket0506 (199498386334753173395341412604528257449/1250000000000000000000000000000000000000) (483805361923022932343215233206061593/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0505 BracketBatch0031.bracket0506
  (199498386334753173395341412604528257449/1250000000000000000000000000000000000000) (483805361923022932343215233206061593/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0505
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0506
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1597025676423674635794062588300975298299/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1597025676423674635794062588300975298299/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1599103050905424502842720058973012974799/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1599103050905424502842720058973012974799/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (1598064363664549569318391323636994136549/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1598064363664549569318391323636994136549/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0506 BracketBatch0031.bracket0507 (1598064363664549569318391323636994136549/10000000000000000000000000000000000000000) (486282095028943794938145990476809247/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0506 BracketBatch0031.bracket0507
  (1598064363664549569318391323636994136549/10000000000000000000000000000000000000000) (486282095028943794938145990476809247/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0506
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0507
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (399775762726356125710680014743253243699/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (399775762726356125710680014743253243699/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (400295157167952783921457058736986674467/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (400295157167952783921457058736986674467/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (400035459947154454816068536740119959083/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (400035459947154454816068536740119959083/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0507 BracketBatch0031.bracket0508 (400035459947154454816068536740119959083/2500000000000000000000000000000000000000) (488768365845511097800670530529979469/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0507 BracketBatch0031.bracket0508
  (400035459947154454816068536740119959083/2500000000000000000000000000000000000000) (488768365845511097800670530529979469/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0507
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0508
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (320236125734362227137165646989589339573/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (320236125734362227137165646989589339573/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1603258410017169215287295386768149196817/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1603258410017169215287295386768149196817/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (1602219519344490175486561810858047947341/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1602219519344490175486561810858047947341/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0508 BracketBatch0031.bracket0509 (1602219519344490175486561810858047947341/10000000000000000000000000000000000000000) (245632099600868756574034740595093753/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0508 BracketBatch0031.bracket0509
  (1602219519344490175486561810858047947341/10000000000000000000000000000000000000000) (245632099600868756574034740595093753/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0508
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0509
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (801629205008584607643647693384074598407/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (801629205008584607643647693384074598407/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (321067279047196592089360052749091898339/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (321067279047196592089360052749091898339/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (3208594805253152175734095650513608688509/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3208594805253152175734095650513608688509/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0509 BracketBatch0031.bracket0510 (3208594805253152175734095650513608688509/20000000000000000000000000000000000000000) (49376961996134467731095756545401459/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0509 BracketBatch0031.bracket0510
  (3208594805253152175734095650513608688509/20000000000000000000000000000000000000000) (49376961996134467731095756545401459/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0509
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0510
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (401334098808995740111700065936364872923/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (401334098808995740111700065936364872923/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (803707292311443190476124041758806280379/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (803707292311443190476124041758806280379/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (64255019597177386827980966945261441049/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64255019597177386827980966945261441049/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0510 BracketBatch0031.bracket0511 (64255019597177386827980966945261441049/400000000000000000000000000000000000000) (496284653022776193418103204895268757/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0510 BracketBatch0031.bracket0511
  (64255019597177386827980966945261441049/400000000000000000000000000000000000000) (496284653022776193418103204895268757/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0510
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0511
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0079.rows BesselBatch0079.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (321482916924577276190449616703522512151/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (321482916924577276190449616703522512151/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0080.rows BesselBatch0080.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (804746489236331765502456781746368499633/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (804746489236331765502456781746368499633/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0528.rows BesselBatch0528.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (3216907563095549911957161647010349560021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3216907563095549911957161647010349560021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0063.rows ScalarLogs0063.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0031.bracket0511 BracketBatch0032.bracket0512 (3216907563095549911957161647010349560021/20000000000000000000000000000000000000000) (249404661659605327575419353113695357/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0031.bracket0511 BracketBatch0032.bracket0512
  (3216907563095549911957161647010349560021/20000000000000000000000000000000000000000) (249404661659605327575419353113695357/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0511
