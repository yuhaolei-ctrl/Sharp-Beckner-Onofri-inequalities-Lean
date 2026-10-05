module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0408
public import BecknerOnofri.EntropyScalarCertificate.Bessel0409
public import BecknerOnofri.EntropyScalarCertificate.Bessel0410
public import BecknerOnofri.EntropyScalarCertificate.Bessel0693
public import BecknerOnofri.EntropyScalarCertificate.Brackets0163
public import BecknerOnofri.EntropyScalarCertificate.Brackets0164
public import BecknerOnofri.EntropyScalarCertificate.Logs0327
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2616
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (478359192910740659672369250229413053650477/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (478359192910740659672369250229413053650477/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (480187120824544298056986853480741420212089/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (480187120824544298056986853480741420212089/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (479273156867642478864678051855077236931283/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (479273156867642478864678051855077236931283/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2616 BracketBatch0163.bracket2617 (479273156867642478864678051855077236931283/10000000000000000000000000000000000000000) (4863260649639748586283820372296530119/9765625000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2616 BracketBatch0163.bracket2617
  (479273156867642478864678051855077236931283/10000000000000000000000000000000000000000) (4863260649639748586283820372296530119/9765625000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2616
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2617
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0408.rows BesselBatch0408.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (240093560412272149028493426740370710106043/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (240093560412272149028493426740370710106043/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (482029110022510981294221094241687644391091/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (482029110022510981294221094241687644391091/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (962216230847055279351207947722429064603177/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (962216230847055279351207947722429064603177/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2617 BracketBatch0163.bracket2618 (962216230847055279351207947722429064603177/20000000000000000000000000000000000000000) (4985594766062516584680578404599005793853/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2617 BracketBatch0163.bracket2618
  (962216230847055279351207947722429064603177/20000000000000000000000000000000000000000) (4985594766062516584680578404599005793853/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2617
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2618
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (30126819376406936330888818390105477774443/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30126819376406936330888818390105477774443/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (96777064675322205310898444030728214551451/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (96777064675322205310898444030728214551451/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (965914433399122007848713314395328717148343/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (965914433399122007848713314395328717148343/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2618 BracketBatch0163.bracket2619 (965914433399122007848713314395328717148343/20000000000000000000000000000000000000000) (2495616199754770008313992110187993205039/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2618 BracketBatch0163.bracket2619
  (965914433399122007848713314395328717148343/20000000000000000000000000000000000000000) (2495616199754770008313992110187993205039/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2618
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2619
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (120971330844152756638623055038410268189313/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (120971330844152756638623055038410268189313/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (97151185256792318473156494262174549639131/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (97151185256792318473156494262174549639131/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (969641249660572618920274691464513820952907/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (969641249660572618920274691464513820952907/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2619 BracketBatch0163.bracket2620 (969641249660572618920274691464513820952907/20000000000000000000000000000000000000000) (624611494838685995856029222202131849387/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2619 BracketBatch0163.bracket2620
  (969641249660572618920274691464513820952907/20000000000000000000000000000000000000000) (624611494838685995856029222202131849387/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2619
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2620
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (121438981570990398091445617827718187048913/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (121438981570990398091445617827718187048913/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (60955135839494256132534916549446651480767/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (60955135839494256132534916549446651480767/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (243349253249978910356515450926611490010447/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (243349253249978910356515450926611490010447/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2620 BracketBatch0163.bracket2621 (243349253249978910356515450926611490010447/5000000000000000000000000000000000000000) (5002573598284442029028856308024998103491/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2620 BracketBatch0163.bracket2621
  (243349253249978910356515450926611490010447/5000000000000000000000000000000000000000) (5002573598284442029028856308024998103491/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2620
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2621
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (487641086715954049060279332395573211846133/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (487641086715954049060279332395573211846133/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (3824538869285412280983344936110635016597/78125000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3824538869285412280983344936110635016597/78125000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (977182061984486821026147484217734493970549/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (977182061984486821026147484217734493970549/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2621 BracketBatch0163.bracket2622 (977182061984486821026147484217734493970549/20000000000000000000000000000000000000000) (156508671073675038942054607783961861771/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2621 BracketBatch0163.bracket2622
  (977182061984486821026147484217734493970549/20000000000000000000000000000000000000000) (156508671073675038942054607783961861771/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2621
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2622
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (489540975268532771965868151822161282124413/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (489540975268532771965868151822161282124413/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (491455765213656965025666064508931626774419/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (491455765213656965025666064508931626774419/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (61312296280136858561970888520693306806177/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (61312296280136858561970888520693306806177/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2622 BracketBatch0163.bracket2623 (61312296280136858561970888520693306806177/1250000000000000000000000000000000000000) (5014003744569771535315606559795736437811/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2622 BracketBatch0163.bracket2623
  (61312296280136858561970888520693306806177/1250000000000000000000000000000000000000) (5014003744569771535315606559795736437811/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2622
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2623
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0409.rows BesselBatch0409.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (30715985325853560314104129031808226673401/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (30715985325853560314104129031808226673401/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0410.rows BesselBatch0410.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (246692816275989059023185001651208153797383/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (246692816275989059023185001651208153797383/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0693.rows BesselBatch0693.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (492420698882817541536018033905673967184591/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (492420698882817541536018033905673967184591/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0327.rows ScalarLogs0327.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0163.bracket2623 BracketBatch0164.bracket2624 (492420698882817541536018033905673967184591/10000000000000000000000000000000000000000) (5019752568095991245103346994623470813963/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0163.bracket2623 BracketBatch0164.bracket2624
  (492420698882817541536018033905673967184591/10000000000000000000000000000000000000000) (5019752568095991245103346994623470813963/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2623
