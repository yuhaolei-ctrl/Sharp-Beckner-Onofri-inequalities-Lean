import BecknerOnofri.EntropyScalarCertificate.Bessel0105
import BecknerOnofri.EntropyScalarCertificate.Bessel0106
import BecknerOnofri.EntropyScalarCertificate.Bessel0541
import BecknerOnofri.EntropyScalarCertificate.Bessel0542
import BecknerOnofri.EntropyScalarCertificate.Brackets0042
import BecknerOnofri.EntropyScalarCertificate.Logs0084
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0672
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (486219749997313030835679425127269310301/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (486219749997313030835679425127269310301/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1946994270595022950142149705104275910687/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1946994270595022950142149705104275910687/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (3891873270584275073484867405613353151891/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3891873270584275073484867405613353151891/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0672 BracketBatch0042.bracket0673 (3891873270584275073484867405613353151891/20000000000000000000000000000000000000000) (1049649244390471102718737852237907461/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0672 BracketBatch0042.bracket0673
  (3891873270584275073484867405613353151891/20000000000000000000000000000000000000000) (1049649244390471102718737852237907461/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0672
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0673
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (486748567648755737535537426276068977671/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (486748567648755737535537426276068977671/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (48727744889783053449815158088858302099/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (48727744889783053449815158088858302099/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (974026016546586272033689007164651998661/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (974026016546586272033689007164651998661/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0673 BracketBatch0042.bracket0674 (974026016546586272033689007164651998661/5000000000000000000000000000000000000000) (1054089819127308091489918150348039029/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0673 BracketBatch0042.bracket0674
  (974026016546586272033689007164651998661/5000000000000000000000000000000000000000) (1054089819127308091489918150348039029/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0673
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0674
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1949109795591322137992606323554332083957/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1949109795591322137992606323554332083957/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1951225575300996479971440324860625920511/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1951225575300996479971440324860625920511/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (975083842723079654491011662103739501117/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (975083842723079654491011662103739501117/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0674 BracketBatch0042.bracket0675 (975083842723079654491011662103739501117/5000000000000000000000000000000000000000) (264636142428321183199946951804121901/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0674 BracketBatch0042.bracket0675
  (975083842723079654491011662103739501117/5000000000000000000000000000000000000000) (264636142428321183199946951804121901/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0674
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0675
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (487806393825249119992860081215156480127/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (487806393825249119992860081215156480127/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (390668322009417701431611304773954811977/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (390668322009417701431611304773954811977/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (3904567185348084987129496848730399980393/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3904567185348084987129496848730399980393/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0675 BracketBatch0042.bracket0676 (3904567185348084987129496848730399980393/20000000000000000000000000000000000000000) (265753381742690340358549355980132681/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0675 BracketBatch0042.bracket0676
  (3904567185348084987129496848730399980393/20000000000000000000000000000000000000000) (265753381742690340358549355980132681/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0675
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0676
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (976670805023544253579028261934887029941/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (976670805023544253579028261934887029941/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (244432237519104599419070418360097422711/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (244432237519104599419070418360097422711/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (390879951019992530251061987075055344157/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (390879951019992530251061987075055344157/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0676 BracketBatch0042.bracket0677 (390879951019992530251061987075055344157/2000000000000000000000000000000000000000) (106749672175928709973321621963271657/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0676 BracketBatch0042.bracket0677
  (390879951019992530251061987075055344157/2000000000000000000000000000000000000000) (106749672175928709973321621963271657/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0676
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0677
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (391091580030567359070512669376155876337/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (391091580030567359070512669376155876337/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (391514889188335254434590812251055087581/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (391514889188335254434590812251055087581/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (391303234609451306752551740813605481959/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (391303234609451306752551740813605481959/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0677 BracketBatch0042.bracket0678 (391303234609451306752551740813605481959/2000000000000000000000000000000000000000) (535997092487808342266404355317630523/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0677 BracketBatch0042.bracket0678
  (391303234609451306752551740813605481959/2000000000000000000000000000000000000000) (535997092487808342266404355317630523/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0677
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0678
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0105.rows BesselBatch0105.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (978787222970838136086477030627637718951/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (978787222970838136086477030627637718951/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (1959691247737238524531556454902505085691/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1959691247737238524531556454902505085691/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (3917265693678914796704510516157780523593/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3917265693678914796704510516157780523593/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0678 BracketBatch0042.bracket0679 (3917265693678914796704510516157780523593/20000000000000000000000000000000000000000) (53825297377686365953783773471057199/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0678 BracketBatch0042.bracket0679
  (3917265693678914796704510516157780523593/20000000000000000000000000000000000000000) (53825297377686365953783773471057199/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0678
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0679
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (244961405967154815566444556862813135711/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (244961405967154815566444556862813135711/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0106.rows BesselBatch0106.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (980904152931676053245745565296294973901/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (980904152931676053245745565296294973901/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0541.rows BesselBatch0541.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0542.rows BesselBatch0542.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (392149955360059063102304758549509503349/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (392149955360059063102304758549509503349/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0084.rows ScalarLogs0084.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0042.bracket0679 BracketBatch0042.bracket0680 (392149955360059063102304758549509503349/2000000000000000000000000000000000000000) (67564502529052221869920059265498149/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0042.bracket0679 BracketBatch0042.bracket0680
  (392149955360059063102304758549509503349/2000000000000000000000000000000000000000) (67564502529052221869920059265498149/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0679
