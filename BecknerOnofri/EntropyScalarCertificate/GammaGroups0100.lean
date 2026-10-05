import BecknerOnofri.EntropyScalarCertificate.Bessel0125
import BecknerOnofri.EntropyScalarCertificate.Bessel0126
import BecknerOnofri.EntropyScalarCertificate.Bessel0551
import BecknerOnofri.EntropyScalarCertificate.Bessel0552
import BecknerOnofri.EntropyScalarCertificate.Brackets0050
import BecknerOnofri.EntropyScalarCertificate.Logs0100
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0800
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (294016980275966270169702775509753497241/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (294016980275966270169702775509753497241/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (1475757641453501177492709002939477367589/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1475757641453501177492709002939477367589/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (1472921271416666264170611440244122426897/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1472921271416666264170611440244122426897/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0800 BracketBatch0050.bracket0801 (1472921271416666264170611440244122426897/5000000000000000000000000000000000000000) (1015293714539663291620450884346641827/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0800 BracketBatch0050.bracket0801
  (1472921271416666264170611440244122426897/5000000000000000000000000000000000000000) (1015293714539663291620450884346641827/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0800
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0801
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (118060611316280094199416720235158189407/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (118060611316280094199416720235158189407/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (2962871491147875236301008210522147344523/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2962871491147875236301008210522147344523/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (2957193387027438795643213108200551039849/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2957193387027438795643213108200551039849/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0801 BracketBatch0050.bracket0802 (2957193387027438795643213108200551039849/10000000000000000000000000000000000000000) (2575133337470365001130254594023266409/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0801 BracketBatch0050.bracket0802
  (2957193387027438795643213108200551039849/10000000000000000000000000000000000000000) (2575133337470365001130254594023266409/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0801
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0802
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (74071787278696880907525205263053683613/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (74071787278696880907525205263053683613/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2974238484182183065814022090348655961279/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2974238484182183065814022090348655961279/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (5937109975330058302115030300870803305799/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5937109975330058302115030300870803305799/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0802 BracketBatch0050.bracket0803 (5937109975330058302115030300870803305799/20000000000000000000000000000000000000000) (208995170355443269605470075461725123/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0802 BracketBatch0050.bracket0803
  (5937109975330058302115030300870803305799/20000000000000000000000000000000000000000) (208995170355443269605470075461725123/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0802
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0803
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (743559621045545766453505522587163990319/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (743559621045545766453505522587163990319/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (2985616318956069144407631175694124756829/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2985616318956069144407631175694124756829/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (1191970960627650442044330653208556143621/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1191970960627650442044330653208556143621/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0803 BracketBatch0050.bracket0804 (1191970960627650442044330653208556143621/4000000000000000000000000000000000000000) (5300312620587221066373490946513327433/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0803 BracketBatch0050.bracket0804
  (1191970960627650442044330653208556143621/4000000000000000000000000000000000000000) (5300312620587221066373490946513327433/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0803
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0804
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1492808159478034572203815587847062378413/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1492808159478034572203815587847062378413/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (749251263165943701171500757655678783133/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (749251263165943701171500757655678783133/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (2991310685809921974546817103158419944679/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2991310685809921974546817103158419944679/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0804 BracketBatch0050.bracket0805 (2991310685809921974546817103158419944679/10000000000000000000000000000000000000000) (537657308668143938041193712363859101/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0804 BracketBatch0050.bracket0805
  (2991310685809921974546817103158419944679/10000000000000000000000000000000000000000) (537657308668143938041193712363859101/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0804
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0805
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (2997005052663774804686003030622715132529/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2997005052663774804686003030622715132529/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (752101185687377682978893085410068154873/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (752101185687377682978893085410068154873/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (6005409795413285536601575372262987752021/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6005409795413285536601575372262987752021/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0805 BracketBatch0050.bracket0806 (6005409795413285536601575372262987752021/20000000000000000000000000000000000000000) (5453667014499702845032209322914756191/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0805 BracketBatch0050.bracket0806
  (6005409795413285536601575372262987752021/20000000000000000000000000000000000000000) (5453667014499702845032209322914756191/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0805
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0806
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0125.rows BesselBatch0125.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3008404742749510731915572341640272619489/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3008404742749510731915572341640272619489/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (3019815446909343307482358407327930544403/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3019815446909343307482358407327930544403/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (1507055047414713509849482687242050790973/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1507055047414713509849482687242050790973/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0806 BracketBatch0050.bracket0807 (1507055047414713509849482687242050790973/5000000000000000000000000000000000000000) (276580039608835322878362470195491933/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0806 BracketBatch0050.bracket0807
  (1507055047414713509849482687242050790973/5000000000000000000000000000000000000000) (276580039608835322878362470195491933/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0806
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0807
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (7549538617273358268705896018319826361/25000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7549538617273358268705896018319826361/25000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0126.rows BesselBatch0126.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1515618611546548064592948093634298187747/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1515618611546548064592948093634298187747/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0551.rows BesselBatch0551.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0552.rows BesselBatch0552.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (3025526335001219718334127297298263459947/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3025526335001219718334127297298263459947/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0100.rows ScalarLogs0100.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0050.bracket0807 BracketBatch0050.bracket0808 (3025526335001219718334127297298263459947/10000000000000000000000000000000000000000) (5610380838761756322450078744472572207/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0050.bracket0807 BracketBatch0050.bracket0808
  (3025526335001219718334127297298263459947/10000000000000000000000000000000000000000) (5610380838761756322450078744472572207/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0807
