import BecknerOnofri.EntropyScalarCertificate.Bessel0152
import BecknerOnofri.EntropyScalarCertificate.Bessel0153
import BecknerOnofri.EntropyScalarCertificate.Bessel0565
import BecknerOnofri.EntropyScalarCertificate.Brackets0061
import BecknerOnofri.EntropyScalarCertificate.Logs0122
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0976
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (1033111829222702577369597625241944412219/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1033111829222702577369597625241944412219/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (1035997071389382558149336963435531117223/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1035997071389382558149336963435531117223/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (1034554450306042567759467294338737764721/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1034554450306042567759467294338737764721/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0976 BracketBatch0061.bracket0977 (1034554450306042567759467294338737764721/2000000000000000000000000000000000000000) (37595814232532043304708671903618489579/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0976 BracketBatch0061.bracket0977
  (1034554450306042567759467294338737764721/2000000000000000000000000000000000000000) (37595814232532043304708671903618489579/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0976
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0977
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (80937271202295512355416950268400868533/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (80937271202295512355416950268400868533/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (2597219299344936341574383665421779781127/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2597219299344936341574383665421779781127/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (5187211977818392736947726074010607574183/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5187211977818392736947726074010607574183/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0977 BracketBatch0061.bracket0978 (5187211977818392736947726074010607574183/10000000000000000000000000000000000000000) (18971416375981882905803731787856332543/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0977 BracketBatch0061.bracket0978
  (5187211977818392736947726074010607574183/10000000000000000000000000000000000000000) (18971416375981882905803731787856332543/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0977
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0978
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (5194438598689872683148767330843559562251/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5194438598689872683148767330843559562251/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (651114877848122828156274016950455000747/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (651114877848122828156274016950455000747/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (10403357621474855308398959466447199568227/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10403357621474855308398959466447199568227/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0978 BracketBatch0061.bracket0979 (10403357621474855308398959466447199568227/20000000000000000000000000000000000000000) (19146193192229536432349933283950957303/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0978 BracketBatch0061.bracket0979
  (10403357621474855308398959466447199568227/20000000000000000000000000000000000000000) (19146193192229536432349933283950957303/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0978
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0979
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0152.rows BesselBatch0152.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (5208919022784982625250192135603640005973/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5208919022784982625250192135603640005973/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (5223426781731090281986997714135421750829/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5223426781731090281986997714135421750829/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (5216172902258036453618594924869530878401/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5216172902258036453618594924869530878401/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0979 BracketBatch0061.bracket0980 (5216172902258036453618594924869530878401/10000000000000000000000000000000000000000) (38644489640860687522861574438577714349/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0979 BracketBatch0061.bracket0980
  (5216172902258036453618594924869530878401/10000000000000000000000000000000000000000) (38644489640860687522861574438577714349/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0979
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0980
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (2611713390865545140993498857067710875413/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2611713390865545140993498857067710875413/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (1309490507273338074161783032412790893363/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1309490507273338074161783032412790893363/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (5230694405412221289317064921893292662139/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5230694405412221289317064921893292662139/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0980 BracketBatch0061.bracket0981 (5230694405412221289317064921893292662139/10000000000000000000000000000000000000000) (9749789276458205808732192431932333153/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0980 BracketBatch0061.bracket0981
  (5230694405412221289317064921893292662139/10000000000000000000000000000000000000000) (9749789276458205808732192431932333153/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0980
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0981
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (5237962029093352296647132129651163573449/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5237962029093352296647132129651163573449/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (2626262459756700563626485176868469818877/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2626262459756700563626485176868469818877/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (10490486948606753423900102483388103211203/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10490486948606753423900102483388103211203/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0981 BracketBatch0061.bracket0982 (10490486948606753423900102483388103211203/20000000000000000000000000000000000000000) (1967820171918313942013865742931857239/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0981 BracketBatch0061.bracket0982
  (10490486948606753423900102483388103211203/20000000000000000000000000000000000000000) (1967820171918313942013865742931857239/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0981
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0982
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (5252524919513401127252970353736939637751/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5252524919513401127252970353736939637751/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (2633557804359814459440280403869019358759/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2633557804359814459440280403869019358759/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (10519640528233030046133531161474978355269/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10519640528233030046133531161474978355269/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0982 BracketBatch0061.bracket0983 (10519640528233030046133531161474978355269/20000000000000000000000000000000000000000) (39716243372288901025577557194596290661/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0982 BracketBatch0061.bracket0983
  (10519640528233030046133531161474978355269/20000000000000000000000000000000000000000) (39716243372288901025577557194596290661/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0982
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0983
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1053423121743925783776112161547607743503/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1053423121743925783776112161547607743503/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0153.rows BesselBatch0153.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (1320433563384397502682271320533228805697/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1320433563384397502682271320533228805697/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0565.rows BesselBatch0565.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (10548849862257218929609646089870953940303/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10548849862257218929609646089870953940303/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0122.rows ScalarLogs0122.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0061.bracket0983 BracketBatch0061.bracket0984 (10548849862257218929609646089870953940303/20000000000000000000000000000000000000000) (1603147668671259418116743249946859543/400000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0061.bracket0983 BracketBatch0061.bracket0984
  (10548849862257218929609646089870953940303/20000000000000000000000000000000000000000) (1603147668671259418116743249946859543/400000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0983
