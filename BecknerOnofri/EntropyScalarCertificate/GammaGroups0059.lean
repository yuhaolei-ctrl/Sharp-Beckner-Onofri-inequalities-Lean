import BecknerOnofri.EntropyScalarCertificate.Bessel0073
import BecknerOnofri.EntropyScalarCertificate.Bessel0074
import BecknerOnofri.EntropyScalarCertificate.Bessel0075
import BecknerOnofri.EntropyScalarCertificate.Bessel0525
import BecknerOnofri.EntropyScalarCertificate.Bessel0526
import BecknerOnofri.EntropyScalarCertificate.Brackets0029
import BecknerOnofri.EntropyScalarCertificate.Brackets0030
import BecknerOnofri.EntropyScalarCertificate.Logs0059
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0472
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (38162845165086768593316859751733597311/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38162845165086768593316859751733597311/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (152858444348558995811258063185585597403/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (152858444348558995811258063185585597403/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (305509825008906070184525502192519986647/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (305509825008906070184525502192519986647/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0472 BracketBatch0029.bracket0473 (305509825008906070184525502192519986647/2000000000000000000000000000000000000000) (203631679066957166833833027213507847/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0472 BracketBatch0029.bracket0473
  (305509825008906070184525502192519986647/2000000000000000000000000000000000000000) (203631679066957166833833027213507847/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0472
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0473
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0073.rows BesselBatch0073.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (1528584443485589958112580631855855974027/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1528584443485589958112580631855855974027/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (191331909216519003224684936049507344327/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (191331909216519003224684936049507344327/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (3059239717217741983910060120251914728643/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3059239717217741983910060120251914728643/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0473 BracketBatch0029.bracket0474 (3059239717217741983910060120251914728643/20000000000000000000000000000000000000000) (102359762362808590610010151003833929/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0473 BracketBatch0029.bracket0474
  (3059239717217741983910060120251914728643/20000000000000000000000000000000000000000) (102359762362808590610010151003833929/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0473
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0474
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1530655273732152025797479488396058754613/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1530655273732152025797479488396058754613/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (1532726297632556055926855466416906971897/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1532726297632556055926855466416906971897/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0525.rows BesselBatch0525.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (306338157136470808172433495481296572651/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (306338157136470808172433495481296572651/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0474 BracketBatch0029.bracket0475 (306338157136470808172433495481296572651/2000000000000000000000000000000000000000) (411623478509641578156113443615746417/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0474 BracketBatch0029.bracket0475
  (306338157136470808172433495481296572651/2000000000000000000000000000000000000000) (411623478509641578156113443615746417/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0474
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0475
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (766363148816278027963427733208453485947/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (766363148816278027963427733208453485947/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1534797515476342246674455447173880235467/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1534797515476342246674455447173880235467/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (3067523813108898302601310913590787207361/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3067523813108898302601310913590787207361/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0475 BracketBatch0029.bracket0476 (3067523813108898302601310913590787207361/20000000000000000000000000000000000000000) (103454167249977646277880531165324383/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0475 BracketBatch0029.bracket0476
  (3067523813108898302601310913590787207361/20000000000000000000000000000000000000000) (103454167249977646277880531165324383/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0475
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0476
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (191849689434542780834306930896735029433/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (191849689434542780834306930896735029433/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (1536868927553192129450152788722487624447/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1536868927553192129450152788722487624447/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (3071666443029534376124608235896367859911/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3071666443029534376124608235896367859911/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0476 BracketBatch0029.bracket0477 (3071666443029534376124608235896367859911/20000000000000000000000000000000000000000) (104004661161776889166469317743953269/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0476 BracketBatch0029.bracket0477
  (3071666443029534376124608235896367859911/20000000000000000000000000000000000000000) (104004661161776889166469317743953269/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0476
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0477
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (384217231888298032362538197180621906111/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (384217231888298032362538197180621906111/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1538940534152928813356335084836415187539/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1538940534152928813356335084836415187539/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (3075809461706120942806487873558902811983/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3075809461706120942806487873558902811983/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0477 BracketBatch0029.bracket0478 (3075809461706120942806487873558902811983/20000000000000000000000000000000000000000) (104557357302650638353698319971028599/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0477 BracketBatch0029.bracket0478
  (3075809461706120942806487873558902811983/20000000000000000000000000000000000000000) (104557357302650638353698319971028599/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0477
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0478
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (96183783384558050834770942802275949221/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (96183783384558050834770942802275949221/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (9631327097284482686870845754485990347/62500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9631327097284482686870845754485990347/62500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (192497054357402877703479400347135852691/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (192497054357402877703479400347135852691/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0478 BracketBatch0029.bracket0479 (192497054357402877703479400347135852691/1250000000000000000000000000000000000000) (21022452324204093090200173656542373/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0478 BracketBatch0029.bracket0479
  (192497054357402877703479400347135852691/1250000000000000000000000000000000000000) (21022452324204093090200173656542373/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0478
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0479
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0074.rows BesselBatch0074.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1541012335565517229899335320717758455517/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1541012335565517229899335320717758455517/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0075.rows BesselBatch0075.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1543084332081064377956427020659442090639/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1543084332081064377956427020659442090639/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0526.rows BesselBatch0526.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (771024166911645401963940585344300136539/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (771024166911645401963940585344300136539/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0059.rows ScalarLogs0059.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0029.bracket0479 BracketBatch0030.bracket0480 (771024166911645401963940585344300136539/5000000000000000000000000000000000000000) (6604336254618130518811863474706713/156250000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0029.bracket0479 BracketBatch0030.bracket0480
  (771024166911645401963940585344300136539/5000000000000000000000000000000000000000) (6604336254618130518811863474706713/156250000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0479
