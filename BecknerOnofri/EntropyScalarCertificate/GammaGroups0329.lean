module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0411
public import BecknerOnofri.EntropyScalarCertificate.Bessel0412
public import BecknerOnofri.EntropyScalarCertificate.Bessel0694
public import BecknerOnofri.EntropyScalarCertificate.Bessel0695
public import BecknerOnofri.EntropyScalarCertificate.Brackets0164
public import BecknerOnofri.EntropyScalarCertificate.Brackets0165
public import BecknerOnofri.EntropyScalarCertificate.Logs0329
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2632
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (101877884377112292308020512597292107230227/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (101877884377112292308020512597292107230227/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (255731691885423602878921519845657161281533/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (255731691885423602878921519845657161281533/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (1020852805656408667297945602677774858714201/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1020852805656408667297945602677774858714201/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2632 BracketBatch0164.bracket2633 (1020852805656408667297945602677774858714201/20000000000000000000000000000000000000000) (5072533913220983811184705167947140471457/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2632 BracketBatch0164.bracket2633
  (1020852805656408667297945602677774858714201/20000000000000000000000000000000000000000) (5072533913220983811184705167947140471457/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2632
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2633
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (511463383770847205757843039691314322563063/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (511463383770847205757843039691314322563063/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (128388586415704322684007083711883409773819/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (128388586415704322684007083711883409773819/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (1025017729433664496493871374538847961658339/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1025017729433664496493871374538847961658339/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2633 BracketBatch0164.bracket2634 (1025017729433664496493871374538847961658339/20000000000000000000000000000000000000000) (2539258686396150042890494094426070867749/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2633 BracketBatch0164.bracket2634
  (1025017729433664496493871374538847961658339/20000000000000000000000000000000000000000) (2539258686396150042890494094426070867749/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2633
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2634
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (513554345662817290736028334847533639095273/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (513554345662817290736028334847533639095273/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (103132503487609517468423726733803151264471/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (103132503487609517468423726733803151264471/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (257304215775216219519536742129137348854407/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (257304215775216219519536742129137348854407/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2634 BracketBatch0164.bracket2635 (257304215775216219519536742129137348854407/5000000000000000000000000000000000000000) (5084525242725682833771064668231265182669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2634 BracketBatch0164.bracket2635
  (257304215775216219519536742129137348854407/5000000000000000000000000000000000000000) (5084525242725682833771064668231265182669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2634
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2635
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (32228907339877974208882414604313484770147/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32228907339877974208882414604313484770147/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (1618087851381713418550679654954846993241/31250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1618087851381713418550679654954846993241/31250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (64590664367512242579896007703410424634967/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64590664367512242579896007703410424634967/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2635 BracketBatch0164.bracket2636 (64590664367512242579896007703410424634967/1250000000000000000000000000000000000000) (1018111540389710972228145107598526602019/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2635 BracketBatch0164.bracket2636
  (64590664367512242579896007703410424634967/1250000000000000000000000000000000000000) (1018111540389710972228145107598526602019/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2635
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2636
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0411.rows BesselBatch0411.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (517788112442148293936217489585551037837117/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (517788112442148293936217489585551037837117/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (8123927305652118795443210646276871721783/156250000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8123927305652118795443210646276871721783/156250000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (1037719460003883896844582970947270828031229/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1037719460003883896844582970947270828031229/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2636 BracketBatch0164.bracket2637 (1037719460003883896844582970947270828031229/20000000000000000000000000000000000000000) (127415373278737064889158345659767164029/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2636 BracketBatch0164.bracket2637
  (1037719460003883896844582970947270828031229/20000000000000000000000000000000000000000) (127415373278737064889158345659767164029/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2636
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2637
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (519931347561735602908365481361719790194109/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (519931347561735602908365481361719790194109/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (522092443298202658879272674298092315993021/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (522092443298202658879272674298092315993021/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0694.rows BesselBatch0694.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (104202379085993826178763815565981210618713/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (104202379085993826178763815565981210618713/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2637 BracketBatch0164.bracket2638 (104202379085993826178763815565981210618713/2000000000000000000000000000000000000000) (1275674278199071489312376590112784062327/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2637 BracketBatch0164.bracket2638
  (104202379085993826178763815565981210618713/2000000000000000000000000000000000000000) (1275674278199071489312376590112784062327/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2637
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2638
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (261046221649101329439636337149046157996509/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (261046221649101329439636337149046157996509/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (524271623843342507483502730438375424247997/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (524271623843342507483502730438375424247997/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (209272813428309033272555080947293548048203/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (209272813428309033272555080947293548048203/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2638 BracketBatch0164.bracket2639 (209272813428309033272555080947293548048203/4000000000000000000000000000000000000000) (319300276947137988748455932918589283351/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2638 BracketBatch0164.bracket2639
  (209272813428309033272555080947293548048203/4000000000000000000000000000000000000000) (319300276947137988748455932918589283351/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2638
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2639
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (262135811921671253741751365219187712123997/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (262135811921671253741751365219187712123997/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0412.rows BesselBatch0412.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (263234558578438752523178619298090124729583/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (263234558578438752523178619298090124729583/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0695.rows BesselBatch0695.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (26268518525005500313246499225863891842679/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (26268518525005500313246499225863891842679/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0329.rows ScalarLogs0329.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0164.bracket2639 BracketBatch0165.bracket2640 (26268518525005500313246499225863891842679/500000000000000000000000000000000000000) (5114937072304134100844082173573940678033/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0164.bracket2639 BracketBatch0165.bracket2640
  (26268518525005500313246499225863891842679/500000000000000000000000000000000000000) (5114937072304134100844082173573940678033/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2639
