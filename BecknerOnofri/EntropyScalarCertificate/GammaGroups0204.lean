import BecknerOnofri.EntropyScalarCertificate.Bessel0255
import BecknerOnofri.EntropyScalarCertificate.Bessel0256
import BecknerOnofri.EntropyScalarCertificate.Bessel0616
import BecknerOnofri.EntropyScalarCertificate.Bessel0617
import BecknerOnofri.EntropyScalarCertificate.Brackets0102
import BecknerOnofri.EntropyScalarCertificate.Logs0204
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1632
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (19003905412483384738537020302792619348449/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19003905412483384738537020302792619348449/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (9507739525564842780336821064412877849373/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9507739525564842780336821064412877849373/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (7603876892722614059842132486323675009439/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7603876892722614059842132486323675009439/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1632 BracketBatch0102.bracket1633 (7603876892722614059842132486323675009439/4000000000000000000000000000000000000000) (374915710962239589107934643232700792021/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1632 BracketBatch0102.bracket1633
  (7603876892722614059842132486323675009439/4000000000000000000000000000000000000000) (374915710962239589107934643232700792021/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1632
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1633
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (19015479051129685560673642128825755698743/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19015479051129685560673642128825755698743/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (4756767222389727838240726439558793499717/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4756767222389727838240726439558793499717/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (38042547940688596913636547887060929697611/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38042547940688596913636547887060929697611/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1633 BracketBatch0102.bracket1634 (38042547940688596913636547887060929697611/20000000000000000000000000000000000000000) (375219432997145089937606842254580861951/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1633 BracketBatch0102.bracket1634
  (38042547940688596913636547887060929697611/20000000000000000000000000000000000000000) (375219432997145089937606842254580861951/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1633
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1634
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (3805413777911782270592581151647034799773/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3805413777911782270592581151647034799773/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (19038674963273447668797317798591886092851/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19038674963273447668797317798591886092851/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (9516435963208089755440055889206765022929/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9516435963208089755440055889206765022929/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1634 BracketBatch0102.bracket1635 (9516435963208089755440055889206765022929/5000000000000000000000000000000000000000) (187761745135710641777903044821653649203/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1634 BracketBatch0102.bracket1635
  (9516435963208089755440055889206765022929/5000000000000000000000000000000000000000) (187761745135710641777903044821653649203/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1634
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1635
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1189917185204590479299832362411992880803/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1189917185204590479299832362411992880803/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (9525148653937304113575519461220507363909/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9525148653937304113575519461220507363909/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (19044486135574027947974178360516450410333/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19044486135574027947974178360516450410333/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1635 BracketBatch0102.bracket1636 (19044486135574027947974178360516450410333/10000000000000000000000000000000000000000) (375827883315886254758331849645600473999/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1635 BracketBatch0102.bracket1636
  (19044486135574027947974178360516450410333/10000000000000000000000000000000000000000) (375827883315886254758331849645600473999/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1635
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1636
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (3810059461574921645430207784488202945563/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3810059461574921645430207784488202945563/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (19061935959062966079079565666654713000613/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19061935959062966079079565666654713000613/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (9528058316734393576557651147273931932107/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9528058316734393576557651147273931932107/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1636 BracketBatch0102.bracket1637 (9528058316734393576557651147273931932107/5000000000000000000000000000000000000000) (752265225324737821937940814203987828303/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1636 BracketBatch0102.bracket1637
  (9528058316734393576557651147273931932107/5000000000000000000000000000000000000000) (752265225324737821937940814203987828303/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1636
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1637
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (1906193595906296607907956566665471300061/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1906193595906296607907956566665471300061/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (9536795476319343047807014610370376725901/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9536795476319343047807014610370376725901/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (9533881727925413043673398721848866613103/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9533881727925413043673398721848866613103/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1637 BracketBatch0102.bracket1638 (9533881727925413043673398721848866613103/5000000000000000000000000000000000000000) (94109419710927764444705704378364198779/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1637 BracketBatch0102.bracket1638
  (9533881727925413043673398721848866613103/5000000000000000000000000000000000000000) (94109419710927764444705704378364198779/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1637
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1638
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0255.rows BesselBatch0255.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (19073590952638686095614029220740753451799/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19073590952638686095614029220740753451799/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (19085262324501858783412851033716737570437/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19085262324501858783412851033716737570437/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (9539713319285136219756720063614372755559/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9539713319285136219756720063614372755559/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1638 BracketBatch0102.bracket1639 (9539713319285136219756720063614372755559/5000000000000000000000000000000000000000) (753486164787538960011681685224387176149/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1638 BracketBatch0102.bracket1639
  (9539713319285136219756720063614372755559/5000000000000000000000000000000000000000) (753486164787538960011681685224387176149/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1638
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1639
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (9542631162250929391706425516858368785217/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9542631162250929391706425516858368785217/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0256.rows BesselBatch0256.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (19096950110652835434570321212146887957477/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19096950110652835434570321212146887957477/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0616.rows BesselBatch0616.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0617.rows BesselBatch0617.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (38182212435154694217983172245863625527911/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38182212435154694217983172245863625527911/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0204.rows ScalarLogs0204.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0102.bracket1639 BracketBatch0102.bracket1640 (38182212435154694217983172245863625527911/20000000000000000000000000000000000000000) (754097647694836056607955949687146441531/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0102.bracket1639 BracketBatch0102.bracket1640
  (38182212435154694217983172245863625527911/20000000000000000000000000000000000000000) (754097647694836056607955949687146441531/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1639
