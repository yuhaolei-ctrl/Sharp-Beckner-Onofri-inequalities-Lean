import BecknerOnofri.EntropyScalarCertificate.Bessel0375
import BecknerOnofri.EntropyScalarCertificate.Bessel0376
import BecknerOnofri.EntropyScalarCertificate.Bessel0676
import BecknerOnofri.EntropyScalarCertificate.Bessel0677
import BecknerOnofri.EntropyScalarCertificate.Brackets0150
import BecknerOnofri.EntropyScalarCertificate.Logs0300
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2400
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (262774645471097277915329370330881820893229/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (262774645471097277915329370330881820893229/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (65830709316507229464525788884824097665959/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (65830709316507229464525788884824097665959/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (105219496547425239154686505174035642311413/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (105219496547425239154686505174035642311413/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2400 BracketBatch0150.bracket2401 (105219496547425239154686505174035642311413/4000000000000000000000000000000000000000) (513372485823730014209989055233357895091/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2400 BracketBatch0150.bracket2401
  (105219496547425239154686505174035642311413/4000000000000000000000000000000000000000) (513372485823730014209989055233357895091/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2400
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2401
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (263322837266028917858103155539296390663833/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (263322837266028917858103155539296390663833/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (8246041642422843854606680814313760769929/312500000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8246041642422843854606680814313760769929/312500000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (527196169823559921205516941597336735301561/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (527196169823559921205516941597336735301561/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2401 BracketBatch0150.bracket2402 (527196169823559921205516941597336735301561/20000000000000000000000000000000000000000) (20549853170283375782793939845330605311/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2401 BracketBatch0150.bracket2402
  (527196169823559921205516941597336735301561/20000000000000000000000000000000000000000) (20549853170283375782793939845330605311/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2401
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2402
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (10554933302301240133896551442321613785509/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10554933302301240133896551442321613785509/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (5288522917879509149393766170237093145103/200000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5288522917879509149393766170237093145103/200000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (4226395827612051686536816756559160015143/160000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4226395827612051686536816756559160015143/160000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2402 BracketBatch0150.bracket2403 (4226395827612051686536816756559160015143/160000000000000000000000000000000000000) (2056484026263659955420545006429250997997/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2402 BracketBatch0150.bracket2403
  (4226395827612051686536816756559160015143/160000000000000000000000000000000000000) (2056484026263659955420545006429250997997/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2402
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2403
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (264426145893975457469688308511854657255147/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (264426145893975457469688308511854657255147/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (52996258389301056681771958228339817649913/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52996258389301056681771958228339817649913/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (66175929730060092609818512456694218188089/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (66175929730060092609818512456694218188089/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2403 BracketBatch0150.bracket2404 (66175929730060092609818512456694218188089/2500000000000000000000000000000000000000) (1028993042508552976058758013070934739867/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2403 BracketBatch0150.bracket2404
  (66175929730060092609818512456694218188089/2500000000000000000000000000000000000000) (1028993042508552976058758013070934739867/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2403
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2404
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (132490645973252641704429895570849544124781/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (132490645973252641704429895570849544124781/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (265538785510332355985692385493336142584747/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (265538785510332355985692385493336142584747/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (530520077456837639394552176635035230834309/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (530520077456837639394552176635035230834309/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2404 BracketBatch0150.bracket2405 (530520077456837639394552176635035230834309/20000000000000000000000000000000000000000) (2059491507390705697396866867398767723083/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2404 BracketBatch0150.bracket2405
  (530520077456837639394552176635035230834309/20000000000000000000000000000000000000000) (2059491507390705697396866867398767723083/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2404
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2405
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (33192348188791544498211548186667017823093/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (33192348188791544498211548186667017823093/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (6652466037651292763679670864129378762159/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6652466037651292763679670864129378762159/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (2076708699282750259894059453353559738559/78125000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2076708699282750259894059453353559738559/78125000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2405 BracketBatch0150.bracket2406 (2076708699282750259894059453353559738559/78125000000000000000000000000000000000) (4122000615145965259842200427747544925007/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2405 BracketBatch0150.bracket2406
  (2076708699282750259894059453353559738559/78125000000000000000000000000000000000) (4122000615145965259842200427747544925007/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2405
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2406
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0375.rows BesselBatch0375.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (266098641506051710547186834565175150486357/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (266098641506051710547186834565175150486357/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (266660874980972574389613265463581092949859/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (266660874980972574389613265463581092949859/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (66594939560878035617100012503594530429527/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (66594939560878035617100012503594530429527/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2406 BracketBatch0150.bracket2407 (66594939560878035617100012503594530429527/2500000000000000000000000000000000000000) (4125024999679283977883158375945378638789/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2406 BracketBatch0150.bracket2407
  (66594939560878035617100012503594530429527/2500000000000000000000000000000000000000) (4125024999679283977883158375945378638789/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2406
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2407
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (8333152343155392949675414545736909154683/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8333152343155392949675414545736909154683/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0376.rows BesselBatch0376.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (133612750555233195036027536039070935094037/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (133612750555233195036027536039070935094037/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0676.rows BesselBatch0676.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0677.rows BesselBatch0677.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (53388637609143896446166833754172296313793/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (53388637609143896446166833754172296313793/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0300.rows ScalarLogs0300.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0150.bracket2407 BracketBatch0150.bracket2408 (53388637609143896446166833754172296313793/2000000000000000000000000000000000000000) (1032014049277132961711622545888483006199/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0150.bracket2407 BracketBatch0150.bracket2408
  (53388637609143896446166833754172296313793/2000000000000000000000000000000000000000) (1032014049277132961711622545888483006199/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2407
