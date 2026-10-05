import BecknerOnofri.EntropyScalarCertificate.Bessel0415
import BecknerOnofri.EntropyScalarCertificate.Bessel0416
import BecknerOnofri.EntropyScalarCertificate.Bessel0696
import BecknerOnofri.EntropyScalarCertificate.Bessel0697
import BecknerOnofri.EntropyScalarCertificate.Brackets0166
import BecknerOnofri.EntropyScalarCertificate.Logs0332
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2656
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (28216074101140475409566306505780152819279/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (28216074101140475409566306505780152819279/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (566869240336590147956947715389832609008361/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (566869240336590147956947715389832609008361/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (1131190722359399656148273845505435665393941/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1131190722359399656148273845505435665393941/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2656 BracketBatch0166.bracket2657 (1131190722359399656148273845505435665393941/20000000000000000000000000000000000000000) (652906884318681853958558721894875634847/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2656 BracketBatch0166.bracket2657
  (1131190722359399656148273845505435665393941/20000000000000000000000000000000000000000) (652906884318681853958558721894875634847/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2656
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2657
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (283434620168295073978473857694916304504179/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (283434620168295073978473857694916304504179/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (284720080221090420611257312110842049740187/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (284720080221090420611257312110842049740187/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (284077350194692747294865584902879177122183/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (284077350194692747294865584902879177122183/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2657 BracketBatch0166.bracket2658 (284077350194692747294865584902879177122183/5000000000000000000000000000000000000000) (326867315287668251033426856480991258423/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2657 BracketBatch0166.bracket2658
  (284077350194692747294865584902879177122183/5000000000000000000000000000000000000000) (326867315287668251033426856480991258423/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2657
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2658
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (569440160442180841222514624221684099480371/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (569440160442180841222514624221684099480371/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (572034559624345988403124138776355287963853/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (572034559624345988403124138776355287963853/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (1114721406314967607056287854490272839301/19531250000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1114721406314967607056287854490272839301/19531250000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2658 BracketBatch0166.bracket2659 (1114721406314967607056287854490272839301/19531250000000000000000000000000000000) (5236528229325480803310821846892508543137/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2658 BracketBatch0166.bracket2659
  (1114721406314967607056287854490272839301/19531250000000000000000000000000000000) (5236528229325480803310821846892508543137/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2658
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2659
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (11440691192486919768062482775527105759277/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11440691192486919768062482775527105759277/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (574652760989588803328663631930518637343801/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (574652760989588803328663631930518637343801/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (1146687320613934791731787770706873925307651/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1146687320613934791731787770706873925307651/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2659 BracketBatch0166.bracket2660 (1146687320613934791731787770706873925307651/20000000000000000000000000000000000000000) (5243208854542982753348159905092713691681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2659 BracketBatch0166.bracket2660
  (1146687320613934791731787770706873925307651/20000000000000000000000000000000000000000) (5243208854542982753348159905092713691681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2659
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2660
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (287326380494794401664331815965259318671899/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (287326380494794401664331815965259318671899/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (28864754680014638027429069333968676660369/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (28864754680014638027429069333968676660369/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (575973927294940781938622509304946085275589/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (575973927294940781938622509304946085275589/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2660 BracketBatch0166.bracket2661 (575973927294940781938622509304946085275589/10000000000000000000000000000000000000000) (1312479787063521812556456935914219259789/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2660 BracketBatch0166.bracket2661
  (575973927294940781938622509304946085275589/10000000000000000000000000000000000000000) (1312479787063521812556456935914219259789/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2660
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2661
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (577295093600292760548581386679373533207377/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (577295093600292760548581386679373533207377/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (579961892612589193950685823014516956698531/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (579961892612589193950685823014516956698531/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (289314246553220488624816802423472622476477/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (289314246553220488624816802423472622476477/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2661 BracketBatch0166.bracket2662 (289314246553220488624816802423472622476477/5000000000000000000000000000000000000000) (1051331868129243608570969684868436777127/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2661 BracketBatch0166.bracket2662
  (289314246553220488624816802423472622476477/5000000000000000000000000000000000000000) (1051331868129243608570969684868436777127/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2661
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2662
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0415.rows BesselBatch0415.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (18123809144143412310958931969203654896829/312500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (18123809144143412310958931969203654896829/312500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (291326749709036181624191675945093784508371/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (291326749709036181624191675945093784508371/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (116261539203066155719906917490470452571527/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (116261539203066155719906917490470452571527/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2662 BracketBatch0166.bracket2663 (116261539203066155719906917490470452571527/2000000000000000000000000000000000000000) (5263429664109678733886175687013241361527/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2662 BracketBatch0166.bracket2663
  (116261539203066155719906917490470452571527/2000000000000000000000000000000000000000) (5263429664109678733886175687013241361527/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2662
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2663
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (582653499418072363248383351890187569016739/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (582653499418072363248383351890187569016739/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0416.rows BesselBatch0416.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (292685130894743920044530392525462029830873/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (292685130894743920044530392525462029830873/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0696.rows BesselBatch0696.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (233604752241512040667488827388222325735697/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (233604752241512040667488827388222325735697/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0332.rows ScalarLogs0332.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0166.bracket2663 BracketBatch0166.bracket2664 (233604752241512040667488827388222325735697/4000000000000000000000000000000000000000) (5270230353251494852979714869567591215939/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0166.bracket2663 BracketBatch0166.bracket2664
  (233604752241512040667488827388222325735697/4000000000000000000000000000000000000000) (5270230353251494852979714869567591215939/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2663
