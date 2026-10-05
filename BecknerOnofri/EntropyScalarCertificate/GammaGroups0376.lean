import BecknerOnofri.EntropyScalarCertificate.Bessel0470
import BecknerOnofri.EntropyScalarCertificate.Bessel0471
import BecknerOnofri.EntropyScalarCertificate.Bessel0723
import BecknerOnofri.EntropyScalarCertificate.Bessel0724
import BecknerOnofri.EntropyScalarCertificate.Brackets0188
import BecknerOnofri.EntropyScalarCertificate.Logs0376
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3008
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (62550120482864247027502260187822530798253/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (62550120482864247027502260187822530798253/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (98040695108956839636718709107018765716459/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (98040695108956839636718709107018765716459/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (3132404133814915609875055850407863521419669/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3132404133814915609875055850407863521419669/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3008 BracketBatch0188.bracket3009 (3132404133814915609875055850407863521419669/20000000000000000000000000000000000000000) (6800775963100884791481015398394176252433/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3008 BracketBatch0188.bracket3009
  (3132404133814915609875055850407863521419669/20000000000000000000000000000000000000000) (6800775963100884791481015398394176252433/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3008
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3009
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (1568651121743309434187499345712300251463341/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1568651121743309434187499345712300251463341/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (7867900185979472048341950030203776064603/50000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7867900185979472048341950030203776064603/50000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0723.rows BesselBatch0723.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (3142231158939203843855889351753055464383941/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3142231158939203843855889351753055464383941/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3009 BracketBatch0188.bracket3010 (3142231158939203843855889351753055464383941/20000000000000000000000000000000000000000) (6805553646392855563330739586407000329731/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3009 BracketBatch0188.bracket3010
  (3142231158939203843855889351753055464383941/20000000000000000000000000000000000000000) (6805553646392855563330739586407000329731/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3009
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3010
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1573580037195894409668390006040755212920597/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1573580037195894409668390006040755212920597/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (789270024983358666399671429567379760184519/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (789270024983358666399671429567379760184519/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (630424017432522348493546573035102946657927/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (630424017432522348493546573035102946657927/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3010 BracketBatch0188.bracket3011 (630424017432522348493546573035102946657927/4000000000000000000000000000000000000000) (34051727435602775260773687321902837123/50000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3010 BracketBatch0188.bracket3011
  (630424017432522348493546573035102946657927/4000000000000000000000000000000000000000) (34051727435602775260773687321902837123/50000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3010
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3011
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (315708009993343466559868571826951904073807/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (315708009993343466559868571826951904073807/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (79176572764174035791082632053258934276137/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (79176572764174035791082632053258934276137/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (126482860210007921944839820007997528235671/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (126482860210007921944839820007997528235671/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3011 BracketBatch0188.bracket3012 (126482860210007921944839820007997528235671/800000000000000000000000000000000000000) (3407575779905786292485350636876031733799/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3011 BracketBatch0188.bracket3012
  (126482860210007921944839820007997528235671/800000000000000000000000000000000000000) (3407575779905786292485350636876031733799/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3011
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3012
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (1583531455283480715821652641065178685522737/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1583531455283480715821652641065178685522737/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (1588554552122810277653093172960407118185559/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1588554552122810277653093172960407118185559/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (396510750925786374184343226753198225463537/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (396510750925786374184343226753198225463537/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3012 BracketBatch0188.bracket3013 (396510750925786374184343226753198225463537/2500000000000000000000000000000000000000) (6819971939469484940448348656100614733353/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3012 BracketBatch0188.bracket3013
  (396510750925786374184343226753198225463537/2500000000000000000000000000000000000000) (6819971939469484940448348656100614733353/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3012
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3013
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (397138638030702569413273293240101779546389/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (397138638030702569413273293240101779546389/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (199201205408743896661696514255552781782499/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (199201205408743896661696514255552781782499/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (795541048848190362736666321751207343111387/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (795541048848190362736666321751207343111387/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3013 BracketBatch0188.bracket3014 (795541048848190362736666321751207343111387/5000000000000000000000000000000000000000) (6824806701575558763507224390648364480733/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3013 BracketBatch0188.bracket3014
  (795541048848190362736666321751207343111387/5000000000000000000000000000000000000000) (6824806701575558763507224390648364480733/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3013
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3014
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0470.rows BesselBatch0470.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1593609643269951173293572114044422254259989/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1593609643269951173293572114044422254259989/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (799348517689804279948354406524145062975793/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (799348517689804279948354406524145062975793/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (127692267145982389327611237083708495208463/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (127692267145982389327611237083708495208463/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3014 BracketBatch0188.bracket3015 (127692267145982389327611237083708495208463/800000000000000000000000000000000000000) (42685349513064903099824912299335609247/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3014 BracketBatch0188.bracket3015
  (127692267145982389327611237083708495208463/800000000000000000000000000000000000000) (42685349513064903099824912299335609247/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3014
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3015
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (1598697035379608559896708813048290125951583/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1598697035379608559896708813048290125951583/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0471.rows BesselBatch0471.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (200477129879744771715925505682197016604773/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (200477129879744771715925505682197016604773/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0724.rows BesselBatch0724.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (3202514074417566733624112858505866258789767/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3202514074417566733624112858505866258789767/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0376.rows ScalarLogs0376.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0188.bracket3015 BracketBatch0188.bracket3016 (3202514074417566733624112858505866258789767/20000000000000000000000000000000000000000) (1708629919363859522463153663938146922663/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0188.bracket3015 BracketBatch0188.bracket3016
  (3202514074417566733624112858505866258789767/20000000000000000000000000000000000000000) (1708629919363859522463153663938146922663/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel3015
