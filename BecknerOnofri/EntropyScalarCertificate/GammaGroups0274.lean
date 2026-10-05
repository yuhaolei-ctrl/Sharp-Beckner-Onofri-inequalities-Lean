import BecknerOnofri.EntropyScalarCertificate.Bessel0342
import BecknerOnofri.EntropyScalarCertificate.Bessel0343
import BecknerOnofri.EntropyScalarCertificate.Bessel0660
import BecknerOnofri.EntropyScalarCertificate.Brackets0137
import BecknerOnofri.EntropyScalarCertificate.Logs0274
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2192
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (44360261139497475371175593087119293865877/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (44360261139497475371175593087119293865877/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (44513506787889520802848596893453788387729/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44513506787889520802848596893453788387729/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨14,by decide⟩
]
theorem midAccepted : besselPointCheck (44436883963693498087012094990286541126803/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44436883963693498087012094990286541126803/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2192 BracketBatch0137.bracket2193 (44436883963693498087012094990286541126803/5000000000000000000000000000000000000000) (1303132935592470255144325547882431695177/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2192 BracketBatch0137.bracket2193
  (44436883963693498087012094990286541126803/5000000000000000000000000000000000000000) (1303132935592470255144325547882431695177/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2192
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2193
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (17805402715155808321139438757381515355091/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (17805402715155808321139438757381515355091/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (44667832471649117341186873311480349638991/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (44667832471649117341186873311480349638991/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨19,by decide⟩
]
theorem midAccepted : besselPointCheck (178362678519077276288070940409868276053437/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (178362678519077276288070940409868276053437/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2193 BracketBatch0137.bracket2194 (178362678519077276288070940409868276053437/20000000000000000000000000000000000000000) (652699005610336066011804576348957467489/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2193 BracketBatch0137.bracket2194
  (178362678519077276288070940409868276053437/20000000000000000000000000000000000000000) (652699005610336066011804576348957467489/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2193
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2194
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (89335664943298234682373746622960699277979/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (89335664943298234682373746622960699277979/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (89646499278188940963413962832823861405819/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (89646499278188940963413962832823861405819/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨24,by decide⟩
]
theorem midAccepted : besselPointCheck (89491082110743587822893854727892280341899/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (89491082110743587822893854727892280341899/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2194 BracketBatch0137.bracket2195 (89491082110743587822893854727892280341899/10000000000000000000000000000000000000000) (1307671746092355075745041056927429872137/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2194 BracketBatch0137.bracket2195
  (89491082110743587822893854727892280341899/10000000000000000000000000000000000000000) (1307671746092355075745041056927429872137/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2194
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2195
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0342.rows BesselBatch0342.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (11205812409773617620426745354102982675727/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11205812409773617620426745354102982675727/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (22489884950466523598580413811251665274469/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (22489884950466523598580413811251665274469/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨29,by decide⟩
]
theorem midAccepted : besselPointCheck (44901509770013758839433904519457630625923/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (44901509770013758839433904519457630625923/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2195 BracketBatch0137.bracket2196 (44901509770013758839433904519457630625923/5000000000000000000000000000000000000000) (1309954202435357249991785647093562728681/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2195 BracketBatch0137.bracket2196
  (44901509770013758839433904519457630625923/5000000000000000000000000000000000000000) (1309954202435357249991785647093562728681/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2195
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2196
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (89959539801866094394321655245006661097873/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (89959539801866094394321655245006661097873/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (90274810066302114833064948331969853046071/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (90274810066302114833064948331969853046071/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨34,by decide⟩
]
theorem midAccepted : besselPointCheck (22529293733521026153423325447122064267993/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (22529293733521026153423325447122064267993/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2196 BracketBatch0137.bracket2197 (22529293733521026153423325447122064267993/2500000000000000000000000000000000000000) (656122721567445269776712211954526502913/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2196 BracketBatch0137.bracket2197
  (22529293733521026153423325447122064267993/2500000000000000000000000000000000000000) (656122721567445269776712211954526502913/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2196
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2197
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (22568702516575528708266237082992463261517/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (22568702516575528708266237082992463261517/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (11324041744991213253552443246494983059349/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11324041744991213253552443246494983059349/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨39,by decide⟩
]
theorem midAccepted : besselPointCheck (9043357201311591043074224715196485876043/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9043357201311591043074224715196485876043/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2197 BracketBatch0137.bracket2198 (9043357201311591043074224715196485876043/1000000000000000000000000000000000000000) (657272765871280380787915057187554501983/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2197 BracketBatch0137.bracket2198
  (9043357201311591043074224715196485876043/1000000000000000000000000000000000000000) (657272765871280380787915057187554501983/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2197
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2198
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (90592333959929706028419545971959864474789/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (90592333959929706028419545971959864474789/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (18182427142734319117868421870155042741713/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18182427142734319117868421870155042741713/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨44,by decide⟩
]
theorem midAccepted : besselPointCheck (90752234836800650808880827661367539091677/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (90752234836800650808880827661367539091677/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2198 BracketBatch0137.bracket2199 (90752234836800650808880827661367539091677/10000000000000000000000000000000000000000) (2633709064971077942832136109738956601403/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2198 BracketBatch0137.bracket2199
  (90752234836800650808880827661367539091677/10000000000000000000000000000000000000000) (2633709064971077942832136109738956601403/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2198
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2199
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (45456067856835797794671054675387606854281/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (45456067856835797794671054675387606854281/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0343.rows BesselBatch0343.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (91234239907100413325302001709282981233483/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (91234239907100413325302001709282981233483/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0660.rows BesselBatch0660.accepted ⟨49,by decide⟩
]
theorem midAccepted : besselPointCheck (36429275124154401782928822212011638988409/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (36429275124154401782928822212011638988409/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0274.rows ScalarLogs0274.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0137.bracket2199 BracketBatch0137.bracket2200 (36429275124154401782928822212011638988409/4000000000000000000000000000000000000000) (2638345020551773634752484924697782008967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0137.bracket2199 BracketBatch0137.bracket2200
  (36429275124154401782928822212011638988409/4000000000000000000000000000000000000000) (2638345020551773634752484924697782008967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2199
