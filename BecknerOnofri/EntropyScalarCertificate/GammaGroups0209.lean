import BecknerOnofri.EntropyScalarCertificate.Bessel0261
import BecknerOnofri.EntropyScalarCertificate.Bessel0262
import BecknerOnofri.EntropyScalarCertificate.Bessel0619
import BecknerOnofri.EntropyScalarCertificate.Bessel0620
import BecknerOnofri.EntropyScalarCertificate.Brackets0104
import BecknerOnofri.EntropyScalarCertificate.Brackets0105
import BecknerOnofri.EntropyScalarCertificate.Logs0209
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1672
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (9739923408367480063908629628821338704493/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9739923408367480063908629628821338704493/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (9746048573564595283290087470170546390317/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9746048573564595283290087470170546390317/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (1948597198193207534719871709899188509481/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1948597198193207534719871709899188509481/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1672 BracketBatch0104.bracket1673 (1948597198193207534719871709899188509481/1000000000000000000000000000000000000000) (774662834633669725742764065615280274031/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1672 BracketBatch0104.bracket1673
  (1948597198193207534719871709899188509481/1000000000000000000000000000000000000000) (774662834633669725742764065615280274031/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1672
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1673
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (19492097147129190566580174940341092780631/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19492097147129190566580174940341092780631/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (4876091294490689336208220902312160945881/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4876091294490689336208220902312160945881/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (7799292465018389582282611709917947312831/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7799292465018389582282611709917947312831/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1673 BracketBatch0104.bracket1674 (7799292465018389582282611709917947312831/4000000000000000000000000000000000000000) (48456121643129386811903155958707071193/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1673 BracketBatch0104.bracket1674
  (7799292465018389582282611709917947312831/4000000000000000000000000000000000000000) (48456121643129386811903155958707071193/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1673
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1674
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (19504365177962757344832883609248643783521/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19504365177962757344832883609248643783521/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (975832547448357229404216422720508495089/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (975832547448357229404216422720508495089/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (39021016126929901932917212063658813685301/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39021016126929901932917212063658813685301/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1674 BracketBatch0104.bracket1675 (39021016126929901932917212063658813685301/20000000000000000000000000000000000000000) (775933772509604349618587496385929981343/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1674 BracketBatch0104.bracket1675
  (39021016126929901932917212063658813685301/20000000000000000000000000000000000000000) (775933772509604349618587496385929981343/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1674
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1675
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (19516650948967144588084328454410169901777/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19516650948967144588084328454410169901777/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (19528954499987108333432187415322458701723/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19528954499987108333432187415322458701723/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (78091210897908505843033031739465257207/40000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (78091210897908505843033031739465257207/40000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1675 BracketBatch0104.bracket1676 (78091210897908505843033031739465257207/40000000000000000000000000000000000000) (97071289304765851146391481338499679577/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1675 BracketBatch0104.bracket1676
  (78091210897908505843033031739465257207/40000000000000000000000000000000000000) (97071289304765851146391481338499679577/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1675
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1676
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0261.rows BesselBatch0261.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (488223862499677708335804685383061467543/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (488223862499677708335804685383061467543/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (19541275870981065902312181278481043127353/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19541275870981065902312181278481043127353/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (39070230370968174235744368693803501829073/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39070230370968174235744368693803501829073/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1676 BracketBatch0104.bracket1677 (39070230370968174235744368693803501829073/20000000000000000000000000000000000000000) (388603786611844547981863196020977665741/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1676 BracketBatch0104.bracket1677
  (39070230370968174235744368693803501829073/20000000000000000000000000000000000000000) (388603786611844547981863196020977665741/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1676
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1677
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (390825517419621318046243625569620862547/200000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (390825517419621318046243625569620862547/200000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (19553615102021486880476115833648587301657/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19553615102021486880476115833648587301657/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0619.rows BesselBatch0619.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (39094890973002552782788297112129630429007/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (39094890973002552782788297112129630429007/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1677 BracketBatch0104.bracket1678 (39094890973002552782788297112129630429007/20000000000000000000000000000000000000000) (777845550016544308679923699633928653317/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1677 BracketBatch0104.bracket1678
  (39094890973002552782788297112129630429007/20000000000000000000000000000000000000000) (777845550016544308679923699633928653317/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1677
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1678
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (9776807551010743440238057916824293650827/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9776807551010743440238057916824293650827/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (9782986116647642856622515497456586946369/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (9782986116647642856622515497456586946369/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (4889948416914596574215143353570220149299/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4889948416914596574215143353570220149299/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1678 BracketBatch0104.bracket1679 (4889948416914596574215143353570220149299/2500000000000000000000000000000000000000) (9731053074614397172096331634584537787/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1678 BracketBatch0104.bracket1679
  (4889948416914596574215143353570220149299/2500000000000000000000000000000000000000) (9731053074614397172096331634584537787/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1678
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1679
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (3913194446659057142649006198982634778547/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3913194446659057142649006198982634778547/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0262.rows BesselBatch0262.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (19578347305104215924132018039399519087629/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19578347305104215924132018039399519087629/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0620.rows BesselBatch0620.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (9786079884599875409344262258578173245091/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (9786079884599875409344262258578173245091/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0209.rows ScalarLogs0209.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0104.bracket1679 BracketBatch0105.bracket1680 (9786079884599875409344262258578173245091/5000000000000000000000000000000000000000) (38956183111809085835855723692801037707/500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0104.bracket1679 BracketBatch0105.bracket1680
  (9786079884599875409344262258578173245091/5000000000000000000000000000000000000000) (38956183111809085835855723692801037707/500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1679
