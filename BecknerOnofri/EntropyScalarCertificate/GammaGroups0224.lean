import BecknerOnofri.EntropyScalarCertificate.Bessel0280
import BecknerOnofri.EntropyScalarCertificate.Bessel0281
import BecknerOnofri.EntropyScalarCertificate.Bessel0628
import BecknerOnofri.EntropyScalarCertificate.Bessel0629
import BecknerOnofri.EntropyScalarCertificate.Brackets0112
import BecknerOnofri.EntropyScalarCertificate.Logs0224
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1792
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (10544218435263419416885490198452918912889/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10544218435263419416885490198452918912889/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (10551565142557701028511446680993197214741/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (10551565142557701028511446680993197214741/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨62,by decide⟩
]
theorem midAccepted : besselPointCheck (2109578357782112044539693687944611612763/1000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2109578357782112044539693687944611612763/1000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1792 BracketBatch0112.bracket1793 (2109578357782112044539693687944611612763/1000000000000000000000000000000000000000) (85631898985226194625774201376485847361/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1792 BracketBatch0112.bracket1793
  (2109578357782112044539693687944611612763/1000000000000000000000000000000000000000) (85631898985226194625774201376485847361/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1792
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1793
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (21103130285115402057022893361986394429479/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21103130285115402057022893361986394429479/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (21117847100968238232196003699924321687457/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21117847100968238232196003699924321687457/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0628.rows BesselBatch0628.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨3,by decide⟩
]
theorem midAccepted : besselPointCheck (5277622173260455036152362132738839514617/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5277622173260455036152362132738839514617/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1793 BracketBatch0112.bracket1794 (5277622173260455036152362132738839514617/2500000000000000000000000000000000000000) (857048688412335716089903835084861047413/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1793 BracketBatch0112.bracket1794
  (5277622173260455036152362132738839514617/2500000000000000000000000000000000000000) (857048688412335716089903835084861047413/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1793
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1794
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (10558923550484119116098001849962160843727/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10558923550484119116098001849962160843727/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (2641573421839699723714579171505748796801/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2641573421839699723714579171505748796801/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨8,by decide⟩
]
theorem midAccepted : besselPointCheck (21125217237842918010956318535985156030931/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21125217237842918010956318535985156030931/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1794 BracketBatch0112.bracket1795 (21125217237842918010956318535985156030931/10000000000000000000000000000000000000000) (857779256159273378006737602921527045843/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1794 BracketBatch0112.bracket1795
  (21125217237842918010956318535985156030931/10000000000000000000000000000000000000000) (857779256159273378006737602921527045843/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1794
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1795
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (4226517474943519557943326674409198074881/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4226517474943519557943326674409198074881/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (5286837790792482907153836069730276558643/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5286837790792482907153836069730276558643/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨13,by decide⟩
]
theorem midAccepted : besselPointCheck (42279938537887529418331977650967096608977/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42279938537887529418331977650967096608977/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1795 BracketBatch0112.bracket1796 (42279938537887529418331977650967096608977/20000000000000000000000000000000000000000) (858510694540394340767502827819946507261/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1795 BracketBatch0112.bracket1796
  (42279938537887529418331977650967096608977/20000000000000000000000000000000000000000) (858510694540394340767502827819946507261/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1795
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1796
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (21147351163169931628615344278921106234569/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21147351163169931628615344278921106234569/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (2645267315413318446860319711362646600729/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2645267315413318446860319711362646600729/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨18,by decide⟩
]
theorem midAccepted : besselPointCheck (42309489686476479203497901969822279040401/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (42309489686476479203497901969822279040401/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1796 BracketBatch0112.bracket1797 (42309489686476479203497901969822279040401/20000000000000000000000000000000000000000) (859243005005899592026239456354599452919/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1796 BracketBatch0112.bracket1797
  (42309489686476479203497901969822279040401/20000000000000000000000000000000000000000) (859243005005899592026239456354599452919/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1796
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1797
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (21162138523306547574882557690901172805829/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21162138523306547574882557690901172805829/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (21176949512284269872806053688147510839091/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21176949512284269872806053688147510839091/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨23,by decide⟩
]
theorem midAccepted : besselPointCheck (1058477200889770436192215284476217091123/500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1058477200889770436192215284476217091123/500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1797 BracketBatch0112.bracket1798 (1058477200889770436192215284476217091123/500000000000000000000000000000000000000) (859976189008878796173734632151144668171/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1797 BracketBatch0112.bracket1798
  (1058477200889770436192215284476217091123/500000000000000000000000000000000000000) (859976189008878796173734632151144668171/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1797
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1798
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0280.rows BesselBatch0280.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (1323559344517766867050378355509219427443/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1323559344517766867050378355509219427443/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (5297946046859025431580898693749319373251/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5297946046859025431580898693749319373251/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨28,by decide⟩
]
theorem midAccepted : besselPointCheck (10592183424930092899782412115786197083023/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10592183424930092899782412115786197083023/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1798 BracketBatch0112.bracket1799 (10592183424930092899782412115786197083023/5000000000000000000000000000000000000000) (26897195250166169428794582924315300101/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1798 BracketBatch0112.bracket1799
  (10592183424930092899782412115786197083023/5000000000000000000000000000000000000000) (26897195250166169428794582924315300101/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1798
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1799
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (21191784187436101726323594774997277493001/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (21191784187436101726323594774997277493001/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0281.rows BesselBatch0281.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (21206642606271890907535308659150175116361/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (21206642606271890907535308659150175116361/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0629.rows BesselBatch0629.accepted ⟨33,by decide⟩
]
theorem midAccepted : besselPointCheck (21199213396853996316929451717073726304681/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (21199213396853996316929451717073726304681/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0224.rows ScalarLogs0224.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0112.bracket1799 BracketBatch0112.bracket1800 (21199213396853996316929451717073726304681/10000000000000000000000000000000000000000) (172289036690820779684925850009636097461/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0112.bracket1799 BracketBatch0112.bracket1800
  (21199213396853996316929451717073726304681/10000000000000000000000000000000000000000) (172289036690820779684925850009636097461/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1799
