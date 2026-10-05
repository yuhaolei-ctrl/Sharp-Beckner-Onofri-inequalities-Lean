import BecknerOnofri.EntropyScalarCertificate.Bessel0037
import BecknerOnofri.EntropyScalarCertificate.Bessel0038
import BecknerOnofri.EntropyScalarCertificate.Bessel0507
import BecknerOnofri.EntropyScalarCertificate.Bessel0508
import BecknerOnofri.EntropyScalarCertificate.Brackets0015
import BecknerOnofri.EntropyScalarCertificate.Logs0030
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0240
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (26268957487929964234986132596427918923/250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (26268957487929964234986132596427918923/250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (131598953644711172737571653724068105017/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (131598953644711172737571653724068105017/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (16433983817772562119531394794137981227/156250000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (16433983817772562119531394794137981227/156250000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0240 BracketBatch0015.bracket0241 (16433983817772562119531394794137981227/156250000000000000000000000000000000000) (92899799375078305735467902117241883/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0240 BracketBatch0015.bracket0241
  (16433983817772562119531394794137981227/156250000000000000000000000000000000000) (92899799375078305735467902117241883/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0240
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0241
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (1052791629157689381900573229792544840133/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1052791629157689381900573229792544840133/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (52741254417461488616386490873124037363/500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (52741254417461488616386490873124037363/500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (2107616717506919154228303047255025587393/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2107616717506919154228303047255025587393/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0241 BracketBatch0015.bracket0242 (2107616717506919154228303047255025587393/20000000000000000000000000000000000000000) (93617762439834453214273300771555251/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0241 BracketBatch0015.bracket0242
  (2107616717506919154228303047255025587393/20000000000000000000000000000000000000000) (93617762439834453214273300771555251/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0241
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0242
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (1054825088349229772327729817462480747257/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1054825088349229772327729817462480747257/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (528429338677304858176039660732197063361/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (528429338677304858176039660732197063361/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (2111683765703839488679809138926874873979/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2111683765703839488679809138926874873979/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0242 BracketBatch0015.bracket0243 (2111683765703839488679809138926874873979/20000000000000000000000000000000000000000) (2948120948398421752963653040345513/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0242 BracketBatch0015.bracket0243
  (2111683765703839488679809138926874873979/20000000000000000000000000000000000000000) (2948120948398421752963653040345513/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0242
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0243
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0037.rows BesselBatch0037.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (1056858677354609716352079321464394126719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1056858677354609716352079321464394126719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (529446198218354751109605076370701281361/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (529446198218354751109605076370701281361/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (2115751073791319218571289474205796689441/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2115751073791319218571289474205796689441/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0243 BracketBatch0015.bracket0244 (2115751073791319218571289474205796689441/20000000000000000000000000000000000000000) (95066139129546637243668053117678671/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0243 BracketBatch0015.bracket0244
  (2115751073791319218571289474205796689441/20000000000000000000000000000000000000000) (95066139129546637243668053117678671/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0243
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0244
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (1058892396436709502219210152741402562719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1058892396436709502219210152741402562719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (66307890366156245523605190765234630519/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (66307890366156245523605190765234630519/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0507.rows BesselBatch0507.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (2119818642295209430596893204985156651023/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2119818642295209430596893204985156651023/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0244 BracketBatch0015.bracket0245 (2119818642295209430596893204985156651023/20000000000000000000000000000000000000000) (47898292420951725602775479338891157/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0244 BracketBatch0015.bracket0245
  (2119818642295209430596893204985156651023/20000000000000000000000000000000000000000) (47898292420951725602775479338891157/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0244
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0245
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (1060926245858499928377683052243754088301/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1060926245858499928377683052243754088301/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (1062960225883042501260788403962216619909/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1062960225883042501260788403962216619909/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (212388647174154242963847145620597070821/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (212388647174154242963847145620597070821/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0245 BracketBatch0015.bracket0246 (212388647174154242963847145620597070821/2000000000000000000000000000000000000000) (48265611752017680164471895158367279/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0245 BracketBatch0015.bracket0246
  (212388647174154242963847145620597070821/2000000000000000000000000000000000000000) (48265611752017680164471895158367279/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0245
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0246
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (531480112941521250630394201981108309953/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (531480112941521250630394201981108309953/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (532497168386744816610940746075955888701/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (532497168386744816610940746075955888701/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (531988640664133033620667474028532099327/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (531988640664133033620667474028532099327/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0246 BracketBatch0015.bracket0247 (531988640664133033620667474028532099327/5000000000000000000000000000000000000000) (607937944619246341248238647469449/62500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0246 BracketBatch0015.bracket0247
  (531988640664133033620667474028532099327/5000000000000000000000000000000000000000) (607937944619246341248238647469449/62500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0246
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0247
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (1064994336773489633221881492151911777399/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1064994336773489633221881492151911777399/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0038.rows BesselBatch0038.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (533514289396542420311832492684968711867/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (533514289396542420311832492684968711867/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0508.rows BesselBatch0508.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (2132022915566574473845546477521849201133/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2132022915566574473845546477521849201133/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0030.rows ScalarLogs0030.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0015.bracket0247 BracketBatch0015.bracket0248 (2132022915566574473845546477521849201133/20000000000000000000000000000000000000000) (19602628814921120537000088581898017/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0015.bracket0247 BracketBatch0015.bracket0248
  (2132022915566574473845546477521849201133/20000000000000000000000000000000000000000) (19602628814921120537000088581898017/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0247
