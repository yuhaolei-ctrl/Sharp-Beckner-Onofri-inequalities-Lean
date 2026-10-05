import BecknerOnofri.EntropyScalarCertificate.Bessel0345
import BecknerOnofri.EntropyScalarCertificate.Bessel0346
import BecknerOnofri.EntropyScalarCertificate.Bessel0661
import BecknerOnofri.EntropyScalarCertificate.Bessel0662
import BecknerOnofri.EntropyScalarCertificate.Brackets0138
import BecknerOnofri.EntropyScalarCertificate.Logs0276
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2208
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (93897030999964182073163941518309449212263/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (93897030999964182073163941518309449212263/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (94241023985418123115577963562426462348567/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (94241023985418123115577963562426462348567/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (18813805498538230518874190508073591156083/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18813805498538230518874190508073591156083/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2208 BracketBatch0138.bracket2209 (18813805498538230518874190508073591156083/2000000000000000000000000000000000000000) (2680874439669572349912717261608260203097/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2208 BracketBatch0138.bracket2209
  (18813805498538230518874190508073591156083/2000000000000000000000000000000000000000) (2680874439669572349912717261608260203097/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2208
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2209
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (23560255996354530778894490890606615587141/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (23560255996354530778894490890606615587141/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (47293792918566682439803046998720241182113/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (47293792918566682439803046998720241182113/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (18882860982255148799518405755986694471279/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (18882860982255148799518405755986694471279/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2209 BracketBatch0138.bracket2210 (18882860982255148799518405755986694471279/2000000000000000000000000000000000000000) (671423007354686175247098573635353930287/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2209 BracketBatch0138.bracket2210
  (18882860982255148799518405755986694471279/2000000000000000000000000000000000000000) (671423007354686175247098573635353930287/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2209
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2210
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (94587585837133364879606093997440482364223/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (94587585837133364879606093997440482364223/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (18987349083419120373339829984528564168231/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (18987349083419120373339829984528564168231/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (94762165627114483373152621960041651602689/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (94762165627114483373152621960041651602689/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2210 BracketBatch0138.bracket2211 (94762165627114483373152621960041651602689/10000000000000000000000000000000000000000) (2690528991897922612328678544937137542421/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2210 BracketBatch0138.bracket2211
  (94762165627114483373152621960041651602689/10000000000000000000000000000000000000000) (2690528991897922612328678544937137542421/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2210
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2211
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (1483386647142118779167174217541294075643/156250000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1483386647142118779167174217541294075643/156250000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (47644266010654436117791067739857854509079/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (47644266010654436117791067739857854509079/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (19022527743840447410228128540235852985931/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19022527743840447410228128540235852985931/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2211 BracketBatch0138.bracket2212 (19022527743840447410228128540235852985931/2000000000000000000000000000000000000000) (2695385472369979129953518806266030318839/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2211 BracketBatch0138.bracket2212
  (19022527743840447410228128540235852985931/2000000000000000000000000000000000000000) (2695385472369979129953518806266030318839/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2211
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2212
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (19057706404261774447116427095943141803631/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19057706404261774447116427095943141803631/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (95642975387984569523317320228646015284027/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (95642975387984569523317320228646015284027/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (95465753704646720879449727854180862151091/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (95465753704646720879449727854180862151091/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2212 BracketBatch0138.bracket2213 (95465753704646720879449727854180862151091/10000000000000000000000000000000000000000) (675065404417834645966550928078344591519/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2212 BracketBatch0138.bracket2213
  (95465753704646720879449727854180862151091/10000000000000000000000000000000000000000) (675065404417834645966550928078344591519/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2212
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2213
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (11955371923498071190414665028580751910503/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (11955371923498071190414665028580751910503/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (96000105705916568357721626987639453250811/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (96000105705916568357721626987639453250811/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (38328616218780227576207789443257093706967/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38328616218780227576207789443257093706967/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2213 BracketBatch0138.bracket2214 (38328616218780227576207789443257093706967/4000000000000000000000000000000000000000) (1352578788116773335184941046665344637083/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2213 BracketBatch0138.bracket2214
  (38328616218780227576207789443257093706967/4000000000000000000000000000000000000000) (1352578788116773335184941046665344637083/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2213
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2214
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0345.rows BesselBatch0345.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (12000013213239571044715203373454931656351/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12000013213239571044715203373454931656351/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (96359953623047417764534589617742412708027/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (96359953623047417764534589617742412708027/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (38472011865792797224451243321076373191767/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (38472011865792797224451243321076373191767/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2214 BracketBatch0138.bracket2215 (38472011865792797224451243321076373191767/4000000000000000000000000000000000000000) (2710073498105184691372606632961413137843/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2214 BracketBatch0138.bracket2215
  (38472011865792797224451243321076373191767/4000000000000000000000000000000000000000) (2710073498105184691372606632961413137843/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2214
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2215
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (12044994202880927220566823702217801588503/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12044994202880927220566823702217801588503/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0346.rows BesselBatch0346.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (12090318781903838365976756469288105515279/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12090318781903838365976756469288105515279/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0661.rows BesselBatch0661.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0662.rows BesselBatch0662.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (12067656492392382793271790085752953551891/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12067656492392382793271790085752953551891/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0276.rows ScalarLogs0276.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0138.bracket2215 BracketBatch0138.bracket2216 (12067656492392382793271790085752953551891/1250000000000000000000000000000000000000) (33937619187176671889984304520534110633/125000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0138.bracket2215 BracketBatch0138.bracket2216
  (12067656492392382793271790085752953551891/1250000000000000000000000000000000000000) (33937619187176671889984304520534110633/125000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2215
