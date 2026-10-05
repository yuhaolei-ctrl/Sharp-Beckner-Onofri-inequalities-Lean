import BecknerOnofri.EntropyScalarCertificate.Bessel0303
import BecknerOnofri.EntropyScalarCertificate.Bessel0304
import BecknerOnofri.EntropyScalarCertificate.Bessel0305
import BecknerOnofri.EntropyScalarCertificate.Bessel0640
import BecknerOnofri.EntropyScalarCertificate.Bessel0641
import BecknerOnofri.EntropyScalarCertificate.Brackets0121
import BecknerOnofri.EntropyScalarCertificate.Brackets0122
import BecknerOnofri.EntropyScalarCertificate.Logs0243
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1944
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (3871863915809753487741311785883367824763/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3871863915809753487741311785883367824763/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (19498851165436036275360322095681597679891/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (19498851165436036275360322095681597679891/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (19429085372242401857033440512549218401853/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (19429085372242401857033440512549218401853/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1944 BracketBatch0121.bracket1945 (19429085372242401857033440512549218401853/5000000000000000000000000000000000000000) (1545655309414663589798340963862018750969/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1944 BracketBatch0121.bracket1945
  (19429085372242401857033440512549218401853/5000000000000000000000000000000000000000) (1545655309414663589798340963862018750969/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1944
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1945
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0303.rows BesselBatch0303.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (38997702330872072550720644191363195359779/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (38997702330872072550720644191363195359779/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (7856204829324101950596100122220550239049/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7856204829324101950596100122220550239049/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (4892420404843286393981321550154121659689/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4892420404843286393981321550154121659689/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1945 BracketBatch0121.bracket1946 (4892420404843286393981321550154121659689/1250000000000000000000000000000000000000) (194284138447060089381695305476659269009/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1945 BracketBatch0121.bracket1946
  (4892420404843286393981321550154121659689/1250000000000000000000000000000000000000) (194284138447060089381695305476659269009/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1945
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1946
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (19640512073310254876490250305551375597621/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19640512073310254876490250305551375597621/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (7913740371893750031052705660744595211059/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (7913740371893750031052705660744595211059/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0640.rows BesselBatch0640.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (78849726006089259908244028914825727250537/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (78849726006089259908244028914825727250537/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1946 BracketBatch0121.bracket1947 (78849726006089259908244028914825727250537/20000000000000000000000000000000000000000) (195370637032368095660694977967062998881/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1946 BracketBatch0121.bracket1947
  (78849726006089259908244028914825727250537/20000000000000000000000000000000000000000) (195370637032368095660694977967062998881/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1946
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1947
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (9892175464867187538815882075930744013823/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (9892175464867187538815882075930744013823/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (39860835718292288185822089064799522317977/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (39860835718292288185822089064799522317977/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (79429537577761038341085617368522498373269/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (79429537577761038341085617368522498373269/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1947 BracketBatch0121.bracket1948 (79429537577761038341085617368522498373269/20000000000000000000000000000000000000000) (1571732284070472669845184967035848772557/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1947 BracketBatch0121.bracket1948
  (79429537577761038341085617368522498373269/20000000000000000000000000000000000000000) (1571732284070472669845184967035848772557/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1947
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1948
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (19930417859146144092911044532399761158987/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (19930417859146144092911044532399761158987/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (20078764541473456637356281253890340311813/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20078764541473456637356281253890340311813/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (100022956001549001825668314465725253677/25000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (100022956001549001825668314465725253677/25000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1948 BracketBatch0121.bracket1949 (100022956001549001825668314465725253677/25000000000000000000000000000000000000) (1580575700653680941317580692817415315881/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1948 BracketBatch0121.bracket1949
  (100022956001549001825668314465725253677/25000000000000000000000000000000000000) (1580575700653680941317580692817415315881/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1948
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1949
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (40157529082946913274712562507780680623623/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40157529082946913274712562507780680623623/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (40458888545938702258198987003125403857389/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (40458888545938702258198987003125403857389/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (20154104407221403883227887377726521120253/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20154104407221403883227887377726521120253/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1949 BracketBatch0121.bracket1950 (20154104407221403883227887377726521120253/5000000000000000000000000000000000000000) (794748198618799934579655627486280443053/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1949 BracketBatch0121.bracket1950
  (20154104407221403883227887377726521120253/5000000000000000000000000000000000000000) (794748198618799934579655627486280443053/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1949
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1950
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (20229444272969351129099493501562701928693/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (20229444272969351129099493501562701928693/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (20382512029916468553502914183303024661863/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20382512029916468553502914183303024661863/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (10152989075721454920650601921216431647639/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (10152989075721454920650601921216431647639/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1950 BracketBatch0121.bracket1951 (10152989075721454920650601921216431647639/2500000000000000000000000000000000000000) (1598495447204509783539460500426811165669/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1950 BracketBatch0121.bracket1951
  (10152989075721454920650601921216431647639/2500000000000000000000000000000000000000) (1598495447204509783539460500426811165669/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1950
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1951
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0304.rows BesselBatch0304.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (40765024059832937107005828366606049323723/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (40765024059832937107005828366606049323723/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0305.rows BesselBatch0305.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (41076049070720639400006576078686501974967/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41076049070720639400006576078686501974967/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0641.rows BesselBatch0641.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (8184107313055357650701240444529255129869/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (8184107313055357650701240444529255129869/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0243.rows ScalarLogs0243.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0121.bracket1951 BracketBatch0122.bracket1952 (8184107313055357650701240444529255129869/2000000000000000000000000000000000000000) (160757394667166630889972743357952209391/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0121.bracket1951 BracketBatch0122.bracket1952
  (8184107313055357650701240444529255129869/2000000000000000000000000000000000000000) (160757394667166630889972743357952209391/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1951
