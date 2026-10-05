module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0417
public import BecknerOnofri.EntropyScalarCertificate.Bessel0418
public import BecknerOnofri.EntropyScalarCertificate.Bessel0697
public import BecknerOnofri.EntropyScalarCertificate.Bessel0698
public import BecknerOnofri.EntropyScalarCertificate.Brackets0167
public import BecknerOnofri.EntropyScalarCertificate.Logs0334
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2672
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨36,by decide⟩
]
theorem leftAccepted : besselPointCheck (608053922310568464831095165530719518340227/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (608053922310568464831095165530719518340227/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨51,by decide⟩
]
theorem rightAccepted : besselPointCheck (611013865077995748084106920411441242588811/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (611013865077995748084106920411441242588811/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨46,by decide⟩
]
theorem midAccepted : besselPointCheck (609533893694282106457601042971080380464519/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (609533893694282106457601042971080380464519/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2672 BracketBatch0167.bracket2673 (609533893694282106457601042971080380464519/10000000000000000000000000000000000000000) (5332842834485312752245137706602094749681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2672 BracketBatch0167.bracket2673
  (609533893694282106457601042971080380464519/10000000000000000000000000000000000000000) (5332842834485312752245137706602094749681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2672
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2673
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨46,by decide⟩
]
theorem leftAccepted : besselPointCheck (76376733134749468510513365051430155323601/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (76376733134749468510513365051430155323601/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨61,by decide⟩
]
theorem rightAccepted : besselPointCheck (307001413635734866629856216753636651524861/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (307001413635734866629856216753636651524861/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨51,by decide⟩
]
theorem midAccepted : besselPointCheck (122501669234946548134381935391871454563853/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (122501669234946548134381935391871454563853/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2673 BracketBatch0167.bracket2674 (122501669234946548134381935391871454563853/2000000000000000000000000000000000000000) (2669980290060565691501546170125751848463/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2673 BracketBatch0167.bracket2674
  (122501669234946548134381935391871454563853/2000000000000000000000000000000000000000) (2669980290060565691501546170125751848463/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2673
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2674
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨56,by decide⟩
]
theorem leftAccepted : besselPointCheck (614002827271469733259712433507273303049719/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (614002827271469733259712433507273303049719/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨7,by decide⟩
]
theorem rightAccepted : besselPointCheck (308510618874722237195205096661601643859421/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (308510618874722237195205096661601643859421/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨56,by decide⟩
]
theorem midAccepted : besselPointCheck (1231024065020914207650122626830476590768561/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1231024065020914207650122626830476590768561/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2674 BracketBatch0167.bracket2675 (1231024065020914207650122626830476590768561/20000000000000000000000000000000000000000) (668388927715137958201410816608421889149/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2674 BracketBatch0167.bracket2675
  (1231024065020914207650122626830476590768561/20000000000000000000000000000000000000000) (668388927715137958201410816608421889149/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2674
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2675
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0417.rows BesselBatch0417.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨2,by decide⟩
]
theorem leftAccepted : besselPointCheck (617021237749444474390410193323203287718839/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (617021237749444474390410193323203287718839/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨17,by decide⟩
]
theorem rightAccepted : besselPointCheck (310034766931310329358446727578030622105189/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (310034766931310329358446727578030622105189/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨61,by decide⟩
]
theorem midAccepted : besselPointCheck (1237090771612065133107303648479264531929217/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1237090771612065133107303648479264531929217/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2675 BracketBatch0167.bracket2676 (1237090771612065133107303648479264531929217/20000000000000000000000000000000000000000) (1338573905329689404532844086663182678179/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2675 BracketBatch0167.bracket2676
  (1237090771612065133107303648479264531929217/20000000000000000000000000000000000000000) (1338573905329689404532844086663182678179/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2675
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2676
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨12,by decide⟩
]
theorem leftAccepted : besselPointCheck (4960556270900965269735147641248489953683/80000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (4960556270900965269735147641248489953683/80000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨27,by decide⟩
]
theorem rightAccepted : besselPointCheck (124629632333039104585496887924707656819539/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (124629632333039104585496887924707656819539/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0697.rows BesselBatch0697.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨2,by decide⟩
]
theorem midAccepted : besselPointCheck (124321769552781618164437789477959952830807/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (124321769552781618164437789477959952830807/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2676 BracketBatch0167.bracket2677 (124321769552781618164437789477959952830807/2000000000000000000000000000000000000000) (5361513443273686162535834808835984804527/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2676 BracketBatch0167.bracket2677
  (124321769552781618164437789477959952830807/2000000000000000000000000000000000000000) (5361513443273686162535834808835984804527/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2676
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2677
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨22,by decide⟩
]
theorem leftAccepted : besselPointCheck (155787040416298880731871109905884571024423/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (155787040416298880731871109905884571024423/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨37,by decide⟩
]
theorem rightAccepted : besselPointCheck (313128788066225133442379491630979986286247/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (313128788066225133442379491630979986286247/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨7,by decide⟩
]
theorem midAccepted : besselPointCheck (624702868898822894906121711442749128335093/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (624702868898822894906121711442749128335093/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2677 BracketBatch0167.bracket2678 (624702868898822894906121711442749128335093/10000000000000000000000000000000000000000) (5368765154272100044412474021468431614241/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2677 BracketBatch0167.bracket2678
  (624702868898822894906121711442749128335093/10000000000000000000000000000000000000000) (5368765154272100044412474021468431614241/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2677
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2678
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨32,by decide⟩
]
theorem leftAccepted : besselPointCheck (626257576132450266884758983261959972572491/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (626257576132450266884758983261959972572491/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨47,by decide⟩
]
theorem rightAccepted : besselPointCheck (314699120692448945943324869759202295723597/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (314699120692448945943324869759202295723597/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨12,by decide⟩
]
theorem midAccepted : besselPointCheck (251131163503469631754281744556072912803937/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (251131163503469631754281744556072912803937/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2678 BracketBatch0167.bracket2679 (251131163503469631754281744556072912803937/4000000000000000000000000000000000000000) (1344012755831455210046557333604341293857/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2678 BracketBatch0167.bracket2679
  (251131163503469631754281744556072912803937/4000000000000000000000000000000000000000) (1344012755831455210046557333604341293857/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2678
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2679
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨42,by decide⟩
]
theorem leftAccepted : besselPointCheck (629398241384897891886649739518404591447191/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (629398241384897891886649739518404591447191/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0418.rows BesselBatch0418.accepted ⟨57,by decide⟩
]
theorem rightAccepted : besselPointCheck (126514126183844679532548362044946701374441/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (126514126183844679532548362044946701374441/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0698.rows BesselBatch0698.accepted ⟨17,by decide⟩
]
theorem midAccepted : besselPointCheck (315492218076030322387347887435784524579849/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (315492218076030322387347887435784524579849/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0334.rows ScalarLogs0334.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0167.bracket2679 BracketBatch0167.bracket2680 (315492218076030322387347887435784524579849/5000000000000000000000000000000000000000) (538337132176960453930189619662358157201/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0167.bracket2679 BracketBatch0167.bracket2680
  (315492218076030322387347887435784524579849/5000000000000000000000000000000000000000) (538337132176960453930189619662358157201/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2679
