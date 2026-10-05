module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0318
public import BecknerOnofri.EntropyScalarCertificate.Bessel0319
public import BecknerOnofri.EntropyScalarCertificate.Bessel0320
public import BecknerOnofri.EntropyScalarCertificate.Bessel0648
public import BecknerOnofri.EntropyScalarCertificate.Brackets0127
public import BecknerOnofri.EntropyScalarCertificate.Brackets0128
public import BecknerOnofri.EntropyScalarCertificate.Logs0255
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2040
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (3651290214146378633176672095072962809221/625000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3651290214146378633176672095072962809221/625000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (29275506435546586614765686538737010260443/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (29275506435546586614765686538737010260443/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (58485828148717615680179063299320712734211/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (58485828148717615680179063299320712734211/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2040 BracketBatch0127.bracket2041 (58485828148717615680179063299320712734211/10000000000000000000000000000000000000000) (2066111555480479621940710578283010081913/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2040 BracketBatch0127.bracket2041
  (58485828148717615680179063299320712734211/10000000000000000000000000000000000000000) (2066111555480479621940710578283010081913/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2040
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2041
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0318.rows BesselBatch0318.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (58551012871093173229531373077474020520883/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (58551012871093173229531373077474020520883/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (14670495408045595404833801030834327249413/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (14670495408045595404833801030834327249413/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (23446598900655110969773315440162265903707/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (23446598900655110969773315440162265903707/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2041 BracketBatch0127.bracket2042 (23446598900655110969773315440162265903707/4000000000000000000000000000000000000000) (2068946530556799932220421076006615123067/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2041 BracketBatch0127.bracket2042
  (23446598900655110969773315440162265903707/4000000000000000000000000000000000000000) (2068946530556799932220421076006615123067/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2041
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2042
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (58681981632182381619335204123337308997649/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (58681981632182381619335204123337308997649/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (58813553841237999619598132058578209769319/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58813553841237999619598132058578209769319/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (14686941934177547654866667022739439845871/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (14686941934177547654866667022739439845871/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2042 BracketBatch0127.bracket2043 (14686941934177547654866667022739439845871/2500000000000000000000000000000000000000) (2071788744229569921391645963128923330297/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2042 BracketBatch0127.bracket2043
  (14686941934177547654866667022739439845871/2500000000000000000000000000000000000000) (2071788744229569921391645963128923330297/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2042
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2043
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (14703388460309499904899533014644552442329/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (14703388460309499904899533014644552442329/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (58945733667973023558517970817057791806859/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (58945733667973023558517970817057791806859/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (4710371500368440927124644115025440063047/800000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4710371500368440927124644115025440063047/800000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2043 BracketBatch0127.bracket2044 (4710371500368440927124644115025440063047/800000000000000000000000000000000000000) (2074638230448554916653448221648817521337/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2043 BracketBatch0127.bracket2044
  (4710371500368440927124644115025440063047/800000000000000000000000000000000000000) (2074638230448554916653448221648817521337/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2043
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2044
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (7368216708496627944814746352132223975857/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (7368216708496627944814746352132223975857/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (11815705064124974883134596172510009316381/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (11815705064124974883134596172510009316381/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (118024258988597897974190951679607838388761/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (118024258988597897974190951679607838388761/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2044 BracketBatch0127.bracket2045 (118024258988597897974190951679607838388761/20000000000000000000000000000000000000000) (415499004681171414301139566099722686747/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2044 BracketBatch0127.bracket2045
  (118024258988597897974190951679607838388761/20000000000000000000000000000000000000000) (415499004681171414301139566099722686747/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2044
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2045
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (29539262660312437207836490431275023290951/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29539262660312437207836490431275023290951/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (59211933046401250202011552063490064434977/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59211933046401250202011552063490064434977/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (118290458367026124617684532926040111016879/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (118290458367026124617684532926040111016879/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2045 BracketBatch0127.bracket2046 (118290458367026124617684532926040111016879/20000000000000000000000000000000000000000) (416071831507636904394267291381714954091/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2045 BracketBatch0127.bracket2046
  (118290458367026124617684532926040111016879/20000000000000000000000000000000000000000) (416071831507636904394267291381714954091/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2045
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2046
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (29605966523200625101005776031745032217487/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (29605966523200625101005776031745032217487/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (3709122570745761579836577437609338513989/625000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3709122570745761579836577437609338513989/625000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (59278947089166717739698395532619740329399/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (59278947089166717739698395532619740329399/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2046 BracketBatch0127.bracket2047 (59278947089166717739698395532619740329399/10000000000000000000000000000000000000000) (130201916720571675189724377742506510651/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2046 BracketBatch0127.bracket2047
  (59278947089166717739698395532619740329399/10000000000000000000000000000000000000000) (130201916720571675189724377742506510651/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2046
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2047
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0319.rows BesselBatch0319.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (59345961131932185277385239001749416223821/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (59345961131932185277385239001749416223821/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0320.rows BesselBatch0320.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (59480613903728417651209796756549803769753/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (59480613903728417651209796756549803769753/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0648.rows BesselBatch0648.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (59413287517830301464297517879149609996787/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (59413287517830301464297517879149609996787/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0255.rows ScalarLogs0255.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0127.bracket2047 BracketBatch0128.bracket2048 (59413287517830301464297517879149609996787/10000000000000000000000000000000000000000) (1043054794155788443888784801893220409859/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0127.bracket2047 BracketBatch0128.bracket2048
  (59413287517830301464297517879149609996787/10000000000000000000000000000000000000000) (1043054794155788443888784801893220409859/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2047
