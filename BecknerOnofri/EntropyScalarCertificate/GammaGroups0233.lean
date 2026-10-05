module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0291
public import BecknerOnofri.EntropyScalarCertificate.Bessel0292
public import BecknerOnofri.EntropyScalarCertificate.Bessel0634
public import BecknerOnofri.EntropyScalarCertificate.Bessel0635
public import BecknerOnofri.EntropyScalarCertificate.Brackets0116
public import BecknerOnofri.EntropyScalarCertificate.Brackets0117
public import BecknerOnofri.EntropyScalarCertificate.Logs0233
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1864
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (996707786475349854292004512281027028877/400000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (996707786475349854292004512281027028877/400000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (25025225237808717210794369648156607142059/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (25025225237808717210794369648156607142059/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (3121432493730778973005905153448892678999/1250000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3121432493730778973005905153448892678999/1250000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1864 BracketBatch0116.bracket1865 (3121432493730778973005905153448892678999/1250000000000000000000000000000000000000) (1033264007065705416777828330437883414271/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1864 BracketBatch0116.bracket1865
  (3121432493730778973005905153448892678999/1250000000000000000000000000000000000000) (1033264007065705416777828330437883414271/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1864
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1865
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (3128153154726089651349296206019575892757/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3128153154726089651349296206019575892757/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (767022566387938074602450945564440041/305175781250000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (767022566387938074602450945564440041/305175781250000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (6269877586651084004920935279051522300693/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6269877586651084004920935279051522300693/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1865 BracketBatch0116.bracket1866 (6269877586651084004920935279051522300693/2500000000000000000000000000000000000000) (519016659809963183166034212716475644397/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1865 BracketBatch0116.bracket1866
  (6269877586651084004920935279051522300693/2500000000000000000000000000000000000000) (519016659809963183166034212716475644397/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1865
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1866
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (5026759091079990965714622516851114252697/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5026759091079990965714622516851114252697/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (1009736808528597251708423616892733272817/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1009736808528597251708423616892733272817/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (5037721566861488612128370300657390308391/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (5037721566861488612128370300657390308391/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1866 BracketBatch0116.bracket1867 (5037721566861488612128370300657390308391/2000000000000000000000000000000000000000) (1042834205816726672445264853504766634747/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1866 BracketBatch0116.bracket1867
  (5037721566861488612128370300657390308391/2000000000000000000000000000000000000000) (1042834205816726672445264853504766634747/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1866
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1867
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (12621710106607465646355295211159165910211/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12621710106607465646355295211159165910211/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (12677057343917921303362342039853523653321/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12677057343917921303362342039853523653321/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (6324691862631346737429409312753172390883/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (6324691862631346737429409312753172390883/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1867 BracketBatch0116.bracket1868 (6324691862631346737429409312753172390883/2500000000000000000000000000000000000000) (1047666952811933451669842571465601106351/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1867 BracketBatch0116.bracket1868
  (6324691862631346737429409312753172390883/2500000000000000000000000000000000000000) (1047666952811933451669842571465601106351/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1867
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1868
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0291.rows BesselBatch0291.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (25354114687835842606724684079707047306639/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25354114687835842606724684079707047306639/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (12732947170235303032362455146058894846459/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12732947170235303032362455146058894846459/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (50820009028306448671449594371824836999557/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (50820009028306448671449594371824836999557/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1868 BracketBatch0116.bracket1869 (50820009028306448671449594371824836999557/20000000000000000000000000000000000000000) (526265925585182233321287011686243152439/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1868 BracketBatch0116.bracket1869
  (50820009028306448671449594371824836999557/20000000000000000000000000000000000000000) (526265925585182233321287011686243152439/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1868
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1869
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (5093178868094121212944982058423557938583/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (5093178868094121212944982058423557938583/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (25578774923747591441757157065594941192049/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (25578774923747591441757157065594941192049/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0634.rows BesselBatch0634.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (12761167316054549376620516839428182721241/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (12761167316054549376620516839428182721241/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1869 BracketBatch0116.bracket1870 (12761167316054549376620516839428182721241/5000000000000000000000000000000000000000) (1057429194929266282439165328939168449967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1869 BracketBatch0116.bracket1870
  (12761167316054549376620516839428182721241/5000000000000000000000000000000000000000) (1057429194929266282439165328939168449967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1869
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1870
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (12789387461873795720878578532797470596023/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (12789387461873795720878578532797470596023/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (642319312217768830121655989985674742597/250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (642319312217768830121655989985674742597/250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (25635773706229172323311698332510965447963/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (25635773706229172323311698332510965447963/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1870 BracketBatch0116.bracket1871 (25635773706229172323311698332510965447963/10000000000000000000000000000000000000000) (265589820415891630987737846390003844911/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1870 BracketBatch0116.bracket1871
  (25635773706229172323311698332510965447963/10000000000000000000000000000000000000000) (265589820415891630987737846390003844911/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1870
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1871
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (25692772488710753204866239599426989703877/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (25692772488710753204866239599426989703877/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0292.rows BesselBatch0292.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (12903951696011044118047200082773675193273/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (12903951696011044118047200082773675193273/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0635.rows BesselBatch0635.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (51500675880732841440960639764974340090423/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (51500675880732841440960639764974340090423/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0233.rows ScalarLogs0233.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0116.bracket1871 BracketBatch0117.bracket1872 (51500675880732841440960639764974340090423/20000000000000000000000000000000000000000) (1067322412552996512126734148712330367097/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0116.bracket1871 BracketBatch0117.bracket1872
  (51500675880732841440960639764974340090423/20000000000000000000000000000000000000000) (1067322412552996512126734148712330367097/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1871
