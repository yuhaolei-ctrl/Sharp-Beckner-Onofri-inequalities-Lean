module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0338
public import BecknerOnofri.EntropyScalarCertificate.Bessel0339
public import BecknerOnofri.EntropyScalarCertificate.Bessel0340
public import BecknerOnofri.EntropyScalarCertificate.Bessel0658
public import BecknerOnofri.EntropyScalarCertificate.Brackets0135
public import BecknerOnofri.EntropyScalarCertificate.Brackets0136
public import BecknerOnofri.EntropyScalarCertificate.Logs0271
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2168
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (10244800770011861184448266303096347013909/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10244800770011861184448266303096347013909/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (41109585445227970712542844021973823016927/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41109585445227970712542844021973823016927/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (82088788525275415450335909234359211072563/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (82088788525275415450335909234359211072563/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2168 BracketBatch0135.bracket2169 (82088788525275415450335909234359211072563/10000000000000000000000000000000000000000) (250243563562724282925559703906581741519/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2168 BracketBatch0135.bracket2169
  (82088788525275415450335909234359211072563/10000000000000000000000000000000000000000) (250243563562724282925559703906581741519/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2168
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2169
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0338.rows BesselBatch0338.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (82219170890455941425085688043947646033851/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (82219170890455941425085688043947646033851/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (82481630485767259300383741649181065479857/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (82481630485767259300383741649181065479857/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (41175200344055800181367357423282177878427/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41175200344055800181367357423282177878427/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2169 BracketBatch0135.bracket2170 (41175200344055800181367357423282177878427/5000000000000000000000000000000000000000) (3916538048486317646604655902245978773/15625000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2169 BracketBatch0135.bracket2170
  (41175200344055800181367357423282177878427/5000000000000000000000000000000000000000) (3916538048486317646604655902245978773/15625000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2169
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2170
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (41240815242883629650191870824590532739927/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (41240815242883629650191870824590532739927/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (82745801506633129487780604848448878603273/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (82745801506633129487780604848448878603273/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (165227431992400388788164346497629944083127/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (165227431992400388788164346497629944083127/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2170 BracketBatch0135.bracket2171 (165227431992400388788164346497629944083127/20000000000000000000000000000000000000000) (2510747750283747228565749867052928175139/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2170 BracketBatch0135.bracket2171
  (165227431992400388788164346497629944083127/20000000000000000000000000000000000000000) (2510747750283747228565749867052928175139/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2170
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2171
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (8274580150663312948778060484844887860327/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (8274580150663312948778060484844887860327/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (41505850365069966357118658874288167913633/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41505850365069966357118658874288167913633/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (20719687779596632775252240324628151803817/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (20719687779596632775252240324628151803817/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2171 BracketBatch0135.bracket2172 (20719687779596632775252240324628151803817/2500000000000000000000000000000000000000) (314365741375649119506637724623404809081/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2171 BracketBatch0135.bracket2172
  (20719687779596632775252240324628151803817/2500000000000000000000000000000000000000) (314365741375649119506637724623404809081/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2171
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2172
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (83011700730139932714237317748576335827263/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (83011700730139932714237317748576335827263/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (41639672576702507539947201116778141210209/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (41639672576702507539947201116778141210209/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (166291045883544947794131719982132618247681/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (166291045883544947794131719982132618247681/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2172 BracketBatch0135.bracket2173 (166291045883544947794131719982132618247681/20000000000000000000000000000000000000000) (62977974794377439383739087965880348469/250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2172 BracketBatch0135.bracket2173
  (166291045883544947794131719982132618247681/20000000000000000000000000000000000000000) (62977974794377439383739087965880348469/250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2172
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2173
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (16655869030681003015978880446711256484083/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (16655869030681003015978880446711256484083/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (20887187999298900680323511363784615389643/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (20887187999298900680323511363784615389643/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (166828097150600617801188447688694743978987/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (166828097150600617801188447688694743978987/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2173 BracketBatch0135.bracket2174 (166828097150600617801188447688694743978987/20000000000000000000000000000000000000000) (252332703214432745714971111246857938333/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2173 BracketBatch0135.bracket2174
  (166828097150600617801188447688694743978987/20000000000000000000000000000000000000000) (252332703214432745714971111246857938333/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2173
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2174
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (83548751997195602721294045455138461558569/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (83548751997195602721294045455138461558569/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (83819938709619378273418854187373117560297/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (83819938709619378273418854187373117560297/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (83684345353407490497356449821255789559433/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (83684345353407490497356449821255789559433/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2174 BracketBatch0135.bracket2175 (83684345353407490497356449821255789559433/10000000000000000000000000000000000000000) (631887538161890302126074227020194933343/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2174 BracketBatch0135.bracket2175
  (83684345353407490497356449821255789559433/10000000000000000000000000000000000000000) (631887538161890302126074227020194933343/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2174
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2175
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0339.rows BesselBatch0339.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (41909969354809689136709427093686558780147/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (41909969354809689136709427093686558780147/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0340.rows BesselBatch0340.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (8409292296988838016406425126431023895803/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (8409292296988838016406425126431023895803/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0658.rows BesselBatch0658.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (41978215419876939609370776362920839129581/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (41978215419876939609370776362920839129581/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0271.rows ScalarLogs0271.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0135.bracket2175 BracketBatch0136.bracket2176 (41978215419876939609370776362920839129581/5000000000000000000000000000000000000000) (1265894227407974328519273055233117901771/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0135.bracket2175 BracketBatch0136.bracket2176
  (41978215419876939609370776362920839129581/5000000000000000000000000000000000000000) (1265894227407974328519273055233117901771/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel2175
