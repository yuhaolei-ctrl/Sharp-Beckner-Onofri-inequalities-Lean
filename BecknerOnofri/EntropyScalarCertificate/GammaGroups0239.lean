module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0298
public import BecknerOnofri.EntropyScalarCertificate.Bessel0299
public import BecknerOnofri.EntropyScalarCertificate.Bessel0300
public import BecknerOnofri.EntropyScalarCertificate.Bessel0638
public import BecknerOnofri.EntropyScalarCertificate.Brackets0119
public import BecknerOnofri.EntropyScalarCertificate.Brackets0120
public import BecknerOnofri.EntropyScalarCertificate.Logs0239
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1912
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (15788976353608546187964023434914468923897/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15788976353608546187964023434914468923897/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (31758722582058218679376505897509088254749/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (31758722582058218679376505897509088254749/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (63336675289275311055304552767338026102543/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (63336675289275311055304552767338026102543/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1912 BracketBatch0119.bracket1913 (63336675289275311055304552767338026102543/20000000000000000000000000000000000000000) (260704521715534134335058443695842678529/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1912 BracketBatch0119.bracket1913
  (63336675289275311055304552767338026102543/20000000000000000000000000000000000000000) (260704521715534134335058443695842678529/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1912
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1913
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0298.rows BesselBatch0298.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (15879361291029109339688252948754544127373/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15879361291029109339688252948754544127373/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (15970864179760128608583976494057742108019/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (15970864179760128608583976494057742108019/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (124414943245270460735438396260985493107/39062500000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (124414943245270460735438396260985493107/39062500000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1913 BracketBatch0119.bracket1914 (124414943245270460735438396260985493107/39062500000000000000000000000000000000) (1310204021808454758489402802745766715967/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1913 BracketBatch0119.bracket1914
  (124414943245270460735438396260985493107/39062500000000000000000000000000000000) (1310204021808454758489402802745766715967/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1913
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1914
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (6388345671904051443433590597623096843207/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6388345671904051443433590597623096843207/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (16063505503776912122663060495378346418487/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (16063505503776912122663060495378346418487/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (64068739367074081462494073978872177053009/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64068739367074081462494073978872177053009/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1914 BracketBatch0119.bracket1915 (64068739367074081462494073978872177053009/20000000000000000000000000000000000000000) (164617013449324754981241743813431773329/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1914 BracketBatch0119.bracket1915
  (64068739367074081462494073978872177053009/20000000000000000000000000000000000000000) (164617013449324754981241743813431773329/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1914
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1915
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (32127011007553824245326120990756692836971/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32127011007553824245326120990756692836971/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (4039326562676361147253918057121092614977/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4039326562676361147253918057121092614977/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (64441623508964713423357465447725433756787/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64441623508964713423357465447725433756787/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1915 BracketBatch0119.bracket1916 (64441623508964713423357465447725433756787/20000000000000000000000000000000000000000) (1323719430021928678830884270810147740157/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1915 BracketBatch0119.bracket1916
  (64441623508964713423357465447725433756787/20000000000000000000000000000000000000000) (1323719430021928678830884270810147740157/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1915
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1916
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (32314612501410889178031344456968740919813/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32314612501410889178031344456968740919813/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (4063071981890952645653103049182340920623/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4063071981890952645653103049182340920623/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (64819188356538510343256168850427468284797/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (64819188356538510343256168850427468284797/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1916 BracketBatch0119.bracket1917 (64819188356538510343256168850427468284797/20000000000000000000000000000000000000000) (1330554562884807597885544893923454667811/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1916 BracketBatch0119.bracket1917
  (64819188356538510343256168850427468284797/20000000000000000000000000000000000000000) (1330554562884807597885544893923454667811/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1916
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1917
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (32504575855127621165224824393458727364981/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (32504575855127621165224824393458727364981/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (4087118144273845992197969518035569295331/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (4087118144273845992197969518035569295331/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (65201521009318389102808580537743281727629/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (65201521009318389102808580537743281727629/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1917 BracketBatch0119.bracket1918 (65201521009318389102808580537743281727629/20000000000000000000000000000000000000000) (1337442089931825787531279291323462281269/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1917 BracketBatch0119.bracket1918
  (65201521009318389102808580537743281727629/20000000000000000000000000000000000000000) (1337442089931825787531279291323462281269/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1917
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1918
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (6539389030838153587516751228856910872529/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (6539389030838153587516751228856910872529/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (32891765589439363887957646260834524128203/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (32891765589439363887957646260834524128203/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (2049647210738441619548168825159971202839/625000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2049647210738441619548168825159971202839/625000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1918 BracketBatch0119.bracket1919 (2049647210738441619548168825159971202839/625000000000000000000000000000000000000) (268876521023739345417870048712349569523/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1918 BracketBatch0119.bracket1919
  (2049647210738441619548168825159971202839/625000000000000000000000000000000000000) (268876521023739345417870048712349569523/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1918
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1919
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0299.rows BesselBatch0299.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (164458827947196819439788231304172620641/50000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (164458827947196819439788231304172620641/50000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0300.rows BesselBatch0300.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (6617816698451235388433983972393741816681/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (6617816698451235388433983972393741816681/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0638.rows BesselBatch0638.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (13196169816339108166025513224560646642321/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (13196169816339108166025513224560646642321/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0239.rows ScalarLogs0239.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0119.bracket1919 BracketBatch0120.bracket1920 (13196169816339108166025513224560646642321/4000000000000000000000000000000000000000) (27027534257371302404123714035357779533/200000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0119.bracket1919 BracketBatch0120.bracket1920
  (13196169816339108166025513224560646642321/4000000000000000000000000000000000000000) (27027534257371302404123714035357779533/200000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel1919
