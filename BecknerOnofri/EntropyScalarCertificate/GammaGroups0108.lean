module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0135
public import BecknerOnofri.EntropyScalarCertificate.Bessel0136
public import BecknerOnofri.EntropyScalarCertificate.Bessel0556
public import BecknerOnofri.EntropyScalarCertificate.Bessel0557
public import BecknerOnofri.EntropyScalarCertificate.Brackets0054
public import BecknerOnofri.EntropyScalarCertificate.Logs0108
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0864
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨4,by decide⟩
]
theorem leftAccepted : besselPointCheck (369044254200928612010052997063896216491/1000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (369044254200928612010052997063896216491/1000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨19,by decide⟩
]
theorem rightAccepted : besselPointCheck (3702600492105024590226113341119920758191/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3702600492105024590226113341119920758191/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨30,by decide⟩
]
theorem midAccepted : besselPointCheck (7393043034114310710326643311758882923101/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7393043034114310710326643311758882923101/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0864 BracketBatch0054.bracket0865 (7393043034114310710326643311758882923101/20000000000000000000000000000000000000000) (11724192680383734074336259356334114637/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0864 BracketBatch0054.bracket0865
  (7393043034114310710326643311758882923101/20000000000000000000000000000000000000000) (11724192680383734074336259356334114637/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0864
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0865
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨14,by decide⟩
]
theorem leftAccepted : besselPointCheck (925650123026256147556528335279980189547/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (925650123026256147556528335279980189547/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨29,by decide⟩
]
theorem rightAccepted : besselPointCheck (148590935344629329668384352951833979213/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (148590935344629329668384352951833979213/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨35,by decide⟩
]
theorem midAccepted : besselPointCheck (7417373875720757831935722164915770238513/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7417373875720757831935722164915770238513/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0865 BracketBatch0054.bracket0866 (7417373875720757831935722164915770238513/20000000000000000000000000000000000000000) (11864160961029953536458768900578943113/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0865 BracketBatch0054.bracket0866
  (7417373875720757831935722164915770238513/20000000000000000000000000000000000000000) (11864160961029953536458768900578943113/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0865
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0866
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨24,by decide⟩
]
theorem leftAccepted : besselPointCheck (1857386691807866620854804411897924740161/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1857386691807866620854804411897924740161/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨39,by decide⟩
]
theorem rightAccepted : besselPointCheck (1863480646737534706694614546405170092531/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1863480646737534706694614546405170092531/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨40,by decide⟩
]
theorem midAccepted : besselPointCheck (930216834636350331887354739575773708173/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (930216834636350331887354739575773708173/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0866 BracketBatch0054.bracket0867 (930216834636350331887354739575773708173/2500000000000000000000000000000000000000) (750338341318016816424531834730988203/625000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0866 BracketBatch0054.bracket0867
  (930216834636350331887354739575773708173/2500000000000000000000000000000000000000) (750338341318016816424531834730988203/625000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0866
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0867
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨34,by decide⟩
]
theorem leftAccepted : besselPointCheck (3726961293475069413389229092810340185059/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3726961293475069413389229092810340185059/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨49,by decide⟩
]
theorem rightAccepted : besselPointCheck (3739164299019387490898321846139744897511/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3739164299019387490898321846139744897511/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨45,by decide⟩
]
theorem midAccepted : besselPointCheck (746612559249445690428755093895008508257/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (746612559249445690428755093895008508257/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0867 BracketBatch0054.bracket0868 (746612559249445690428755093895008508257/2000000000000000000000000000000000000000) (3036989673379216022440440295215882589/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0867 BracketBatch0054.bracket0868
  (746612559249445690428755093895008508257/2000000000000000000000000000000000000000) (3036989673379216022440440295215882589/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0867
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0868
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨44,by decide⟩
]
theorem leftAccepted : besselPointCheck (934791074754846872724580461534936224377/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (934791074754846872724580461534936224377/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨59,by decide⟩
]
theorem rightAccepted : besselPointCheck (3751382477990944611346760087569528486753/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (3751382477990944611346760087569528486753/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨50,by decide⟩
]
theorem midAccepted : besselPointCheck (7490546777010332102245081933709273384261/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7490546777010332102245081933709273384261/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0868 BracketBatch0054.bracket0869 (7490546777010332102245081933709273384261/20000000000000000000000000000000000000000) (12291805210851518998574253294179158609/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0868 BracketBatch0054.bracket0869
  (7490546777010332102245081933709273384261/20000000000000000000000000000000000000000) (12291805210851518998574253294179158609/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0868
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0869
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨54,by decide⟩
]
theorem leftAccepted : besselPointCheck (15005529911963778445387040350278113947/40000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (15005529911963778445387040350278113947/40000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨5,by decide⟩
]
theorem rightAccepted : besselPointCheck (1881807954270567861171676623437875851983/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1881807954270567861171676623437875851983/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨55,by decide⟩
]
theorem midAccepted : besselPointCheck (1878749596633020083422528333611320047679/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1878749596633020083422528333611320047679/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0869 BracketBatch0054.bracket0870 (1878749596633020083422528333611320047679/5000000000000000000000000000000000000000) (12436961605385386101134557914715466141/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0869 BracketBatch0054.bracket0870
  (1878749596633020083422528333611320047679/5000000000000000000000000000000000000000) (12436961605385386101134557914715466141/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0869
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0870
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0135.rows BesselBatch0135.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨0,by decide⟩
]
theorem leftAccepted : besselPointCheck (3763615908541135722343353246875751703963/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3763615908541135722343353246875751703963/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨15,by decide⟩
]
theorem rightAccepted : besselPointCheck (5899788545677747380536710500553416413/15625000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (5899788545677747380536710500553416413/15625000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨60,by decide⟩
]
theorem midAccepted : besselPointCheck (7539480577774894045886847967229938208283/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7539480577774894045886847967229938208283/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0870 BracketBatch0054.bracket0871 (7539480577774894045886847967229938208283/20000000000000000000000000000000000000000) (3145859127337560303950296103615860823/2500000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0870 BracketBatch0054.bracket0871
  (7539480577774894045886847967229938208283/20000000000000000000000000000000000000000) (3145859127337560303950296103615860823/2500000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0870
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0871
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨10,by decide⟩
]
theorem leftAccepted : besselPointCheck (3775864669233758323543494720354186504317/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (3775864669233758323543494720354186504317/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0136.rows BesselBatch0136.accepted ⟨25,by decide⟩
]
theorem rightAccepted : besselPointCheck (1894064419524153611542192374709242875801/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1894064419524153611542192374709242875801/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0556.rows BesselBatch0556.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0557.rows BesselBatch0557.accepted ⟨1,by decide⟩
]
theorem midAccepted : besselPointCheck (7563993508282065546627879469772672255919/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (7563993508282065546627879469772672255919/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0108.rows ScalarLogs0108.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0054.bracket0871 BracketBatch0054.bracket0872 (7563993508282065546627879469772672255919/20000000000000000000000000000000000000000) (12731238595099226690735142936017161681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0054.bracket0871 BracketBatch0054.bracket0872
  (7563993508282065546627879469772672255919/20000000000000000000000000000000000000000) (12731238595099226690735142936017161681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0871
