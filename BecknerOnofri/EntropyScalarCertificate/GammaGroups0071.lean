module

public import BecknerOnofri.EntropyScalarCertificate.Bessel0088
public import BecknerOnofri.EntropyScalarCertificate.Bessel0089
public import BecknerOnofri.EntropyScalarCertificate.Bessel0090
public import BecknerOnofri.EntropyScalarCertificate.Bessel0533
public import BecknerOnofri.EntropyScalarCertificate.Brackets0035
public import BecknerOnofri.EntropyScalarCertificate.Brackets0036
public import BecknerOnofri.EntropyScalarCertificate.Logs0071
public import BecknerOnofri.ScalarElementaryComposition
public import BecknerOnofri.ScalarGammaEnclosure
public import BecknerOnofri.ScalarLogBesselEndpoints

@[expose] public section
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0568
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (863109261176022791354621224729875068223/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (863109261176022791354621224729875068223/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (432077265716674061361831345138892813317/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (432077265716674061361831345138892813317/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨22,by decide⟩
]
theorem midAccepted : besselPointCheck (1727263792609370914078283915007660694857/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1727263792609370914078283915007660694857/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0568 BracketBatch0035.bracket0569 (1727263792609370914078283915007660694857/10000000000000000000000000000000000000000) (329736724581191165501497897082764569/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0568 BracketBatch0035.bracket0569
  (1727263792609370914078283915007660694857/10000000000000000000000000000000000000000) (329736724581191165501497897082764569/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0568
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0569
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0088.rows BesselBatch0088.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (345661812573339249089465076111114250653/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (345661812573339249089465076111114250653/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (173039982520723990134389104211040384453/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (173039982520723990134389104211040384453/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨27,by decide⟩
]
theorem midAccepted : besselPointCheck (691741777614787229358243284533195019559/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (691741777614787229358243284533195019559/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0569 BracketBatch0035.bracket0570 (691741777614787229358243284533195019559/4000000000000000000000000000000000000000) (82825116915393815336578769428018443/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0569 BracketBatch0035.bracket0570
  (691741777614787229358243284533195019559/4000000000000000000000000000000000000000) (82825116915393815336578769428018443/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0569
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0570
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (1730399825207239901343891042110403844527/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1730399825207239901343891042110403844527/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (433122702419442978613584743301993598283/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (433122702419442978613584743301993598283/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨32,by decide⟩
]
theorem midAccepted : besselPointCheck (3462890634885011815798230015318378237659/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3462890634885011815798230015318378237659/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0570 BracketBatch0035.bracket0571 (3462890634885011815798230015318378237659/20000000000000000000000000000000000000000) (133147918347602309262856541395149037/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0570 BracketBatch0035.bracket0571
  (3462890634885011815798230015318378237659/20000000000000000000000000000000000000000) (133147918347602309262856541395149037/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0570
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0571
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (1732490809677771914454338973207974393129/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1732490809677771914454338973207974393129/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (867291008291276709553217988435209028819/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (867291008291276709553217988435209028819/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨37,by decide⟩
]
theorem midAccepted : besselPointCheck (3467072826260325333560774950078392450767/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3467072826260325333560774950078392450767/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0571 BracketBatch0035.bracket0572 (3467072826260325333560774950078392450767/20000000000000000000000000000000000000000) (668889445448885760616702692905717207/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0571 BracketBatch0035.bracket0572
  (3467072826260325333560774950078392450767/20000000000000000000000000000000000000000) (668889445448885760616702692905717207/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0571
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0572
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (346916403316510683821287195374083611527/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (346916403316510683821287195374083611527/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (868336723113005795517887764389069845197/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (868336723113005795517887764389069845197/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨42,by decide⟩
]
theorem midAccepted : besselPointCheck (3471255462808565010142211505648557748029/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (3471255462808565010142211505648557748029/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0572 BracketBatch0035.bracket0573 (3471255462808565010142211505648557748029/20000000000000000000000000000000000000000) (672050523533263612403292291625171009/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0572 BracketBatch0035.bracket0573
  (3471255462808565010142211505648557748029/20000000000000000000000000000000000000000) (672050523533263612403292291625171009/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0572
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0573
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1736673446226011591035775528778139690391/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1736673446226011591035775528778139690391/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (1738765098912739918829865553833243592163/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1738765098912739918829865553833243592163/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨47,by decide⟩
]
theorem midAccepted : besselPointCheck (1737719272569375754932820541305691641277/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1737719272569375754932820541305691641277/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0573 BracketBatch0035.bracket0574 (1737719272569375754932820541305691641277/10000000000000000000000000000000000000000) (337611426552110003334653838037572869/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0573 BracketBatch0035.bracket0574
  (1737719272569375754932820541305691641277/10000000000000000000000000000000000000000) (337611426552110003334653838037572869/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0573
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0574
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (10867281868204624492686659711457772451/62500000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (10867281868204624492686659711457772451/62500000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (870428487473749237840728250082255516401/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (870428487473749237840728250082255516401/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨52,by decide⟩
]
theorem midAccepted : besselPointCheck (1739811036930119197255661026998877312481/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1739811036930119197255661026998877312481/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0574 BracketBatch0035.bracket0575 (1739811036930119197255661026998877312481/10000000000000000000000000000000000000000) (678406461310428699129522303236560537/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0574 BracketBatch0035.bracket0575
  (1739811036930119197255661026998877312481/10000000000000000000000000000000000000000) (678406461310428699129522303236560537/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0574
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0575
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0089.rows BesselBatch0089.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (1740856974947498475681456500164511032799/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1740856974947498475681456500164511032799/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0090.rows BesselBatch0090.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (348589814927042838290344543236059101423/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (348589814927042838290344543236059101423/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0533.rows BesselBatch0533.accepted ⟨57,by decide⟩
]
theorem midAccepted : besselPointCheck (1741903024791356333566589608172403269957/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1741903024791356333566589608172403269957/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0071.rows ScalarLogs0071.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0035.bracket0575 BracketBatch0036.bracket0576 (1741903024791356333566589608172403269957/10000000000000000000000000000000000000000) (681601375336176711158694725640562249/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0035.bracket0575 BracketBatch0036.bracket0576
  (1741903024791356333566589608172403269957/10000000000000000000000000000000000000000) (681601375336176711158694725640562249/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0575
