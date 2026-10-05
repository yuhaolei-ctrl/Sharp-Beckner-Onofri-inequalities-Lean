import BecknerOnofri.EntropyScalarCertificate.Bessel0113
import BecknerOnofri.EntropyScalarCertificate.Bessel0114
import BecknerOnofri.EntropyScalarCertificate.Bessel0115
import BecknerOnofri.EntropyScalarCertificate.Bessel0545
import BecknerOnofri.EntropyScalarCertificate.Bessel0546
import BecknerOnofri.EntropyScalarCertificate.Brackets0045
import BecknerOnofri.EntropyScalarCertificate.Brackets0046
import BecknerOnofri.EntropyScalarCertificate.Logs0091
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0728
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨52,by decide⟩
]
theorem leftAccepted : besselPointCheck (1074040653631783507189759702860327972403/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1074040653631783507189759702860327972403/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨3,by decide⟩
]
theorem rightAccepted : besselPointCheck (215878942347248910018971629646490983703/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (215878942347248910018971629646490983703/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨54,by decide⟩
]
theorem midAccepted : besselPointCheck (1076717682684014028642308925546391445459/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1076717682684014028642308925546391445459/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0728 BracketBatch0045.bracket0729 (1076717682684014028642308925546391445459/5000000000000000000000000000000000000000) (1530486930264099209963205146696836027/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0728 BracketBatch0045.bracket0729
  (1076717682684014028642308925546391445459/5000000000000000000000000000000000000000) (1530486930264099209963205146696836027/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0728
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0729
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0113.rows BesselBatch0113.accepted ⟨62,by decide⟩
]
theorem leftAccepted : besselPointCheck (2158789423472489100189716296464909837027/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2158789423472489100189716296464909837027/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨13,by decide⟩
]
theorem rightAccepted : besselPointCheck (1084752363888062988382485676926835248059/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1084752363888062988382485676926835248059/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨59,by decide⟩
]
theorem midAccepted : besselPointCheck (865658830249723015390937530063716066629/4000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (865658830249723015390937530063716066629/4000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0729 BracketBatch0045.bracket0730 (865658830249723015390937530063716066629/4000000000000000000000000000000000000000) (1560327222893831386660506307438537043/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0729 BracketBatch0045.bracket0730
  (865658830249723015390937530063716066629/4000000000000000000000000000000000000000) (1560327222893831386660506307438537043/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0729
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0730
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨8,by decide⟩
]
theorem leftAccepted : besselPointCheck (433900945555225195352994270770734099223/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (433900945555225195352994270770734099223/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨23,by decide⟩
]
theorem rightAccepted : besselPointCheck (545056815804458583122224682851116778323/2500000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (545056815804458583122224682851116778323/2500000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨0,by decide⟩
]
theorem midAccepted : besselPointCheck (4349731990993960309253870085258137609407/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4349731990993960309253870085258137609407/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0730 BracketBatch0045.bracket0731 (4349731990993960309253870085258137609407/20000000000000000000000000000000000000000) (198825368048546994881580603804036563/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0730 BracketBatch0045.bracket0731
  (4349731990993960309253870085258137609407/20000000000000000000000000000000000000000) (198825368048546994881580603804036563/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0730
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0731
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨18,by decide⟩
]
theorem leftAccepted : besselPointCheck (2180227263217834332488898731404467113289/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2180227263217834332488898731404467113289/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨33,by decide⟩
]
theorem rightAccepted : besselPointCheck (1095478536492245492551802553666619027037/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1095478536492245492551802553666619027037/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨5,by decide⟩
]
theorem midAccepted : besselPointCheck (4371184336202325317592503838737705167363/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4371184336202325317592503838737705167363/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0731 BracketBatch0045.bracket0732 (4371184336202325317592503838737705167363/20000000000000000000000000000000000000000) (202664803559775170025653032757311657/1250000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0731 BracketBatch0045.bracket0732
  (4371184336202325317592503838737705167363/20000000000000000000000000000000000000000) (202664803559775170025653032757311657/1250000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0731
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0732
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨28,by decide⟩
]
theorem leftAccepted : besselPointCheck (2190957072984490985103605107333238054071/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2190957072984490985103605107333238054071/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨43,by decide⟩
]
theorem rightAccepted : besselPointCheck (88067768016303591482142674919467310813/400000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (88067768016303591482142674919467310813/400000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨10,by decide⟩
]
theorem midAccepted : besselPointCheck (1098162818348020193039292995079980206099/5000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (1098162818348020193039292995079980206099/5000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0732 BracketBatch0045.bracket0733 (1098162818348020193039292995079980206099/5000000000000000000000000000000000000000) (1652478033295450180658521630970941691/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0732 BracketBatch0045.bracket0733
  (1098162818348020193039292995079980206099/5000000000000000000000000000000000000000) (1652478033295450180658521630970941691/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0732
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0733
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨38,by decide⟩
]
theorem leftAccepted : besselPointCheck (1100847100203794893526783436493341385161/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1100847100203794893526783436493341385161/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨53,by decide⟩
]
theorem rightAccepted : besselPointCheck (276554836120543227611936726588035020019/1250000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (276554836120543227611936726588035020019/1250000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨11,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨15,by decide⟩
]
theorem midAccepted : besselPointCheck (2207066444685967803974530342845481465237/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2207066444685967803974530342845481465237/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0733 BracketBatch0045.bracket0734 (2207066444685967803974530342845481465237/10000000000000000000000000000000000000000) (1684086141435165872115294243833246681/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0733 BracketBatch0045.bracket0734
  (2207066444685967803974530342845481465237/10000000000000000000000000000000000000000) (1684086141435165872115294243833246681/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0733
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0734
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨48,by decide⟩
]
theorem leftAccepted : besselPointCheck (2212438688964345820895493812704280160149/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2212438688964345820895493812704280160149/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨63,by decide⟩
]
theorem rightAccepted : besselPointCheck (1111595291139403477985081957437753719761/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1111595291139403477985081957437753719761/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨20,by decide⟩
]
theorem midAccepted : besselPointCheck (4435629271243152776865657727579787599671/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4435629271243152776865657727579787599671/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0734 BracketBatch0045.bracket0735 (4435629271243152776865657727579787599671/20000000000000000000000000000000000000000) (858073580008480061222978838292677623/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0734 BracketBatch0045.bracket0735
  (4435629271243152776865657727579787599671/20000000000000000000000000000000000000000) (858073580008480061222978838292677623/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0734
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0735
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0114.rows BesselBatch0114.accepted ⟨58,by decide⟩
]
theorem leftAccepted : besselPointCheck (2223190582278806955970163914875507439519/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2223190582278806955970163914875507439519/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0115.rows BesselBatch0115.accepted ⟨9,by decide⟩
]
theorem rightAccepted : besselPointCheck (1116974962061486419118269671374081635619/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1116974962061486419118269671374081635619/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨21,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0546.rows BesselBatch0546.accepted ⟨25,by decide⟩
]
theorem midAccepted : besselPointCheck (4457140506401779794206703257623670710757/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4457140506401779794206703257623670710757/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0091.rows ScalarLogs0091.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0045.bracket0735 BracketBatch0046.bracket0736 (4457140506401779794206703257623670710757/20000000000000000000000000000000000000000) (1748665520747123557284755929934050599/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0045.bracket0735 BracketBatch0046.bracket0736
  (4457140506401779794206703257623670710757/20000000000000000000000000000000000000000) (1748665520747123557284755929934050599/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0735
