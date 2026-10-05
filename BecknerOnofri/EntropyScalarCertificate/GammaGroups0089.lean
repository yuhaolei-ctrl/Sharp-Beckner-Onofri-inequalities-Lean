import BecknerOnofri.EntropyScalarCertificate.Bessel0111
import BecknerOnofri.EntropyScalarCertificate.Bessel0112
import BecknerOnofri.EntropyScalarCertificate.Bessel0544
import BecknerOnofri.EntropyScalarCertificate.Bessel0545
import BecknerOnofri.EntropyScalarCertificate.Brackets0044
import BecknerOnofri.EntropyScalarCertificate.Brackets0045
import BecknerOnofri.EntropyScalarCertificate.Logs0089
import BecknerOnofri.ScalarElementaryComposition
import BecknerOnofri.ScalarGammaEnclosure
import BecknerOnofri.ScalarLogBesselEndpoints
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0712
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨16,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨20,by decide⟩
]
theorem leftAccepted : besselPointCheck (1014845728325154287319164111020317063557/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1014845728325154287319164111020317063557/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨31,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨32,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨33,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨35,by decide⟩
]
theorem rightAccepted : besselPointCheck (406363431331977371781976104917074531087/2000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (406363431331977371781976104917074531087/2000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨34,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨35,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨38,by decide⟩
]
theorem midAccepted : besselPointCheck (4061508613310195433548208746626006782549/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4061508613310195433548208746626006782549/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨0,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨1,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨2,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨3,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨4,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨5,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨6,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨7,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨8,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨9,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨10,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨11,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨12,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨13,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨14,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨15,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0712 BracketBatch0044.bracket0713 (4061508613310195433548208746626006782549/20000000000000000000000000000000000000000) (1238637330964901489806821880628508697/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0712 BracketBatch0044.bracket0713
  (4061508613310195433548208746626006782549/20000000000000000000000000000000000000000) (1238637330964901489806821880628508697/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0712
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0713
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨26,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨30,by decide⟩
]
theorem leftAccepted : besselPointCheck (253977144582485857363735065573171581929/1250000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (253977144582485857363735065573171581929/1250000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨43,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨45,by decide⟩
]
theorem rightAccepted : besselPointCheck (1016971562064803167256628707736159127109/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1016971562064803167256628707736159127109/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨41,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨42,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨43,by decide⟩
]
theorem midAccepted : besselPointCheck (81315205615789863868462758801153818193/400000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (81315205615789863868462758801153818193/400000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨16,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨17,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨18,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨19,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨20,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨21,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨22,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨23,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨24,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨25,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨26,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨27,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨28,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨29,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨30,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨31,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0713 BracketBatch0044.bracket0714 (81315205615789863868462758801153818193/400000000000000000000000000000000000000) (248733870017591458444124189134309579/2000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0713 BracketBatch0044.bracket0714
  (81315205615789863868462758801153818193/400000000000000000000000000000000000000) (248733870017591458444124189134309579/2000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0713
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0714
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨36,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨40,by decide⟩
]
theorem leftAccepted : besselPointCheck (406788624825921266902651483094463650843/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (406788624825921266902651483094463650843/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨53,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨55,by decide⟩
]
theorem rightAccepted : besselPointCheck (2036069359390386363467107410630861299169/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2036069359390386363467107410630861299169/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨44,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨45,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨48,by decide⟩
]
theorem midAccepted : besselPointCheck (508751560439999087247545603262897444173/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (508751560439999087247545603262897444173/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨32,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨33,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨34,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨35,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨36,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨37,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨38,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨39,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨40,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨41,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨42,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨43,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨44,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨45,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨46,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨47,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0714 BracketBatch0044.bracket0715 (508751560439999087247545603262897444173/2500000000000000000000000000000000000000) (1248716807130370827832616236954041431/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0714 BracketBatch0044.bracket0715
  (508751560439999087247545603262897444173/2500000000000000000000000000000000000000) (1248716807130370827832616236954041431/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0714
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0715
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨46,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨47,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨48,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨50,by decide⟩
]
theorem leftAccepted : besselPointCheck (1018034679695193181733553705315430649583/5000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (1018034679695193181733553705315430649583/5000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨63,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨1,by decide⟩
]
theorem rightAccepted : besselPointCheck (203819586277335461721877419180529739881/1000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (203819586277335461721877419180529739881/1000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨49,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨50,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨51,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨52,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨53,by decide⟩
]
theorem midAccepted : besselPointCheck (509283152770467622585735200304519837247/2500000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (509283152770467622585735200304519837247/2500000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨48,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨49,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨50,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨51,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨52,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨53,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨54,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨55,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨56,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨57,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨58,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨59,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨60,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨61,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨62,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨63,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0715 BracketBatch0044.bracket0716 (509283152770467622585735200304519837247/2500000000000000000000000000000000000000) (1253779734415428189424455819247394703/10000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0715 BracketBatch0044.bracket0716
  (509283152770467622585735200304519837247/2500000000000000000000000000000000000000) (1253779734415428189424455819247394703/10000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0715
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0716
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨58,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0111.rows BesselBatch0111.accepted ⟨60,by decide⟩
]
theorem leftAccepted : besselPointCheck (2038195862773354617218774191805297398807/10000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (2038195862773354617218774191805297398807/10000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨9,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨10,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨11,by decide⟩
]
theorem rightAccepted : besselPointCheck (2040322634609847399094320179529437193263/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2040322634609847399094320179529437193263/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨54,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨55,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨56,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨57,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨58,by decide⟩
]
theorem midAccepted : besselPointCheck (407851849738320201631309437133473459207/2000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (407851849738320201631309437133473459207/2000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨64,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨65,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨66,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨67,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨68,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨69,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨70,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨71,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨72,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨73,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨74,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨75,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨76,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨77,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨78,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨79,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0716 BracketBatch0044.bracket0717 (407851849738320201631309437133473459207/2000000000000000000000000000000000000000) (125885816430429708731345569310721999/1000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0716 BracketBatch0044.bracket0717
  (407851849738320201631309437133473459207/2000000000000000000000000000000000000000) (125885816430429708731345569310721999/1000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0716
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0717
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨4,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨6,by decide⟩
]
theorem leftAccepted : besselPointCheck (102016131730492369954716008976471859663/500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (102016131730492369954716008976471859663/500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨17,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨18,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨19,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨20,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨21,by decide⟩
]
theorem rightAccepted : besselPointCheck (1020693060650882605046254869989054448349/5000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (1020693060650882605046254869989054448349/5000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨59,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨60,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨61,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨62,by decide⟩,
  checkedBesselOfRows BesselBatch0544.rows BesselBatch0544.accepted ⟨63,by decide⟩
]
theorem midAccepted : besselPointCheck (2040854377955806304593414959753773044979/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2040854377955806304593414959753773044979/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨80,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨81,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨82,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨83,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨84,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨85,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨86,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨87,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨88,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨89,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨90,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨91,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨92,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨93,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨94,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨95,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0717 BracketBatch0044.bracket0718 (2040854377955806304593414959753773044979/10000000000000000000000000000000000000000) (632170973201845317244357662710420797/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0717 BracketBatch0044.bracket0718
  (2040854377955806304593414959753773044979/10000000000000000000000000000000000000000) (632170973201845317244357662710420797/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0717
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0718
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨12,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨13,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨14,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨15,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨16,by decide⟩
]
theorem leftAccepted : besselPointCheck (408277224260353042018501947995621779339/2000000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (408277224260353042018501947995621779339/2000000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨27,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨28,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨29,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨30,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨31,by decide⟩
]
theorem rightAccepted : besselPointCheck (2052024693143769880962136808170592832359/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2052024693143769880962136808170592832359/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨0,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨1,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨2,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨3,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨4,by decide⟩
]
theorem midAccepted : besselPointCheck (2046705407222767545527323274074350864527/10000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (2046705407222767545527323274074350864527/10000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨96,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨97,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨98,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨99,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨100,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨101,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨102,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨103,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨104,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨105,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨106,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨107,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨108,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨109,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨110,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨111,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0718 BracketBatch0044.bracket0719 (2046705407222767545527323274074350864527/10000000000000000000000000000000000000000) (627548248812688823033074787272055909/5000000000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0718 BracketBatch0044.bracket0719
  (2046705407222767545527323274074350864527/10000000000000000000000000000000000000000) (627548248812688823033074787272055909/5000000000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0718
namespace BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0719
open EntropyLogCertificate CircleScalar
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def leftBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨22,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨23,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨24,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨25,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨26,by decide⟩
]
theorem leftAccepted : besselPointCheck (513006173285942470240534202042648208089/2500000000000000000000000000000000000000) leftBessels=true := by decide +kernel
def leftPoint := besselPointOfChecked (513006173285942470240534202042648208089/2500000000000000000000000000000000000000) leftBessels leftAccepted
def rightBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨37,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨38,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨39,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨40,by decide⟩,
  checkedBesselOfRows BesselBatch0112.rows BesselBatch0112.accepted ⟨41,by decide⟩
]
theorem rightAccepted : besselPointCheck (2062670030304283690276374011019472017463/10000000000000000000000000000000000000000) rightBessels=true := by decide +kernel
def rightPoint := besselPointOfChecked (2062670030304283690276374011019472017463/10000000000000000000000000000000000000000) rightBessels rightAccepted
def midBessels : Fin 5 → CheckedBessel := ![
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨5,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨6,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨7,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨8,by decide⟩,
  checkedBesselOfRows BesselBatch0545.rows BesselBatch0545.accepted ⟨9,by decide⟩
]
theorem midAccepted : besselPointCheck (4114694723448053571238510819190064849819/20000000000000000000000000000000000000000) midBessels=true := by decide +kernel
def midPoint := besselPointOfChecked (4114694723448053571238510819190064849819/20000000000000000000000000000000000000000) midBessels midAccepted
def whole_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨112,by decide⟩
def whole_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨113,by decide⟩
def whole_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨114,by decide⟩
def whole_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨115,by decide⟩
def whole_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨116,by decide⟩
def whole_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨117,by decide⟩
def whole_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨118,by decide⟩
def whole_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨119,by decide⟩
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
def point_wl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨120,by decide⟩
def point_wu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨121,by decide⟩
def point_pl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨122,by decide⟩
def point_pu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨123,by decide⟩
def point_ml := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨124,by decide⟩
def point_mu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨125,by decide⟩
def point_zl := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨126,by decide⟩
def point_zu := checkedLogOfRows ScalarLogs0089.rows ScalarLogs0089.accepted ⟨127,by decide⟩
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
theorem panelAccepted : gammaPanelCheck BracketBatch0044.bracket0719 BracketBatch0045.bracket0720 (4114694723448053571238510819190064849819/20000000000000000000000000000000000000000) (40025485353821829656639232103560961/312500000000000000000000000000000000000) wholeGamma pointGamma=true := by decide +kernel
noncomputable def certificate : CertifiedGammaCell := gammaCellOfEnclosures BracketBatch0044.bracket0719 BracketBatch0045.bracket0720
  (4114694723448053571238510819190064849819/20000000000000000000000000000000000000000) (40025485353821829656639232103560961/312500000000000000000000000000000000000) wholeGamma pointGamma panelAccepted
#print axioms certificate
end BecknerOnofri.HighDim.ScalarCertificate.GammaPanel0719
