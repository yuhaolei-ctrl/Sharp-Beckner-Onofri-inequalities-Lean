module

public import BecknerOnofri.V2.Onset.SobolevAlgebra
public import BecknerOnofri.GeneralSobolevEmbedding
public import BecknerOnofri.SubspectralResolvent
public import BecknerOnofri.ContinuousComplementInverse

@[expose] public section

/-! # The Sobolev Banach algebra `H^s(𝕋^d)`, `s > d/2`, as a complete normed `ℝ`-algebra

Stage A of the Sobolev re-audit (manuscript Section 4, proof of
`lem:section4-local-uniqueness`; Section 5, the Lyapunov--Schmidt setup before
`lem:section5-quartic-reduction`): "the Sobolev space `H^s(𝕋^d)` is a Banach algebra".

**Banach-space model.**  `Hs d s` is the subalgebra `{u ∈ C(𝕋^d, ℝ) : u ∈ H^s}` of the algebra
of real continuous functions (every `H^s` function, `s > d/2`, has a unique continuous
representative), so its ring/algebra structure is inherited and no associativity of convolution
has to be reproved.  It is given the norm
`‖u‖ := C_{d,s} * ‖u‖_{H^s}` where `C_{d,s} = sobolevAlgConst d s` is the Banach-algebra constant
of `Onset/SobolevAlgebra.lean` (`sobolev_mul_space`).  This is an equivalent norm on `H^s`
(a constant multiple of the Fourier-weighted `ℓ²` norm) for which the algebra is a genuine
`NormedRing` (`‖uv‖ ≤ ‖u‖ ‖v‖`), so that Mathlib's `NormedSpace.exp` on a complete normed algebra
(analytic everywhere) applies.  The Banach space structure is obtained from the isometric
embedding `u ↦ C (w_k û(k))_k` into the Hilbert space `ℓ²(ℤ^d, ℂ)` (`NormedAddCommGroup.induced`),
and completeness is proved from the completeness of `C(𝕋^d, ℝ)` (sup-norm control of `H^s`) and
of `ℓ²`.

The norm is a constant multiple of the manuscript's `H^s` norm: `norm_eq`. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal Topology

namespace BecknerOnofri.V2.Reaudit.Sobolev
open BecknerOnofri.HighDim ContinuousGibbs ContinuousFirstShell

/-- The Sobolev index hypotheses `0 < d`, `s > d/2` (Banach-algebra regime). -/
class SobolevIndex (d : ℕ) (s : ℝ) : Prop where
  pos : 0 < d
  gt : (d : ℝ) / 2 < s

theorem SobolevIndex.hd (d : ℕ) (s : ℝ) [h : SobolevIndex d s] : 0 < d := h.pos

theorem SobolevIndex.hs (d : ℕ) (s : ℝ) [h : SobolevIndex d s] : (d : ℝ) / 2 < s := h.gt

theorem SobolevIndex.nonneg (d : ℕ) (s : ℝ) [h : SobolevIndex d s] : 0 ≤ s := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith [h.gt]

instance : SobolevIndex 11 11 := ⟨by norm_num, by norm_num⟩

/-! ## Weighted coefficients of a continuous function -/

/-- The Fourier-weighted coefficients `w_k û(k)`, `w_k = (1 + (2π|k|)²)^{s/2}`. -/
def scaledCoeff {d : ℕ} (s : ℝ) (u : Space d) : Frequency d → ℂ :=
  fun k => (sobolevScale s k : ℂ) * coefficient k u

theorem scaledCoeff_eq {d : ℕ} (s : ℝ) (u : Space d) : scaledCoeff s u = scaledFourier s ⇑u := by
  funext k
  simp [scaledCoeff, scaledFourier, coefficient_eq_fourierCoeff]

theorem scaledCoeff_add {d : ℕ} (s : ℝ) (u v : Space d) :
    scaledCoeff s (u + v) = scaledCoeff s u + scaledCoeff s v := by
  funext k
  simp [scaledCoeff, mul_add]

theorem scaledCoeff_smul {d : ℕ} (s : ℝ) (c : ℝ) (u : Space d) :
    scaledCoeff s (c • u) = c • scaledCoeff s u := by
  funext k
  simp only [scaledCoeff, map_smul, Pi.smul_apply, Complex.real_smul]
  ring

@[simp] theorem scaledCoeff_zero {d : ℕ} (s : ℝ) : scaledCoeff s (0 : Space d) = 0 := by
  funext k; simp [scaledCoeff]

theorem inSobolev_iff_memℓp {d : ℕ} (s : ℝ) (u : Space d) :
    InSobolev s ⇑u ↔ Memℓp (scaledCoeff s u) 2 := by
  rw [scaledCoeff_eq, memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, scaledFourier_norm_sq]
  exact ⟨fun h => h.2, fun h => ⟨ContinuousMap.memLp (p := 2) (torusMeasure d) ℝ u, h⟩⟩

theorem inSobolev_const {d : ℕ} (s : ℝ) (c : ℝ) :
    InSobolev s ⇑(ContinuousMap.const (Torus d) c) := by
  classical
  rw [inSobolev_iff_memℓp, memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ℝ≥0∞).toReal)]
  refine summable_of_ne_finset_zero (s := {0}) fun k hk => ?_
  have hk' : k ≠ 0 := by simpa using hk
  simp [scaledCoeff, coefficient_const, hk']

/-! ## The subalgebra and the type `Hs d s` -/

variable (d : ℕ) (s : ℝ) [SobolevIndex d s]

/-- `H^s(𝕋^d) ∩ C(𝕋^d, ℝ)` as a subalgebra of the real continuous functions. -/
def sobolevAlg : Subalgebra ℝ (Space d) where
  carrier := {u | InSobolev s ⇑u}
  mul_mem' := fun {u v} hu hv =>
    (BecknerOnofri.V2.Onset.sobolev_mul_space (SobolevIndex.hd d s) (SobolevIndex.hs d s) u v hu hv).1
  add_mem' := fun {u v} hu hv => by
    rw [Set.mem_ofPred_eq, inSobolev_iff_memℓp, scaledCoeff_add]
    exact ((inSobolev_iff_memℓp s u).mp hu).add ((inSobolev_iff_memℓp s v).mp hv)
  zero_mem' := by
    rw [Set.mem_ofPred_eq, inSobolev_iff_memℓp, scaledCoeff_zero]
    exact zero_memℓp
  one_mem' := inSobolev_const s 1
  algebraMap_mem' := fun c => inSobolev_const s c

/-- The Banach algebra `H^s(𝕋^d)` (continuous representatives), `s > d/2`.  A `def` (not an
`abbrev`) so that the metric structure of `C(𝕋^d, ℝ)` is not inherited by the subtype. -/
def Hs : Type := ↥(sobolevAlg d s)

instance : CommRing (Hs d s) := inferInstanceAs (CommRing ↥(sobolevAlg d s))
instance : Algebra ℝ (Hs d s) := inferInstanceAs (Algebra ℝ ↥(sobolevAlg d s))

variable {d s}

/-- The underlying continuous function. -/
def Hs.val (u : Hs d s) : Space d := Subtype.val u

theorem Hs.val_injective : Function.Injective (Hs.val : Hs d s → Space d) :=
  fun _ _ h => Subtype.ext h

theorem Hs.ext {u v : Hs d s} (h : u.val = v.val) : u = v := Hs.val_injective h

theorem Hs.inSobolev (u : Hs d s) : InSobolev s ⇑u.val := u.property

/-- Build an element of `H^s` from a continuous function in `H^s`. -/
def Hs.mk (f : Space d) (hf : InSobolev s ⇑f) : Hs d s := ⟨f, hf⟩

@[simp] theorem Hs.val_mk (f : Space d) (hf : InSobolev s ⇑f) : (Hs.mk f hf).val = f := rfl
@[simp] theorem Hs.val_add (u v : Hs d s) : (u + v).val = u.val + v.val := rfl
@[simp] theorem Hs.val_sub (u v : Hs d s) : (u - v).val = u.val - v.val := rfl
@[simp] theorem Hs.val_neg (u : Hs d s) : (-u).val = -u.val := rfl
@[simp] theorem Hs.val_zero : (0 : Hs d s).val = 0 := rfl
@[simp] theorem Hs.val_one : (1 : Hs d s).val = 1 := rfl
@[simp] theorem Hs.val_mul (u v : Hs d s) : (u * v).val = u.val * v.val := rfl
@[simp] theorem Hs.val_smul (c : ℝ) (u : Hs d s) : (c • u).val = c • u.val := rfl
@[simp] theorem Hs.val_algebraMap (c : ℝ) :
    (algebraMap ℝ (Hs d s) c).val = algebraMap ℝ (Space d) c := rfl

/-- The inclusion `H^s → C(𝕋^d, ℝ)` as an algebra homomorphism. -/
def Hs.toSpaceAlg : Hs d s →ₐ[ℝ] Space d := (sobolevAlg d s).val

@[simp] theorem Hs.toSpaceAlg_apply (u : Hs d s) : Hs.toSpaceAlg u = u.val := rfl

/-- The weighted coefficient sequence of an `H^s` function, as an element of `ℓ²`. -/
def Hs.encode : Hs d s →ₗ[ℝ] FourierL2 d where
  toFun u := ⟨scaledCoeff s u.val, (inSobolev_iff_memℓp s u.val).mp u.inSobolev⟩
  map_add' u v := by
    apply lp.ext
    funext k
    simp [scaledCoeff, mul_add]
  map_smul' c u := by
    apply lp.ext
    funext k
    simp only [Hs.val_smul, RingHom.id_apply, lp.coeFn_smul, Pi.smul_apply]
    exact congrFun (scaledCoeff_smul s c u.val) k

@[simp] theorem Hs.encode_apply (u : Hs d s) (k : Frequency d) :
    Hs.encode u k = scaledCoeff s u.val k := rfl

theorem Hs.encode_eq (u : Hs d s) : Hs.encode u = encodeSobolev ⇑u.val u.inSobolev := by
  apply lp.ext
  funext k
  exact congrFun (scaledCoeff_eq s u.val) k

/-- `‖encode u‖_{ℓ²} = ‖u‖_{H^s}`. -/
theorem Hs.norm_encode (u : Hs d s) : ‖Hs.encode u‖ = sobolevNorm s ⇑u.val := by
  rw [Hs.encode_eq, encodeSobolev_norm]

theorem Hs.encode_injective : Function.Injective (Hs.encode : Hs d s →ₗ[ℝ] FourierL2 d) := by
  intro u v h
  apply Hs.ext
  apply coefficient_ext
  intro k
  have hk := congrFun (congrArg (fun a : FourierL2 d => (a : Frequency d → ℂ)) h) k
  simp only [Hs.encode_apply, scaledCoeff] at hk
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (sobolevScale_pos s k).ne') hk

theorem algConst_pos (d : ℕ) (s : ℝ) [SobolevIndex d s] : 0 < BecknerOnofri.V2.Onset.sobolevAlgConst d s := by
  have hsum := BecknerOnofri.V2.Onset.summable_inverse_scale_sq (SobolevIndex.hd d s)
    (SobolevIndex.hs d s)
  have h1 : (1 : ℝ) ≤ BecknerOnofri.V2.Onset.thetaR d s := by
    have := hsum.le_tsum (0 : Frequency d) (fun j _ => sq_nonneg _)
    have h0 : sobolevScale s (0 : Frequency d) = 1 := by simp [sobolevScale, frequencyLength]
    simpa [BecknerOnofri.V2.Onset.thetaR, h0] using this
  unfold BecknerOnofri.V2.Onset.sobolevAlgConst
  have : 0 < Real.sqrt (BecknerOnofri.V2.Onset.thetaR d s) := Real.sqrt_pos.mpr (by linarith)
  positivity

/-- The `ℓ²`-valued embedding with the Banach-algebra normalization `C_{d,s} * (w_k û(k))`. -/
def Hs.encodeAlg (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →ₗ[ℝ] FourierL2 d :=
  (BecknerOnofri.V2.Onset.sobolevAlgConst d s) • Hs.encode

theorem Hs.encodeAlg_injective (d : ℕ) (s : ℝ) [SobolevIndex d s] :
    Function.Injective (Hs.encodeAlg d s) := by
  intro u v h
  apply Hs.encode_injective
  have hC : BecknerOnofri.V2.Onset.sobolevAlgConst d s ≠ 0 := (algConst_pos d s).ne'
  have h' : (BecknerOnofri.V2.Onset.sobolevAlgConst d s) • Hs.encode u =
      (BecknerOnofri.V2.Onset.sobolevAlgConst d s) • Hs.encode v := h
  exact smul_right_injective _ hC h'

instance : NormedAddCommGroup (Hs d s) :=
  NormedAddCommGroup.induced (Hs d s) (FourierL2 d) (Hs.encodeAlg d s) (Hs.encodeAlg_injective d s)

instance : NormedSpace ℝ (Hs d s) :=
  NormedSpace.induced ℝ (Hs d s) (FourierL2 d) (Hs.encodeAlg d s)

/-- The norm of `Hs d s` is the Banach-algebra constant times the manuscript's `H^s` norm. -/
theorem Hs.norm_eq (u : Hs d s) :
    ‖u‖ = BecknerOnofri.V2.Onset.sobolevAlgConst d s * sobolevNorm s ⇑u.val := by
  change ‖(BecknerOnofri.V2.Onset.sobolevAlgConst d s) • Hs.encode u‖ = _
  rw [norm_smul, Hs.norm_encode, Real.norm_of_nonneg (algConst_pos d s).le]

theorem Hs.sobolevNorm_eq (u : Hs d s) :
    sobolevNorm s ⇑u.val = ‖u‖ / BecknerOnofri.V2.Onset.sobolevAlgConst d s := by
  rw [Hs.norm_eq]
  field_simp [(algConst_pos d s).ne']

theorem Hs.dist_eq_encodeAlg (u v : Hs d s) : dist u v = dist (Hs.encodeAlg d s u) (Hs.encodeAlg d s v) := rfl

theorem Hs.isometry_encodeAlg : Isometry (Hs.encodeAlg d s) :=
  AddMonoidHomClass.isometry_of_norm _ (fun _ => rfl)

instance : NormedRing (Hs d s) :=
  { (inferInstance : NormedAddCommGroup (Hs d s)), (inferInstance : Ring (Hs d s)) with
    norm_mul_le := fun u v => by
      rw [Hs.norm_eq, Hs.norm_eq, Hs.norm_eq]
      have hC := algConst_pos d s
      have h := (BecknerOnofri.V2.Onset.sobolev_mul_space (SobolevIndex.hd d s)
        (SobolevIndex.hs d s) u.val v.val u.inSobolev v.inSobolev).2
      have h0 := BecknerOnofri.V2.Onset.sobolevNorm_nonneg' (d := d) s ⇑(u.val * v.val)
      rw [Hs.val_mul]
      calc BecknerOnofri.V2.Onset.sobolevAlgConst d s * sobolevNorm s ⇑(u.val * v.val)
          ≤ BecknerOnofri.V2.Onset.sobolevAlgConst d s *
              (BecknerOnofri.V2.Onset.sobolevAlgConst d s * sobolevNorm s ⇑u.val *
                sobolevNorm s ⇑v.val) := by
            gcongr
        _ = _ := by ring }

instance : NormedCommRing (Hs d s) :=
  { (inferInstance : NormedRing (Hs d s)), (inferInstance : CommRing (Hs d s)) with }

instance : NormedAlgebra ℝ (Hs d s) :=
  { (inferInstance : Algebra ℝ (Hs d s)), (inferInstance : NormedSpace ℝ (Hs d s)) with }

/-! ## Continuity of the inclusion, completeness -/

theorem Hs.norm_val_le (u : Hs d s) :
    ‖u.val‖ ≤ (‖SobolevEmbedding.inverseScaleLp (SobolevIndex.hd d s) (SobolevIndex.hs d s)‖ /
      BecknerOnofri.V2.Onset.sobolevAlgConst d s) * ‖u‖ := by
  have h := SobolevEmbedding.continuous_norm_bound (SobolevIndex.hd d s) (SobolevIndex.hs d s)
    u.val u.inSobolev
  rw [Hs.sobolevNorm_eq] at h
  calc ‖u.val‖ ≤ _ := h
    _ = _ := by ring

/-- The continuous inclusion `H^s ↪ C(𝕋^d, ℝ)`. -/
def Hs.toSpaceCLM (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] Space d :=
  LinearMap.mkContinuous (Hs.toSpaceAlg (d := d) (s := s)).toLinearMap
    (‖SobolevEmbedding.inverseScaleLp (SobolevIndex.hd d s) (SobolevIndex.hs d s)‖ /
      BecknerOnofri.V2.Onset.sobolevAlgConst d s) Hs.norm_val_le

@[simp] theorem Hs.toSpaceCLM_apply (u : Hs d s) : Hs.toSpaceCLM d s u = u.val := rfl

theorem Hs.continuous_val : Continuous (Hs.val : Hs d s → Space d) :=
  (Hs.toSpaceCLM d s).continuous

/-- The Fourier coefficient functional `u ↦ û(k)` on `H^s`. -/
def Hs.coeffCLM (k : Frequency d) : Hs d s →L[ℝ] ℂ := (coefficient k).comp (Hs.toSpaceCLM d s)

@[simp] theorem Hs.coeffCLM_apply (k : Frequency d) (u : Hs d s) :
    Hs.coeffCLM k u = coefficient k u.val := rfl

/-- The mean functional `u ↦ ∫ u` on `H^s`. -/
def Hs.meanCLM (d : ℕ) (s : ℝ) [SobolevIndex d s] : Hs d s →L[ℝ] ℝ := (mean d).comp (Hs.toSpaceCLM d s)

@[simp] theorem Hs.meanCLM_apply (u : Hs d s) : Hs.meanCLM d s u = mean d u.val := rfl

instance : CompleteSpace (Hs d s) := by
  apply Metric.complete_of_cauchySeq_tendsto
  intro u hu
  have hf : CauchySeq (fun n => (u n).val) :=
    (Hs.toSpaceCLM d s).lipschitzWith.cauchySeq_comp hu
  obtain ⟨f, hf'⟩ := cauchySeq_tendsto_of_complete hf
  have hb : CauchySeq (fun n => Hs.encodeAlg d s (u n)) :=
    Hs.isometry_encodeAlg.lipschitzWith.cauchySeq_comp hu
  obtain ⟨b, hb'⟩ := cauchySeq_tendsto_of_complete hb
  set C := BecknerOnofri.V2.Onset.sobolevAlgConst d s with hCdef
  have hC : 0 < C := algConst_pos d s
  have hk : ∀ k, (C : ℂ) * scaledCoeff s f k = b k := by
    intro k
    have h1 : Filter.Tendsto (fun n => Hs.encodeAlg d s (u n) k) Filter.atTop (𝓝 (b k)) :=
      ((lp.evalCLM ℂ (fun _ : Frequency d => ℂ) 2 k).continuous.tendsto b).comp hb'
    have h2 : Filter.Tendsto (fun n => Hs.encodeAlg d s (u n) k) Filter.atTop
        (𝓝 ((C : ℂ) * scaledCoeff s f k)) := by
      have h3 : Filter.Tendsto (fun n => coefficient k (u n).val) Filter.atTop
          (𝓝 (coefficient k f)) := ((coefficient k).continuous.tendsto f).comp hf'
      have h4 := h3.const_mul ((C : ℂ) * (sobolevScale s k : ℂ))
      have e : ∀ n, Hs.encodeAlg d s (u n) k =
          (C : ℂ) * (sobolevScale s k : ℂ) * coefficient k (u n).val := fun n => by
        simp [Hs.encodeAlg, scaledCoeff, Complex.real_smul, hCdef]
        ring
      simp_rw [e]
      convert h4 using 2
      simp only [scaledCoeff]
      ring
    exact tendsto_nhds_unique h2 h1
  have hmem : InSobolev s ⇑f := by
    rw [inSobolev_iff_memℓp]
    have : scaledCoeff s f = ((C⁻¹ : ℝ) : ℂ) • (b : Frequency d → ℂ) := by
      funext k
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← hk k, ← mul_assoc]
      have : ((C⁻¹ : ℝ) : ℂ) * (C : ℂ) = 1 := by
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ hC.ne', Complex.ofReal_one]
      rw [this, one_mul]
    rw [this]
    exact (lp.memℓp b).const_smul _
  refine ⟨Hs.mk f hmem, ?_⟩
  have hg : Hs.encodeAlg d s (Hs.mk f hmem) = b := by
    apply lp.ext
    funext k
    have := hk k
    simp only [Hs.encodeAlg, LinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply, Hs.encode_apply,
      Hs.val_mk, Complex.real_smul]
    exact this
  rw [Isometry.tendsto_nhds_iff Hs.isometry_encodeAlg, hg]
  exact hb'

end BecknerOnofri.V2.Reaudit.Sobolev
