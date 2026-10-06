module

public import BecknerOnofri.SpinPressureCertificateIdentity

@[expose] public section

/-!
# Soundness of one cell of the certificate for Lemma 5.20

If `checkCell lo hi d = true`, then `t⁴/200 < 𝓑(t)` for every `t ∈ [lo/d, hi/d] ⊆ (0, 1)`:
the Taylor model of `scalarModel (mkCtx lo hi d)` encloses `𝓑(t) - t⁴/200`
(`scalarModel_mem`, `scalarValue_eq`), and its range has a positive lower endpoint.
-/

namespace BecknerOnofri.HighDim.Spin.PressureCertificate

open Real

/-- The cell context admits every offset `s = t - t₀` from its midpoint. -/
theorem mkCtx_adm {lo hi d : ℤ} (hd : 0 < d) {t : ℝ} (ht : (lo : ℝ) / d ≤ t ∧ t ≤ (hi : ℝ) / d) :
    (mkCtx lo hi d).Adm (t - ((lo + hi : ℤ) : ℝ) / ((2 * d : ℤ) : ℝ)) ∧
      (mkCtx lo hi d).mid.Mem (((lo + hi : ℤ) : ℝ) / ((2 * d : ℤ) : ℝ)) := by
  have hS := scale_pos
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set H := cdiv ((hi - lo) * scale) (2 * d)
  have hH : ((hi - lo : ℤ) : ℝ) * scale / ((2 * d : ℤ) : ℝ) ≤ (H : ℝ) := by
    have := le_cdiv ((hi - lo) * scale) (2 * d) (by omega)
    push_cast at this ⊢
    exact this
  set s := t - ((lo + hi : ℤ) : ℝ) / ((2 * d : ℤ) : ℝ)
  have hs : |s| ≤ ((hi - lo : ℤ) : ℝ) / ((2 * d : ℤ) : ℝ) := by
    rw [abs_le]
    push_cast at ht ⊢
    constructor
    · have : (lo : ℝ) / d = ((lo : ℝ) + hi) / (2 * d) - ((hi : ℝ) - lo) / (2 * d) := by
        field_simp; ring
      simp only [s]; push_cast; linarith
    · have : (hi : ℝ) / d = ((lo : ℝ) + hi) / (2 * d) + ((hi : ℝ) - lo) / (2 * d) := by
        field_simp; ring
      simp only [s]; push_cast; linarith
  have hsH : |s| ≤ (H : ℝ) / scale := by
    rw [le_div_iff₀ hS]
    calc |s| * scale ≤ ((hi - lo : ℤ) : ℝ) / ((2 * d : ℤ) : ℝ) * scale :=
          mul_le_mul_of_nonneg_right hs hS.le
      _ = ((hi - lo : ℤ) : ℝ) * scale / ((2 * d : ℤ) : ℝ) := by ring
      _ ≤ H := hH
  refine ⟨⟨Iv.mem_symm hsH, ?_, ?_⟩, ?_⟩
  · simp only [mkCtx]
    push_cast
    rw [zero_div]
    positivity
  · simp only [mkCtx]
    have hc := le_cdiv (H * H) scale scale_pos_int
    push_cast at hc
    have hsq : s ^ 2 ≤ ((H : ℝ) / scale) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg s) hsH 2
    calc s ^ 2 ≤ ((H : ℝ) / scale) ^ 2 := hsq
      _ = (H : ℝ) * H / scale / scale := by ring
      _ ≤ _ := by gcongr
  · simpa [mkCtx] using Iv.mem_ofRat (lo + hi) (2 * d) (by omega)

/-- **One cell of Lemma 5.20.** -/
theorem checkCell_sound {lo hi d : ℤ} (h : checkCell lo hi d = true) {t : ℝ}
    (ht : (lo : ℝ) / d ≤ t ∧ t ≤ (hi : ℝ) / d) (ht0 : 0 < t) (ht1 : t < 1) :
    t ^ 4 / 200 < pressureScalar t := by
  simp only [checkCell, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hok, hpos⟩, hd⟩, -⟩ := h
  obtain ⟨hx, hmid⟩ := mkCtx_adm hd ht
  have hmem := scalarModel_mem hx hmid
  have hr := TM.mem_range hx hmem hok
  have hv := Iv.lo_pos_of_mem hr hpos
  rw [add_sub_cancel, scalarValue_eq ht0 ht1] at hv
  linarith

end BecknerOnofri.HighDim.Spin.PressureCertificate
