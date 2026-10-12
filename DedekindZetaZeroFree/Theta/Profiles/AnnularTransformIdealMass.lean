module

public import DedekindZetaZeroFree.HarmonicAnalysis.Poisson.FieldTransform.EulerDerivativesAndDecay
public import DedekindZetaZeroFree.Arithmetic.Ideals.TwoEndedPowerEnvelopeSums
public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.SmoothAnnularWeight

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Sieve

open scoped NumberField Classical ContDiff

theorem initial_annular_transform_mass
    (F : Type) [Field F] [NumberField F]
    (hTC : NumberField.IsTotallyComplex F) :
    let D : ℝ := (|NumberField.discr F| : ℤ)
    let r : ℕ := NumberField.InfinitePlace.nrComplexPlaces F
    let h : ℝ → ℂ := fun x => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ)
    ∃ B : ℝ, 0 ≤ B ∧ ∀ Y : ℝ, 0 < Y →
      ∀ v : Ideal (𝓞 F) → ℂ, (∀ I, ‖v I‖ ≤ 1) →
        let g : Ideal (𝓞 F) → ℂ := fun I =>
          if I = ⊥ then 0 else
            v I * DedekindZetaZeroFree.LargeSieve.fieldTransform D r h ((Ideal.absNorm I : ℝ) / Y)
        Summable (fun I => ‖g I‖) ∧ Summable g ∧ (∑' I, ‖g I‖) ≤ B * Y := by
  classical
  letI : NumberField.IsTotallyComplex F := hTC

  have hD : (0 : ℝ) < ((|NumberField.discr F| : ℤ) : ℝ) := by
    have hne : NumberField.discr F ≠ 0 := NumberField.discr_ne_zero F
    have hpos : (0 : ℤ) < |NumberField.discr F| := by
      rw [Int.abs_eq_natAbs]
      exact_mod_cast Int.natAbs_pos.mpr hne
    exact_mod_cast hpos

  have hr : 1 ≤ NumberField.InfinitePlace.nrComplexPlaces F := by
    have hfr : 0 < Module.finrank ℚ F := Module.finrank_pos
    have h2 := NumberField.IsTotallyComplex.finrank F
    omega

  have hh : ContDiff ℝ ∞ (fun x : ℝ => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ)) := by
    simpa [Function.comp_def] using
      (Complex.ofRealCLM.contDiff (n := ∞)).comp DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_contDiff
  have hhc : HasCompactSupport (fun x : ℝ => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ)) := by
    have hsupp : Function.support (fun x : ℝ => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ))
        = Function.support DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight := by
      ext x; simp [Function.mem_support]
    have hts : tsupport (fun x : ℝ => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ))
        = tsupport DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight := by
      simp only [tsupport, hsupp]
    simpa [HasCompactSupport, hts] using DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight_hasCompactSupport

  obtain ⟨C, hCpos, hCle, hCge⟩ :=
    DedekindZetaZeroFree.LargeSieve.fieldTransform_euler_two_ended_bound
      ((|NumberField.discr F| : ℤ) : ℝ) (NumberField.InfinitePlace.nrComplexPlaces F)
      (fun x : ℝ => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ)) hD hr hh hhc 0 2 (1 / 2)
      (by norm_num)
  obtain ⟨Bc, hBcnonneg, hBc⟩ := initial_two_ended_ideal_sum F
  dsimp only
  refine ⟨C * Bc, mul_nonneg hCpos.le hBcnonneg, ?_⟩
  intro Y hY v hv
  set T : ℝ → ℂ := DedekindZetaZeroFree.LargeSieve.fieldTransform ((|NumberField.discr F| : ℤ) : ℝ)
      (NumberField.InfinitePlace.nrComplexPlaces F)
      (fun x : ℝ => (DedekindZetaZeroFree.LargeSieve.Vendor.annularWeight x : ℂ)) with hTdef
  have hCnorm : ‖(C : ℂ)‖ = C := by
    have h : ‖((C : ℂ))‖ ^ 2 = C ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
    have h2 : 0 ≤ ‖((C : ℂ))‖ := norm_nonneg _
    nlinarith [h, hCpos, h2]
  have hCinvnorm : ‖((C : ℂ))⁻¹‖ = C⁻¹ := by rw [norm_inv, hCnorm]
  have hCne : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hCpos)

  have hb1 : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖T x‖ ≤ C * x ^ (-(1 / 2 : ℝ)) := by
    intro x hx hx1
    have h := hCle x hx hx1
    simp only [DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter_zero, ← hTdef] at h
    exact h
  have hb2 : ∀ x : ℝ, 1 ≤ x → ‖T x‖ ≤ C * x ^ (-(2 : ℝ)) := by
    intro x hx
    have h := hCge x hx
    simp only [DedekindZetaZeroFree.LargeSieve.Vendor.EulerIter_zero, ← hTdef] at h
    exact h
  let gfun : Ideal (𝓞 F) → ℂ := fun I =>
    if I = ⊥ then (0 : ℂ) else v I * T ((Ideal.absNorm I : ℝ) / Y)
  change Summable (fun I : Ideal (𝓞 F) => ‖gfun I‖) ∧ Summable gfun ∧
    (∑' I : Ideal (𝓞 F), ‖gfun I‖) ≤ (C * Bc) * Y
  have hgfun_bot : gfun ⊥ = 0 := by simp [gfun]

  have hkey : ∀ I : Ideal (𝓞 F), I ≠ ⊥ →
      ‖(C : ℂ)⁻¹ * gfun I‖ ≤
        (if (Ideal.absNorm I : ℝ) ≤ Y then ((Ideal.absNorm I : ℝ) / Y) ^ (-(1 / 2 : ℝ))
         else ((Ideal.absNorm I : ℝ) / Y) ^ (-(2 : ℝ))) := by
    intro I hI
    have hgI : gfun I = v I * T ((Ideal.absNorm I : ℝ) / Y) := by simp [gfun, hI]
    have hNI : (Ideal.absNorm I : ℝ) ≠ 0 := by
      exact_mod_cast (show Ideal.absNorm I ≠ 0 from fun h0 =>
        hI (Ideal.absNorm_eq_zero_iff.mp h0))
    simp only [hgI, norm_mul, hCinvnorm]
    set x : ℝ := (Ideal.absNorm I : ℝ) / Y with hxdef
    have hxpos : 0 < x := by
      rw [hxdef]
      exact div_pos (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hNI)) hY
    have hbnd : ‖v I‖ * ‖T x‖ ≤
        C * (if (Ideal.absNorm I : ℝ) ≤ Y then x ^ (-(1 / 2 : ℝ))
             else x ^ (-(2 : ℝ))) := by
      by_cases hcase : (Ideal.absNorm I : ℝ) ≤ Y
      · have hx1 : x ≤ 1 := by rw [hxdef, div_le_one hY]; exact hcase
        rw [if_pos hcase]
        calc ‖v I‖ * ‖T x‖ ≤ 1 * (C * x ^ (-(1 / 2 : ℝ))) :=
              mul_le_mul (hv I) (hb1 x hxpos hx1) (norm_nonneg _) (by norm_num)
          _ = C * x ^ (-(1 / 2 : ℝ)) := by ring
      · have hx1 : 1 ≤ x := by
          rw [hxdef, le_div_iff₀ hY]; linarith [not_le.mp hcase]
        rw [if_neg hcase]
        calc ‖v I‖ * ‖T x‖ ≤ 1 * (C * x ^ (-(2 : ℝ))) :=
              mul_le_mul (hv I) (hb2 x hx1) (norm_nonneg _) (by norm_num)
          _ = C * x ^ (-(2 : ℝ)) := by ring
    calc C⁻¹ * (‖v I‖ * ‖T x‖)
        ≤ C⁻¹ * (C * (if (Ideal.absNorm I : ℝ) ≤ Y then x ^ (-(1 / 2 : ℝ))
                       else x ^ (-(2 : ℝ)))) :=
          mul_le_mul_of_nonneg_left hbnd (inv_nonneg.mpr hCpos.le)
      _ = (if (Ideal.absNorm I : ℝ) ≤ Y then x ^ (-(1 / 2 : ℝ))
           else x ^ (-(2 : ℝ))) := by
          rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hCpos), one_mul]
  obtain ⟨hsum1, hsum2, hle2⟩ :=
    hBc Y hY (fun I : Ideal (𝓞 F) => (C : ℂ)⁻¹ * gfun I) (by simp [hgfun_bot]) hkey
  have hnorm_eq : ∀ I : Ideal (𝓞 F), ‖gfun I‖ = C * ‖(C : ℂ)⁻¹ * gfun I‖ := by
    intro I
    have h1 : gfun I = (C : ℂ) * ((C : ℂ)⁻¹ * gfun I) :=
      (mul_inv_cancel_left₀ hCne (gfun I)).symm
    calc ‖gfun I‖ = ‖(C : ℂ) * ((C : ℂ)⁻¹ * gfun I)‖ := congrArg (fun z : ℂ => ‖z‖) h1
      _ = ‖(C : ℂ)‖ * ‖(C : ℂ)⁻¹ * gfun I‖ := norm_mul _ _
      _ = C * ‖(C : ℂ)⁻¹ * gfun I‖ := by rw [hCnorm]
  refine ⟨?_, ?_, ?_⟩
  · have h := hsum1.mul_left C
    exact h.congr (fun I => (hnorm_eq I).symm)
  · have h := hsum2.mul_left (C : ℂ)
    exact h.congr (fun I => mul_inv_cancel_left₀ hCne (gfun I))
  · calc (∑' I : Ideal (𝓞 F), ‖gfun I‖)
        = ∑' I : Ideal (𝓞 F), C * ‖(C : ℂ)⁻¹ * gfun I‖ :=
          tsum_congr (fun I => hnorm_eq I)
      _ = C * ∑' I : Ideal (𝓞 F), ‖(C : ℂ)⁻¹ * gfun I‖ := tsum_mul_left
      _ ≤ C * (Bc * Y) := mul_le_mul_of_nonneg_left hle2 hCpos.le
      _ = (C * Bc) * Y := by ring

end DedekindZetaZeroFree.LargeSieve.Sieve
