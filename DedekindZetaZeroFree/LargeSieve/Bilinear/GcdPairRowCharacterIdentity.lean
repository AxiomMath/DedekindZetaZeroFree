module

public import DedekindZetaZeroFree.LFunctions.Hecke.QuadraticFamilies.UniformConductorControl

@[expose] public section

namespace DedekindZetaZeroFree.LargeSieve.Bilinear

open scoped NumberField Classical
open DedekindZetaZeroFree

variable {F : Type} [Field F] [NumberField F]

private theorem sup_mul_eq_top {I X Y : Ideal (𝓞 F)}
    (hX : I ⊔ X = ⊤) (hY : I ⊔ Y = ⊤) : I ⊔ X * Y = ⊤ :=
  ((Ideal.isCoprime_iff_sup_eq.mpr hX).mul_right
    (Ideal.isCoprime_iff_sup_eq.mpr hY)).sup_eq

private theorem le_of_dvd_ideal {X Y : Ideal (𝓞 F)} (h : X ∣ Y) : Y ≤ X := by
  obtain ⟨k, hk⟩ := h
  rw [hk]
  exact Ideal.mul_le_left

variable {c : Ideal (𝓞 F)}

theorem pairRowTransport
    (hc : c ≠ ⊥) (Q : QuadraticHeckeFamily F c)
    {q : Ideal (𝓞 F)} (hq : q ≠ ⊥) (hcq : c ∣ q)
    (hcontrol : ∀ b : Ideal (𝓞 F), Squarefree b → b ⊔ c = ⊤ →
      Q.cond b ∣ b * q ∧ b ∣ Q.cond b * q)
    {d u v : Ideal (𝓞 F)}
    (hd0 : d ≠ ⊥) (hu0 : u ≠ ⊥) (hv0 : v ≠ ⊥)
    (hd : Squarefree d) (hu : Squarefree u) (hv : Squarefree v)
    (hdu : Squarefree (d * u)) (hdv : Squarefree (d * v))
    (hduc : (d * u) ⊔ c = ⊤) (hdvc : (d * v) ⊔ c = ⊤)
    (huv : u ⊔ v = ⊤) (hduv : d ⊔ (u * v) = ⊤)
    (hclass : Q.cls (d * u) = Q.cls (d * v)) :
    ∃ ψ : RayClassCharacter F (u * v), ψ.IsPrimitive ∧
      (∀ I : Ideal (𝓞 F), I ⊔ (Q.cond u * Q.cond v) = ⊤ →
        ψ I = (Q.χ u) I * starRingEnd ℂ ((Q.χ v) I)) ∧
      (∀ I : Ideal (𝓞 F), I ⊔ (q * d) = ⊤ →
        (Q.χ (d * u)) I * starRingEnd ℂ ((Q.χ (d * v)) I) = ψ I ∧
          ψ I = (Q.χ u) I * starRingEnd ℂ ((Q.χ v) I)) := by

  have hdc : d ⊔ c = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = d * u ⊔ c := hduc.symm
      _ ≤ d ⊔ c := sup_le_sup_right Ideal.mul_le_left c
  have huc : u ⊔ c = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = d * u ⊔ c := hduc.symm
      _ ≤ u ⊔ c := sup_le_sup_right Ideal.mul_le_right c
  have hvc : v ⊔ c = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = d * v ⊔ c := hdvc.symm
      _ ≤ v ⊔ c := sup_le_sup_right Ideal.mul_le_right c

  have hclsu : Q.cls u = Q.cls v :=
    (ClassTwists.cls_mul_eq_iff Q d u v hdc huc hvc hduc hdvc).mp hclass
  obtain ⟨ψ, hψprim, hψagr⟩ := Q.product_primitive u v hu huc hv hvc huv hclsu

  have hsup : d * u ⊔ d * v = d := by
    rw [← Ideal.mul_sup, huv, Ideal.mul_top]
  have hau : d * u = (d * u ⊔ d * v) * u := by rw [hsup]
  have hbv : d * v = (d * u ⊔ d * v) * v := by rw [hsup]
  obtain ⟨-, hagree, -, -, -⟩ :=
    rawGcdPairTransport hc Q hdu hdv hduc hdvc hclass hau hbv
  refine ⟨ψ, hψprim, fun I hI => hψagr I hI, ?_⟩
  intro I hI
  by_cases hIbot : I = ⊥
  · subst hIbot
    simp [RayOperations.map_bot]
  · have hIq : I ⊔ q = ⊤ := by
      rw [eq_top_iff]
      calc ⊤ = I ⊔ (q * d) := hI.symm
        _ ≤ I ⊔ q := sup_le_sup_left Ideal.mul_le_left I
    have hId : I ⊔ d = ⊤ := by
      rw [eq_top_iff]
      calc ⊤ = I ⊔ (q * d) := hI.symm
        _ ≤ I ⊔ d := sup_le_sup_left Ideal.mul_le_right I
    have hIc : I ⊔ c = ⊤ := by
      rw [eq_top_iff]
      calc ⊤ = I ⊔ q := hIq.symm
        _ ≤ I ⊔ c := sup_le_sup_left (le_of_dvd_ideal hcq) I
    by_cases hIuv : I ⊔ (u * v) = ⊤
    ·
      have hIu : I ⊔ u = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = I ⊔ (u * v) := hIuv.symm
          _ ≤ I ⊔ u := sup_le_sup_left Ideal.mul_le_left I
      have hIv : I ⊔ v = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = I ⊔ (u * v) := hIuv.symm
          _ ≤ I ⊔ v := sup_le_sup_left Ideal.mul_le_right I
      have hIdu : I ⊔ (d * u) = ⊤ := sup_mul_eq_top hId hIu
      have hIdv : I ⊔ (d * v) = ⊤ := sup_mul_eq_top hId hIv
      have hIconddu : I ⊔ Q.cond (d * u) = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = I ⊔ ((d * u) * q) := (sup_mul_eq_top hIdu hIq).symm
          _ ≤ I ⊔ Q.cond (d * u) :=
              sup_le_sup_left (le_of_dvd_ideal (hcontrol (d * u) hdu hduc).1) I
      have hIconddv : I ⊔ Q.cond (d * v) = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = I ⊔ ((d * v) * q) := (sup_mul_eq_top hIdv hIq).symm
          _ ≤ I ⊔ Q.cond (d * v) :=
              sup_le_sup_left (le_of_dvd_ideal (hcontrol (d * v) hdv hdvc).1) I
      have hIcondu : I ⊔ Q.cond u = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = I ⊔ (u * q) := (sup_mul_eq_top hIu hIq).symm
          _ ≤ I ⊔ Q.cond u :=
              sup_le_sup_left (le_of_dvd_ideal (hcontrol u hu huc).1) I
      have hIcondv : I ⊔ Q.cond v = ⊤ := by
        rw [eq_top_iff]
        calc ⊤ = I ⊔ (v * q) := (sup_mul_eq_top hIv hIq).symm
          _ ≤ I ⊔ Q.cond v :=
              sup_le_sup_left (le_of_dvd_ideal (hcontrol v hv hvc).1) I
      have hIR : I ⊔ (c * (d * u) * (d * v) * Q.cond (d * u) * Q.cond (d * v) *
          Q.cond u * Q.cond v) = ⊤ :=
        sup_mul_eq_top
          (sup_mul_eq_top
            (sup_mul_eq_top
              (sup_mul_eq_top
                (sup_mul_eq_top
                  (sup_mul_eq_top hIc hIdu) hIdv) hIconddu) hIconddv) hIcondu) hIcondv
      have hval : (Q.χ (d * u)) I * (Q.χ (d * v)) I = (Q.χ u) I * (Q.χ v) I :=
        hagree I hIbot hIR
      have hcjv : (starRingEnd ℂ) ((Q.χ (d * v)) I) = (Q.χ (d * v)) I :=
        quadraticFamily_conj Q hdv hdvc I
      have hcjv' : (starRingEnd ℂ) ((Q.χ v) I) = (Q.χ v) I :=
        quadraticFamily_conj Q hv hvc I
      have hpsi : ψ I = (Q.χ u) I * starRingEnd ℂ ((Q.χ v) I) :=
        hψagr I (sup_mul_eq_top hIcondu hIcondv)
      exact ⟨by rw [hcjv, hval, ← hcjv', hpsi], by rw [hpsi]⟩
    ·
      have hor : I ⊔ u ≠ ⊤ ∨ I ⊔ v ≠ ⊤ := by
        by_contra h
        push Not at h
        exact hIuv (sup_mul_eq_top h.1 h.2)
      have hzpsi : ψ I = 0 := (ψ.eq_zero_iff' I).mpr (Or.inr hIuv)
      rcases hor with hune | hvne
      · have hcu : I ⊔ Q.cond u ≠ ⊤ := by
          intro hc
          refine hune ?_
          rw [eq_top_iff]
          calc ⊤ = I ⊔ (Q.cond u * q) := (sup_mul_eq_top hc hIq).symm
            _ ≤ I ⊔ u := sup_le_sup_left (le_of_dvd_ideal (hcontrol u hu huc).2) I
        have hcdu : I ⊔ Q.cond (d * u) ≠ ⊤ := by
          intro hc
          refine hune ?_
          rw [eq_top_iff]
          calc ⊤ = I ⊔ (Q.cond (d * u) * q) := (sup_mul_eq_top hc hIq).symm
            _ ≤ I ⊔ (d * u) :=
                sup_le_sup_left (le_of_dvd_ideal (hcontrol (d * u) hdu hduc).2) I
            _ ≤ I ⊔ u := sup_le_sup_left Ideal.mul_le_right I
        have hzu : (Q.χ u) I = 0 := ((Q.χ u).eq_zero_iff' I).mpr (Or.inr hcu)
        have hzdu : (Q.χ (d * u)) I = 0 := ((Q.χ (d * u)).eq_zero_iff' I).mpr (Or.inr hcdu)
        exact ⟨by simp [hzdu, hzpsi], by simp [hzpsi, hzu]⟩
      · have hcv : I ⊔ Q.cond v ≠ ⊤ := by
          intro hc
          refine hvne ?_
          rw [eq_top_iff]
          calc ⊤ = I ⊔ (Q.cond v * q) := (sup_mul_eq_top hc hIq).symm
            _ ≤ I ⊔ v := sup_le_sup_left (le_of_dvd_ideal (hcontrol v hv hvc).2) I
        have hcdv : I ⊔ Q.cond (d * v) ≠ ⊤ := by
          intro hc
          refine hvne ?_
          rw [eq_top_iff]
          calc ⊤ = I ⊔ (Q.cond (d * v) * q) := (sup_mul_eq_top hc hIq).symm
            _ ≤ I ⊔ (d * v) :=
                sup_le_sup_left (le_of_dvd_ideal (hcontrol (d * v) hdv hdvc).2) I
            _ ≤ I ⊔ v := sup_le_sup_left Ideal.mul_le_right I
        have hzv : (Q.χ v) I = 0 := ((Q.χ v).eq_zero_iff' I).mpr (Or.inr hcv)
        have hzdv : (Q.χ (d * v)) I = 0 := ((Q.χ (d * v)).eq_zero_iff' I).mpr (Or.inr hcdv)
        exact ⟨by simp [hzdv, hzpsi], by simp [hzpsi, hzv]⟩

end DedekindZetaZeroFree.LargeSieve.Bilinear
