module

public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicLocalCoverAlgebra
public import DedekindZetaZeroFree.Arithmetic.LocalFields.CubeNeighborhoodsAndMatrixCongruences

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPDeepRawSplitting

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))

private lemma tau_chart (K : Type*) [Field K] (M : Type*) [CommGroup M]
    (B : Kˣ → Kˣ → M)
    (hL : ∀ a b c, B (a * b) c = B a c * B b c)
    (hR : ∀ a b c, B a (b * c) = B a b * B a c)
    (hS : ∀ a b : Kˣ, (a : K) + b = 1 → B a b = 1)
    (hC : ∀ a b : Kˣ, B (a ^ 3) b = 1 ∧ B a (b ^ 3) = 1)
    (hN : ∀ a : Kˣ, B a (-a) = 1)
    (g h : KubotaRankTwo.GL2 K)
    (hdiag : ∀ q ∈ ({g, h, g * h} : Set (KubotaRankTwo.GL2 K)),
      ∀ i : Fin 2, ∃ t : Kˣ, ((t ^ 3 : Kˣ) : K) = q i i)
    (hdet : ∃ t : Kˣ, t ^ 3 = KubotaRankTwo.det K g) :
    KubotaElementaryLastArgument.tau K M B g h = 1 := by
  classical
  let L (b : Kˣ) : Kˣ →* M := {
    toFun := fun a => B a b
    map_one' := by
      apply mul_left_cancel (a := B 1 b)
      simpa using (hL 1 1 b).symm
    map_mul' := fun a c => hL a c b }
  let R (a : Kˣ) : Kˣ →* M := {
    toFun := B a
    map_one' := by
      apply mul_left_cancel (a := B a 1)
      simpa using (hR a 1 1).symm
    map_mul' := hR a }
  have hDL (a b c : Kˣ) : B (a / b) c = B a c / B b c := map_div (L c) a b
  have hDR (a b c : Kˣ) : B a (b / c) = B a b / B a c := map_div (R a) b c
  have hIL (a b : Kˣ) : B a⁻¹ b = (B a b)⁻¹ := map_inv (L b) a
  have hIR (a b : Kˣ) : B a b⁻¹ = (B a b)⁻¹ := map_inv (R a) b
  have h1L (b : Kˣ) : B 1 b = 1 := (L b).map_one
  have h1R (a : Kˣ) : B a 1 = 1 := (R a).map_one
  obtain ⟨ta, hta⟩ := hdiag h (by simp) 0
  obtain ⟨td, htd⟩ := hdiag g (by simp) 1
  let A : Kˣ := ta ^ 3
  let D : Kˣ := td ^ 3
  have hA : (A : K) = h 0 0 := hta
  have hD : (D : K) = g 1 1 := htd
  have hAL (b : Kˣ) : B A b = 1 := (hC ta b).1
  have hAR (a : Kˣ) : B a A = 1 := (hC a ta).2
  have hDL' (b : Kˣ) : B D b = 1 := (hC td b).1
  have hDR' (a : Kˣ) : B a D = 1 := (hC a td).2
  obtain ⟨te, hte⟩ := hdet
  have hER (a : Kˣ) : B a (KubotaRankTwo.det K g) = 1 := by
    rw [← hte]; exact (hC a te).2
  have hentry : (g * h : KubotaRankTwo.GL2 K) 1 0 = g 1 0 * h 0 0 + g 1 1 * h 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hXval (q : KubotaRankTwo.GL2 K) :
      ((KubotaRankTwo.X K q : Kˣ) : K) =
        if q 1 0 = 0 then q 1 1 else q 1 0 := by
    rfl
  have hXcube (q : KubotaRankTwo.GL2 K)
      (hq : q ∈ ({g, h, g * h} : Set (KubotaRankTwo.GL2 K))) (hz : q 1 0 = 0) :
      ∃ t : Kˣ, t ^ 3 = KubotaRankTwo.X K q := by
    obtain ⟨t, ht⟩ := hdiag q hq 1
    refine ⟨t, Units.ext ?_⟩
    rw [hXval, if_pos hz]
    exact ht
  unfold KubotaElementaryLastArgument.tau
  have htwist (a b c : Kˣ) : B a (b / (c * KubotaRankTwo.det K g)) = B a (b / c) := by
    rw [hDR a b, hR, hER, mul_one, ← hDR]
  rw [htwist]
  by_cases hc : g 1 0 = 0
  · obtain ⟨t, ht⟩ := hXcube g (by simp) hc
    by_cases hf : h 1 0 = 0
    · have hz : (g * h : KubotaRankTwo.GL2 K) 1 0 = 0 := by rw [hentry, hc, hf]; ring
      obtain ⟨s, hs⟩ := hXcube (g * h) (by simp) hz
      rw [hDL, ← hs, ← ht, (hC s _).1, (hC t _).1, one_div, inv_one]
    · have hz : (g * h : KubotaRankTwo.GL2 K) 1 0 ≠ 0 := by
        rw [hentry, hc, zero_mul, zero_add, ← hD]
        exact mul_ne_zero D.ne_zero hf
      have hX : KubotaRankTwo.X K (g * h) = D * KubotaRankTwo.X K h := by
        apply Units.ext
        rw [Units.val_mul, hXval, hXval, if_neg hf, if_neg hz]
        rw [hentry, hc, zero_mul, zero_add, hD]
      rw [hX, mul_div_cancel_right, hDR']
  · by_cases hf : h 1 0 = 0
    · have hz : (g * h : KubotaRankTwo.GL2 K) 1 0 ≠ 0 := by
        rw [hentry, hf, mul_zero, add_zero, ← hA]
        exact mul_ne_zero hc A.ne_zero
      have hX : KubotaRankTwo.X K (g * h) = KubotaRankTwo.X K g * A := by
        apply Units.ext
        rw [Units.val_mul, hXval, hXval, if_neg hc, if_neg hz]
        rw [hentry, hf, mul_zero, add_zero, hA]
      rw [hX, mul_div_cancel_left, hAL]
    · by_cases hz : (g * h : KubotaRankTwo.GL2 K) 1 0 = 0
      · obtain ⟨s, hs⟩ := hXcube (g * h) (by simp) hz
        have hrel : KubotaRankTwo.X K h = -(KubotaRankTwo.X K g) * A / D := by
          apply Units.ext
          simp only [Units.val_div_eq_div_val, Units.val_mul, Units.val_neg,
            hXval, if_neg hc, if_neg hf, hA, hD]
          apply (eq_div_iff (show g 1 1 ≠ 0 from hD ▸ D.ne_zero)).2
          have he := hentry.symm.trans hz
          rw [hD] at *
          linear_combination he
        rw [hDL, ← hs, (hC s _).1, one_div, hDR, (hC _ s).2, one_div]
        rw [hrel, hDR, hR, hDR', hAR, hN]
        simp
      · let U : Kˣ := KubotaRankTwo.X K g * A
        let V : Kˣ := D * KubotaRankTwo.X K h
        let S : Kˣ := KubotaRankTwo.X K (g * h)
        have hsum : (U : K) + (V : K) = (S : K) := by
          change ((KubotaRankTwo.X K g : Kˣ) : K) * (A : K) + (D : K) * ((KubotaRankTwo.X K h : Kˣ) : K) = ((KubotaRankTwo.X K (g * h) : Kˣ) : K)
          rw [hXval, hXval, hXval, if_neg hc, if_neg hf, if_neg hz, hA, hD]
          exact hentry.symm
        have hst : B (U / S) (V / S) = 1 := by
          apply hS
          simp only [Units.val_div_eq_div_val, ← add_div, hsum]
          exact div_self S.ne_zero
        have hsti : B (S / U) (S / V) = 1 := by
          have he : B (U / S)⁻¹ (V / S)⁻¹ = 1 := by rw [hIL, hIR, hst]; simp
          simpa only [inv_div] using he
        have he : B (S / U) (S / V) =
            B (S / KubotaRankTwo.X K g) (S / KubotaRankTwo.X K h) := by
          simp only [U, V, hDL, hDR, hL, hR, hAL, hAR, hDL', hDR', mul_one, one_mul, div_one]
        exact he ▸ hsti

theorem sigmaTwo_eq_one_on_Gamma (r : ℕ)
    (hcharts : ∀ g ∈ KPLocalCube.Gamma F v r,
      (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
        ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
          KPLocalCube.LocalField F v) = g i i) ∧
      Matrix.GeneralLinearGroup.det g ∈ KPLocalCube.cubes F v)
    (g h : KPLocalCube.LocalGL2 F v)
    (hg : g ∈ KPLocalCube.Gamma F v r)
    (hh : h ∈ KPLocalCube.Gamma F v r) :
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g h = 1 := by
  classical
  let K := KPLocalCube.LocalField F v
  let B := KPHilbert.B3 F ζ hζ (Sum.inr v)
  obtain ⟨hL, hR, _hSkew, hStein, hC, hNeg⟩ :=
    KPHilbert.B3_laws F ζ hζ (Sum.inr v)
  have hdiag : ∀ q ∈ ({g, h, g * h} : Set (KubotaRankTwo.GL2 K)),
      ∀ i : Fin 2, ∃ t : Kˣ, ((t ^ 3 : Kˣ) : K) = q i i := by
    intro q hq i
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with hq | hq | hq
    · subst q; exact (hcharts g hg).1 i
    · subst q; exact (hcharts h hh).1 i
    · subst q; exact (hcharts (g * h) (mul_mem hg hh)).1 i
  obtain ⟨t, ht⟩ := (hcharts g hg).2
  have hdet : ∃ t : Kˣ, t ^ 3 = KubotaRankTwo.det K g := ⟨t, ht⟩
  dsimp only [KPLocalCover.sigmaTwo]
  rw [tau_chart K (rootsOfUnity 3 F) B hL hR hStein hC
    (fun a => (hNeg a).2.2) g h hdiag hdet]
  have ht' : t ^ 3 = KubotaRankTwo.det K g := ht
  have he := (hC t (KubotaRankTwo.det K h)).1
  rw [ht'] at he
  rw [he, one_pow, one_mul]

theorem raw_section_splitting (r : ℕ)
    (hsigma : ∀ g ∈ KPLocalCube.Gamma F v r,
      ∀ h ∈ KPLocalCube.Gamma F v r,
        KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g h = 1) :
    ∃ s : KPLocalCube.Gamma F v r →*
        KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v),
      (∀ g, s g = KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g.val) ∧
      Function.Injective s ∧
      (KPLocalCover.projection F ζ hζ (Sum.inr v)).comp s =
        (KPLocalCube.Gamma F v r).subtype := by
  let s : KPLocalCube.Gamma F v r →*
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) := {
    toFun := fun g => KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g.val
    map_one' := by rfl
    map_mul' := by
      intro g h
      change (⟨g.val * h.val, (1 : rootsOfUnity 3 F)⟩ :
          KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) =
        ⟨g.val * h.val,
          1 * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g.val h.val⟩
      rw [hsigma g g.property h h.property, one_mul, one_mul]
  }
  refine ⟨s, (fun _ => rfl), ?_, ?_⟩
  · intro g h heq
    apply Subtype.ext
    exact congrArg (fun x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v) => x.g) heq
  · ext g
    rfl

theorem deep_raw_splitting :
    ∃ m : ℕ, 1 ≤ m ∧
      (∀ a ∈ KPLocalCube.principalUnitSet F v m,
        ∃ t : (KPLocalCube.LocalField F v)ˣ,
          ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
            KPLocalCube.LocalField F v) = a) ∧
      ∀ r : ℕ, m ≤ r →
        (∀ g ∈ KPLocalCube.Gamma F v r,
          (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
            ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
              KPLocalCube.LocalField F v) = g i i) ∧
          Matrix.GeneralLinearGroup.det g ∈ KPLocalCube.cubes F v) ∧
        (∀ g ∈ KPLocalCube.Gamma F v r,
          ∀ h ∈ KPLocalCube.Gamma F v r,
            KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g h = 1) ∧
        ∃ s : KPLocalCube.Gamma F v r →*
            KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v),
          (∀ g, s g = KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g.val) ∧
          Function.Injective s ∧
          (KPLocalCover.projection F ζ hζ (Sum.inr v)).comp s =
            (KPLocalCube.Gamma F v r).subtype := by
  obtain ⟨m, hm, hcubes, _hbasis, hdeep⟩ :=
    KPLocalCube.deep_principal_units_and_matrix_charts F v
  refine ⟨m, hm, hcubes, ?_⟩
  intro r hr
  obtain ⟨_hcompact, _hopen, hcharts⟩ := hdeep r hr
  have hsigma : ∀ g ∈ KPLocalCube.Gamma F v r,
      ∀ h ∈ KPLocalCube.Gamma F v r,
        KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g h = 1 := by
    intro g hg h hh
    exact sigmaTwo_eq_one_on_Gamma F ζ hζ v r hcharts g h hg hh
  exact ⟨hcharts, hsigma, raw_section_splitting F ζ hζ v r hsigma⟩

end
end DedekindZetaZeroFree.KPDeepRawSplitting
