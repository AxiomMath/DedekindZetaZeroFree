module

public import DedekindZetaZeroFree.Metaplectic.Kubota.DeepCongruenceSplitting

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain Topology

namespace DedekindZetaZeroFree.KPDeepConjugationGerms

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (v : HeightOneSpectrum (𝓞 F))

private lemma d_inv (a b : (KPLocalCube.LocalField F v)ˣ) :
    (KubotaRankTwo.d (KPLocalCube.LocalField F v) a b)⁻¹ =
      KubotaRankTwo.d (KPLocalCube.LocalField F v) a⁻¹ b⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [KubotaRankTwo.coe_d, Matrix.mul_apply, Fin.sum_univ_two]

private lemma X_continuousAt_open (g : KPLocalCube.LocalGL2 F v)
    (hg : g 1 0 ≠ 0) : ContinuousAt (KubotaRankTwo.X (KPLocalCube.LocalField F v)) g := by
  have hc : Continuous (fun k : KPLocalCube.LocalGL2 F v => k 1 0) :=
    by fun_prop
  have he : ∀ᶠ k in 𝓝 g, k 1 0 ≠ 0 := hc.continuousAt.eventually_ne hg
  rw [Units.isEmbedding_val₀.isInducing.continuousAt_iff]
  have hh : (fun k => ((KubotaRankTwo.X (KPLocalCube.LocalField F v) k :
        (KPLocalCube.LocalField F v)ˣ) : KPLocalCube.LocalField F v)) =ᶠ[𝓝 g]
        (fun k => k 1 0) := by
    filter_upwards [he] with k hk
    simp [KubotaRankTwo.X, KubotaRankTwo.x, hk]
  exact hc.continuousAt.congr hh.symm

private lemma cubes_nhds (m : ℕ) (hm : 1 ≤ m)
    (hcharts : ∀ k ∈ KPLocalCube.Gamma F v m,
      (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
        ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
          KPLocalCube.LocalField F v) = k i i) ∧
      Matrix.GeneralLinearGroup.det k ∈ KPLocalCube.cubes F v) :
    (KPLocalCube.cubes F v : Set (KPLocalCube.LocalField F v)ˣ) ∈ 𝓝 1 := by
  have hc : Continuous (fun t : (KPLocalCube.LocalField F v)ˣ =>
      KubotaRankTwo.d (KPLocalCube.LocalField F v) t 1) := by
    rw [Units.continuous_iff]
    constructor
    · apply continuous_pi; intro i
      apply continuous_pi; intro j
      fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.coe_d] <;> fun_prop
    · apply continuous_pi; intro i
      apply continuous_pi; intro j
      simp_rw [d_inv F v]
      fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.coe_d] <;> try exact continuous_const
      exact Units.continuous_val.inv₀ (fun u => u.ne_zero)
  have ho := (KPLocalCube.Gamma_compact_open F v m hm).2
  have hone : KubotaRankTwo.d (KPLocalCube.LocalField F v) 1 1 = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [KubotaRankTwo.coe_d]
  have he : ∀ᶠ t in 𝓝 (1 : (KPLocalCube.LocalField F v)ˣ),
      KubotaRankTwo.d (KPLocalCube.LocalField F v) t 1 ∈ KPLocalCube.Gamma F v m :=
    hc.continuousAt.preimage_mem_nhds (by rw [hone]; exact ho.mem_nhds (Subgroup.one_mem _))
  filter_upwards [he] with t ht
  obtain ⟨u, hu⟩ := (hcharts _ ht).1 0
  exact ⟨u, Units.ext (by simpa [KubotaRankTwo.coe_d] using hu)⟩

private lemma lift_conjugation (g k : KPLocalCube.LocalGL2 F v)
    (hs : KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g *
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k *
      (KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g)⁻¹ =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹))
    (x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) (hx : x.g = g) :
    x * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k * x⁻¹ =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹) := by
  have hs' := (mul_inv_eq_iff_eq_mul).mp hs
  have he := congrArg KPLocalCover.CubicGL2Raw.epsilon hs'
  simp only [KPLocalCover.mul_epsilon, KPLocalCover.sectionMap_epsilon,
    KPLocalCover.sectionMap_g, one_mul] at he
  have hmul : x * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹) * x := by
    cases x with
    | mk xg xe =>
      dsimp at hx
      subst xg
      change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
      congr 1
      · simp [KPLocalCover.rawMul, mul_assoc]
      · simpa [KPLocalCover.rawMul, KPLocalCover.sectionMap, mul_comm] using
          congrArg (fun z => xe * z) he
  exact (mul_inv_eq_iff_eq_mul).mpr hmul

 def Good (g : KPLocalCube.LocalGL2 F v) : Prop :=
  ∀ᶠ k in 𝓝 (1 : KPLocalCube.LocalGL2 F v),
    ∀ x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v), x.g = g →
      x * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k * x⁻¹ =
        KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹)

private lemma symbol_cube_left (a b : (KPLocalCube.LocalField F v)ˣ)
    (ha : a ∈ KPLocalCube.cubes F v) : KPHilbert.B3 F ζ hζ (Sum.inr v) a b = 1 := by
  obtain ⟨t, rfl⟩ := ha
  exact (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.1 t b |>.1

private lemma symbol_cube_right (a b : (KPLocalCube.LocalField F v)ˣ)
    (hb : b ∈ KPLocalCube.cubes F v) : KPHilbert.B3 F ζ hζ (Sum.inr v) a b = 1 := by
  obtain ⟨t, rfl⟩ := hb
  exact (KPHilbert.B3_laws F ζ hζ (Sum.inr v)).2.2.2.2.1 a t |>.2

private lemma Good_open (m : ℕ) (hm : 1 ≤ m)
    (hcharts : ∀ k ∈ KPLocalCube.Gamma F v m,
      (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
        ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
          KPLocalCube.LocalField F v) = k i i) ∧
      Matrix.GeneralLinearGroup.det k ∈ KPLocalCube.cubes F v)
    (g : KPLocalCube.LocalGL2 F v) (hg : g 1 0 ≠ 0) : Good F ζ hζ v g := by
  have hr : Filter.Tendsto (fun k : KPLocalCube.LocalGL2 F v =>
      KubotaRankTwo.X (KPLocalCube.LocalField F v) (g * k) /
        KubotaRankTwo.X (KPLocalCube.LocalField F v) g) (𝓝 1) (𝓝 1) := by
    have hx := (X_continuousAt_open F v g hg).tendsto
    have hmul : Filter.Tendsto (fun k : KPLocalCube.LocalGL2 F v => g * k)
        (𝓝 1) (𝓝 g) := by
      have hh : Continuous (fun k : KPLocalCube.LocalGL2 F v => g * k) := by fun_prop
      simpa using hh.tendsto 1
    simpa using (hx.comp hmul).div_const (KubotaRankTwo.X (KPLocalCube.LocalField F v) g)
  have hc := hr (cubes_nhds F v m hm hcharts)
  have htarget : ∀ᶠ k in 𝓝 (1 : KPLocalCube.LocalGL2 F v),
      g * k * g⁻¹ ∈ KPLocalCube.Gamma F v m := by
    have hconj : Continuous (fun k : KPLocalCube.LocalGL2 F v => g * k * g⁻¹) := by fun_prop
    exact hconj.continuousAt.preimage_mem_nhds (by
      simp only [mul_one, mul_inv_cancel]
      exact (KPLocalCube.Gamma_compact_open F v m hm).2.mem_nhds (Subgroup.one_mem _))
  have hsource : ∀ᶠ k in 𝓝 (1 : KPLocalCube.LocalGL2 F v), k ∈ KPLocalCube.Gamma F v m :=
    (KPLocalCube.Gamma_compact_open F v m hm).2.mem_nhds (Subgroup.one_mem _)
  filter_upwards [hc, htarget, hsource] with k hratio hq hk
  intro x hx
  apply lift_conjugation F ζ hζ v g k _ x hx
  apply (mul_inv_eq_iff_eq_mul).mpr
  have he : (g * k * g⁻¹) * g = g * k := by group
  have hs1 : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g k = 1 := by
    unfold KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
    rw [symbol_cube_left F ζ hζ v _ _ hratio,
      symbol_cube_right F ζ hζ v _ _ (hcharts k hk).2]
    simp
  have hs2 : KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (g * k * g⁻¹) g = 1 := by
    unfold KPLocalCover.sigmaTwo KubotaElementaryLastArgument.tau
    rw [he]
    have hb : KubotaRankTwo.X (KPLocalCube.LocalField F v) (g * k) /
        (KubotaRankTwo.X (KPLocalCube.LocalField F v) g *
          KubotaRankTwo.det (KPLocalCube.LocalField F v) (g * k * g⁻¹)) ∈
        KPLocalCube.cubes F v := by
      have heq : KubotaRankTwo.X (KPLocalCube.LocalField F v) (g * k) /
        (KubotaRankTwo.X (KPLocalCube.LocalField F v) g *
          KubotaRankTwo.det (KPLocalCube.LocalField F v) (g * k * g⁻¹)) =
        (KubotaRankTwo.X (KPLocalCube.LocalField F v) (g * k) /
          KubotaRankTwo.X (KPLocalCube.LocalField F v) g) /
            KubotaRankTwo.det (KPLocalCube.LocalField F v) (g * k * g⁻¹) := by
        exact div_mul_eq_div_div _ _ _
      rw [heq]
      exact (KPLocalCube.cubes F v).div_mem hratio (hcharts _ hq).2
    rw [symbol_cube_right F ζ hζ v _ _ hb,
      symbol_cube_left F ζ hζ v _ _ (hcharts _ hq).2]
    simp
  change (KPLocalCover.CubicGL2Raw.mk (g * k) (1 * 1 *
    KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g k) :
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) =
    KPLocalCover.CubicGL2Raw.mk ((g * k * g⁻¹) * g) (1 * 1 *
      KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) (g * k * g⁻¹) g)
  rw [he, hs1, hs2]

private lemma Good_mul (g h : KPLocalCube.LocalGL2 F v)
    (hg : Good F ζ hζ v g) (hh : Good F ζ hζ v h) : Good F ζ hζ v (g * h) := by
  have hc : Filter.Tendsto (fun k : KPLocalCube.LocalGL2 F v => h * k * h⁻¹)
      (𝓝 1) (𝓝 1) := by
    have hh : Continuous (fun k : KPLocalCube.LocalGL2 F v => h * k * h⁻¹) := by fun_prop
    simpa using hh.tendsto 1
  have he := hc.eventually hg
  filter_upwards [he, hh] with k hk hk'
  intro x hx
  let y := (KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g)⁻¹ * x
  have hy : y.g = h := by simp [y, hx]
  have hx' : x = KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g * y := by simp [y]
  rw [hx']
  have hyk := hk' y hy
  have hgk := hk (KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g) rfl
  calc
    _ = KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g *
        (y * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k * y⁻¹) *
        (KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g)⁻¹ := by group
    _ = _ := by rw [hyk, hgk]; congr 1; group

private lemma Good_all (m : ℕ) (hm : 1 ≤ m)
    (hcharts : ∀ k ∈ KPLocalCube.Gamma F v m,
      (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
        ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
          KPLocalCube.LocalField F v) = k i i) ∧
      Matrix.GeneralLinearGroup.det k ∈ KPLocalCube.cubes F v)
    (g : KPLocalCube.LocalGL2 F v) : Good F ζ hζ v g := by
  by_cases hg : g 1 0 = 0
  · let w := KubotaRankTwo.w (KPLocalCube.LocalField F v)
    have hw : (g * w) 1 0 ≠ 0 := by
      simpa [w, KubotaRankTwo.coe_w, Matrix.mul_apply, Fin.sum_univ_two] using
        KubotaRankTwo.bottomRight_ne_zero (KPLocalCube.LocalField F v) g hg
    have hw' : w⁻¹ 1 0 ≠ 0 := by
      have hi : w⁻¹ = w * w * w := by
        apply inv_eq_of_mul_eq_one_right
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [w, KubotaRankTwo.coe_w, Matrix.mul_apply, Fin.sum_univ_two]
      rw [hi]
      simp [w, KubotaRankTwo.coe_w, Matrix.mul_apply, Fin.sum_univ_two]
    have he := Good_mul F ζ hζ v (g * w) w⁻¹
      (Good_open F ζ hζ v m hm hcharts _ hw) (Good_open F ζ hζ v m hm hcharts _ hw')
    simpa using he
  · exact Good_open F ζ hζ v m hm hcharts g hg

theorem cover_eq (x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) :
    x = KPLocalCover.centralInjection F ζ hζ (Sum.inr v) x.epsilon *
        KPLocalCover.sectionMap F ζ hζ (Sum.inr v) x.g := by
  obtain ⟨g, ε⟩ := x
  change (⟨g, ε⟩ : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) =
    ⟨1 * g, ε * 1 * KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) 1 g⟩
  simp

theorem central_comm (ε : rootsOfUnity 3 F)
    (y : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) :
    KPLocalCover.centralInjection F ζ hζ (Sum.inr v) ε * y =
      y * KPLocalCover.centralInjection F ζ hζ (Sum.inr v) ε := by
  obtain ⟨g, δ⟩ := y
  change (⟨1 * g, ε * δ * KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) 1 g⟩ :
      KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v)) =
    ⟨g * 1, δ * ε * KPLocalCover.sigmaTwo F ζ hζ (Sum.inr v) g 1⟩
  simp [mul_comm]

theorem conjugation_compatibility_near_identity (m : ℕ) (hm : 1 ≤ m)
    (hcharts : ∀ k ∈ KPLocalCube.Gamma F v m,
      (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
        ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
          KPLocalCube.LocalField F v) = k i i) ∧
      Matrix.GeneralLinearGroup.det k ∈ KPLocalCube.cubes F v)
    (g : KPLocalCube.LocalGL2 F v) :
    ∃ r : ℕ, m ≤ r ∧ ∀ k ∈ KPLocalCube.Gamma F v r,
      g * k * g⁻¹ ∈ KPLocalCube.Gamma F v m ∧
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g *
        KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k *
        (KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g)⁻¹ =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹) := by
  have he := Good_all F ζ hζ v m hm hcharts g
  have ht : ∀ᶠ k in 𝓝 (1 : KPLocalCube.LocalGL2 F v),
      g * k * g⁻¹ ∈ KPLocalCube.Gamma F v m := by
    have hc : Continuous (fun k : KPLocalCube.LocalGL2 F v => g * k * g⁻¹) := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (by
      simp only [mul_one, mul_inv_cancel]
      exact (KPLocalCube.Gamma_compact_open F v m hm).2.mem_nhds (Subgroup.one_mem _))
  have hboth : {k : KPLocalCube.LocalGL2 F v |
      g * k * g⁻¹ ∈ KPLocalCube.Gamma F v m ∧
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g *
        KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k *
        (KPLocalCover.sectionMap F ζ hζ (Sum.inr v) g)⁻¹ =
          KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹)} ∈ 𝓝 1 := by
    filter_upwards [he, ht] with k hk hq
    exact ⟨hq, hk _ rfl⟩
  exact (KPLocalCube.Gamma_nhds_basis F v m hm).mem_iff.mp hboth

theorem raw_extension_conjugation_near_identity (m : ℕ) (hm : 1 ≤ m)
    (hcharts : ∀ k ∈ KPLocalCube.Gamma F v m,
      (∀ i : Fin 2, ∃ t : (KPLocalCube.LocalField F v)ˣ,
        ((t ^ 3 : (KPLocalCube.LocalField F v)ˣ) :
          KPLocalCube.LocalField F v) = k i i) ∧
      Matrix.GeneralLinearGroup.det k ∈ KPLocalCube.cubes F v)
    (g : KPLocalCube.LocalGL2 F v) :
    ∃ r : ℕ, m ≤ r ∧ ∀ k ∈ KPLocalCube.Gamma F v r,
      g * k * g⁻¹ ∈ KPLocalCube.Gamma F v m ∧
      ∀ x : KPLocalCover.CubicGL2Raw F ζ hζ (Sum.inr v), x.g = g →
        x * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k * x⁻¹ =
          KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹) := by
  obtain ⟨r, hr, h⟩ := conjugation_compatibility_near_identity F ζ hζ v m hm hcharts g
  refine ⟨r, hr, ?_⟩
  intro k hk
  obtain ⟨hq, hs⟩ := h k hk
  refine ⟨hq, ?_⟩
  intro x hx
  have hs' := (mul_inv_eq_iff_eq_mul).mp hs
  have he := congrArg KPLocalCover.CubicGL2Raw.epsilon hs'
  simp only [KPLocalCover.mul_epsilon, KPLocalCover.sectionMap_epsilon,
    KPLocalCover.sectionMap_g, one_mul] at he
  have hmul : x * KPLocalCover.sectionMap F ζ hζ (Sum.inr v) k =
      KPLocalCover.sectionMap F ζ hζ (Sum.inr v) (g * k * g⁻¹) * x := by
    cases x with
    | mk xg xe =>
      dsimp at hx
      subst xg
      change KPLocalCover.CubicGL2Raw.mk _ _ = KPLocalCover.CubicGL2Raw.mk _ _
      congr 1
      · simp [KPLocalCover.rawMul, mul_assoc]
      · simpa [KPLocalCover.rawMul, KPLocalCover.sectionMap, mul_comm] using
          congrArg (fun z => xe * z) he
  exact (mul_inv_eq_iff_eq_mul).mpr hmul

end
end DedekindZetaZeroFree.KPDeepConjugationGerms
