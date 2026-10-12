module

public import DedekindZetaZeroFree.Arithmetic.ResidueSymbols.Hilbert.SexticHilbertNormalization

@[expose] public section

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPLocalCube

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))

abbrev LocalField := v.adicCompletion F

local instance : ValuativeRel (LocalField F v) :=
  ClassFieldTheory.finitePlaceCompletionValuativeRel F v
local instance : IsNonarchimedeanLocalField (LocalField F v) :=
  ClassFieldTheory.finitePlaceCompletionIsNonarchimedeanLocalField F v

abbrev LocalIntegers := (ValuativeRel.valuation (LocalField F v)).integer

def maximalIdeal : Ideal (LocalIntegers F v) :=
  IsLocalRing.maximalIdeal (LocalIntegers F v)

def principalUnitSet (r : ℕ) : Set (LocalField F v) :=
  {a | ∃ x : LocalIntegers F v,
    x ∈ maximalIdeal F v ^ r ∧ a = 1 + (x : LocalField F v)}

def cubes : Subgroup (LocalField F v)ˣ :=
  (powMonoidHom 3 : (LocalField F v)ˣ →* (LocalField F v)ˣ).range

abbrev IntegerGL2 := Matrix.GeneralLinearGroup (Fin 2) (LocalIntegers F v)
abbrev LocalGL2 := Matrix.GeneralLinearGroup (Fin 2) (LocalField F v)

def integerCongruence (r : ℕ) : Subgroup (IntegerGL2 F v) :=
  (Matrix.GeneralLinearGroup.map
    (Ideal.Quotient.mk (maximalIdeal F v ^ r))).ker

def integerInclusion : IntegerGL2 F v →* LocalGL2 F v :=
  Matrix.GeneralLinearGroup.map (LocalIntegers F v).subtype

def Gamma (r : ℕ) : Subgroup (LocalGL2 F v) :=
  (integerCongruence F v r).map (integerInclusion F v)

theorem mem_integerCongruence_iff (r : ℕ) (g : IntegerGL2 F v) :
    g ∈ integerCongruence F v r ↔
      ∀ i j : Fin 2,
        g i j - (1 : Matrix (Fin 2) (Fin 2) (LocalIntegers F v)) i j ∈
          maximalIdeal F v ^ r := by
  change Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk (maximalIdeal F v ^ r)) g = 1 ↔ _
  rw [Matrix.GeneralLinearGroup.ext_iff]
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.GeneralLinearGroup.coe_one]
  constructor
  · intro h i j
    apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
    simpa [Matrix.one_apply] using h i j
  · intro h i j
    have hi := (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (h i j)
    simpa [Matrix.one_apply] using hi

open Polynomial in
private theorem cube_of_nine_times_maximalIdeal (c : LocalIntegers F v) (hc : c ∈ maximalIdeal F v) :
    ∃ t : (LocalField F v)ˣ, (t ^ 3 : (LocalField F v)ˣ).val = 1 + 9 * (c : LocalField F v) := by
  letI : HenselianRing (LocalIntegers F v) (maximalIdeal F v) :=
    (LocalFieldTheory.localCompleteDVF (LocalField F v)).henselianRing
  let P : (LocalIntegers F v)[X] := X^3 - X^2 - C (3*c)*X - C (3*c^2)
  have hm : P.Monic := by
    have hP : P = X^3 - (X^2 + C (3*c)*X + C (3*c^2)) := by dsimp [P]; ring
    rw [hP]
    apply monic_X_pow_sub
    compute_degree
    norm_num
  have he : P.eval 1 ∈ maximalIdeal F v := by
    simp only [P, eval_sub, eval_pow, eval_X, eval_C, eval_mul, one_pow, mul_one, sub_self]
    exact (maximalIdeal F v).sub_mem ((maximalIdeal F v).sub_mem (Ideal.zero_mem _) ((maximalIdeal F v).mul_mem_left 3 hc))
      ((maximalIdeal F v).mul_mem_left 3 (by simpa [pow_two] using (maximalIdeal F v).mul_mem_left c hc))
  have hd : IsUnit ((Ideal.Quotient.mk (maximalIdeal F v)) (P.derivative.eval 1)) := by
    have h : (Ideal.Quotient.mk (maximalIdeal F v)) (P.derivative.eval 1) = 1 := by
      simp [P, derivative_sub, derivative_pow, derivative_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hc]
      norm_num [map_ofNat]
    rw [h]
    exact isUnit_one
  obtain ⟨w, hw, hwp⟩ := HenselianRing.is_henselian P hm 1 he hd
  have hwn : (w : LocalField F v) ≠ 0 := by
    intro h
    have hw0 : w = 0 := Subtype.val_injective h
    have h1 : (1 : LocalIntegers F v) ∈ maximalIdeal F v := by
      simpa [hw0] using (maximalIdeal F v).neg_mem hwp
    exact (IsLocalRing.maximalIdeal.isMaximal (LocalIntegers F v)).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hwf : (w : LocalField F v)^3 - (w : LocalField F v)^2 - 3*(c : LocalField F v)*(w : LocalField F v) - 3*(c : LocalField F v)^2 = 0 := by
    have heq : w^3 - w^2 - 3*c*w - 3*c^2 = 0 := by
      simpa [Polynomial.IsRoot, P] using hw
    exact congrArg (fun x : LocalIntegers F v => (x : LocalField F v)) heq
  let t : LocalField F v := 1 + 3*(c : LocalField F v)/(w : LocalField F v)
  have ht : t^3 = 1 + 9*(c : LocalField F v) := by
    dsimp [t]
    field_simp [hwn]
    linear_combination -9*(c : LocalField F v)*hwf
  have htn : t ≠ 0 := by
    intro ht0
    have ha : (1 : LocalIntegers F v) + 9*c = 0 := by
      apply Subtype.val_injective
      have hn : ((9 : LocalIntegers F v) : LocalField F v) = 9 := by norm_cast
      simpa only [Subring.coe_add, Subring.coe_one, Subring.coe_mul, Subring.coe_zero, hn, ht0, zero_pow (by decide : (3 : ℕ) ≠ 0)] using ht.symm
    have h1 : (1 : LocalIntegers F v) ∈ maximalIdeal F v := by
      have h9 := (maximalIdeal F v).mul_mem_left 9 hc
      have heq : -(9*c) = (1 : LocalIntegers F v) := by linear_combination -ha
      rw [← heq]
      exact (maximalIdeal F v).neg_mem h9
    exact (IsLocalRing.maximalIdeal.isMaximal (LocalIntegers F v)).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  exact ⟨Units.mk0 t htn, ht⟩

theorem principal_units_eventually_cubes :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ r : ℕ, m ≤ r →
      ∀ a ∈ principalUnitSet F v r, ∃ t : (LocalField F v)ˣ,
        ((t ^ 3 : (LocalField F v)ˣ) : LocalField F v) = a := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (LocalIntegers F v)
  have h9 : Ideal.span ({(9 : LocalIntegers F v)} : Set (LocalIntegers F v)) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact by norm_num
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible h9 hπ
  have hp : maximalIdeal F v ^ n = Ideal.span {(9 : LocalIntegers F v)} := by
    rw [maximalIdeal, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, hn]
  refine ⟨n+1, Nat.le_add_left 1 n, ?_⟩
  intro r hr a ha
  obtain ⟨x, hx, rfl⟩ := ha
  have hx' : x ∈ Ideal.span {(9 : LocalIntegers F v)} * maximalIdeal F v := by
    rw [← hp, ← pow_succ]
    exact Ideal.pow_le_pow_right hr hx
  obtain ⟨c, hc, hcx⟩ := Ideal.mem_span_singleton_mul.mp hx'
  obtain ⟨t, ht⟩ := cube_of_nine_times_maximalIdeal F v c hc
  refine ⟨t, ?_⟩
  rw [ht, ← hcx]
  norm_cast

theorem Gamma_compact_open (r : ℕ) (hr : 1 ≤ r) :
    IsCompact (Gamma F v r : Set (LocalGL2 F v)) ∧
      IsOpen (Gamma F v r : Set (LocalGL2 F v)) := by
  letI : CompactSpace (LocalIntegers F v) := inferInstance
  letI : CompactSpace (Matrix (Fin 2) (Fin 2) (LocalIntegers F v)) :=
    inferInstanceAs (CompactSpace (Fin 2 → Fin 2 → LocalIntegers F v))
  letI : CompactSpace (IntegerGL2 F v) := inferInstance
  have hh : (integerCongruence F v r : Set (IntegerGL2 F v)) =
      {g | ∀ i j : Fin 2, g i j -
        (1 : Matrix (Fin 2) (Fin 2) (LocalIntegers F v)) i j ∈ maximalIdeal F v ^ r} := by
    ext g
    exact mem_integerCongruence_iff F v r g
  have hclosed : IsClosed (integerCongruence F v r : Set (IntegerGL2 F v)) := by
    rw [hh]
    simp only [Set.setOf_forall]
    apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro j
    apply (Ideal.isCompact_of_fg (IsNoetherian.noetherian (maximalIdeal F v ^ r))).isClosed.preimage
    fun_prop
  have hopen : IsOpen (integerCongruence F v r : Set (IntegerGL2 F v)) := by
    rw [hh]
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    apply (IsLocalRing.isOpen_maximalIdeal_pow (LocalIntegers F v) r).preimage
    fun_prop
  have hi : Topology.IsOpenEmbedding (LocalIntegers F v).subtype :=
    (ValuativeRel.valuation (LocalField F v)).isOpen_integer.isOpenEmbedding_subtypeVal
  have hc : Continuous (integerInclusion F v) := hi.continuous.generalLinearGroup_map
  have ho : IsOpenMap (integerInclusion F v) :=
    Units.isOpenMap_map hi.matrix_map.injective hi.matrix_map.isOpenMap
  exact ⟨hclosed.isCompact.image hc, ho _ hopen⟩

private theorem cube_inclusion_injective : Function.Injective (integerInclusion F v) := by
  intro g h he
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  apply Subtype.val_injective
  exact congrArg (fun A : LocalGL2 F v => A i j) he
private theorem cube_Gamma_antitone {r s : ℕ} (hrs : r ≤ s) : Gamma F v s ≤ Gamma F v r := by
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨g, ?_, rfl⟩
  apply (mem_integerCongruence_iff F v r g).mpr
  intro i j
  exact Ideal.pow_le_pow_right hrs ((mem_integerCongruence_iff F v s g).mp hg i j)

theorem Gamma_nhds_basis (m : ℕ) (hm : 1 ≤ m) :
    (nhds (1 : LocalGL2 F v)).HasBasis (fun r : ℕ => m ≤ r)
      (fun r => (Gamma F v r : Set (LocalGL2 F v))) := by
  have hinter : (⋂ n : ℕ, (Gamma F v (m + n) : Set (LocalGL2 F v))) = {1} := by
    apply Set.Subset.antisymm
    · intro g hg
      have hall : ∀ n, g ∈ Gamma F v (m + n) := Set.mem_iInter.mp hg
      obtain ⟨g₀, _, h₀⟩ := hall 0
      have hc : ∀ n, g₀ ∈ integerCongruence F v (m + n) := by
        intro n
        obtain ⟨g₁, hg₁, h₁⟩ := hall n
        have he : g₁ = g₀ := cube_inclusion_injective F v (h₁.trans h₀.symm)
        simpa [he] using hg₁
      have he : g₀ = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        have hz : g₀ i j - (1 : Matrix (Fin 2) (Fin 2) (LocalIntegers F v)) i j ∈
            (⨅ n : ℕ, maximalIdeal F v ^ n) := by
          rw [Ideal.mem_iInf]
          intro n
          exact Ideal.pow_le_pow_right (Nat.le_add_left n m)
            ((mem_integerCongruence_iff F v (m+n) g₀).mp (hc n) i j)
        rw [Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal F v)
          (IsLocalRing.maximalIdeal.isMaximal (LocalIntegers F v)).ne_top] at hz
        exact sub_eq_zero.mp (Ideal.mem_bot.mp hz)
      simp [← h₀, he]
    · intro g hg
      have : g = 1 := Set.mem_singleton_iff.mp hg
      simp [this]
  apply Filter.hasBasis_iff.mpr
  intro U
  constructor
  · intro hU
    have hdir : Directed (fun x y : Set (LocalGL2 F v) => x ⊇ y)
        (fun n : ℕ => (Gamma F v (m+n) : Set (LocalGL2 F v))) := by
      intro a b
      refine ⟨max a b, ?_, ?_⟩
      · exact cube_Gamma_antitone F v (Nat.add_le_add_left (le_max_left _ _) _)
      · exact cube_Gamma_antitone F v (Nat.add_le_add_left (le_max_right _ _) _)
    have hU' : U ∈ nhdsSet (⋂ n : ℕ, (Gamma F v (m+n) : Set (LocalGL2 F v))) := by
      simpa [hinter] using hU
    obtain ⟨n, hn⟩ := exists_subset_nhds_of_isCompact hdir
      (fun n => (Gamma_compact_open F v (m+n) (hm.trans (Nat.le_add_right _ _))).1) hU'
    exact ⟨m+n, Nat.le_add_right _ _, hn⟩
  · rintro ⟨r, hr, hsub⟩
    exact Filter.mem_of_superset ((Gamma_compact_open F v r (hm.trans hr)).2.mem_nhds
      (Subgroup.one_mem _)) hsub

theorem deep_principal_units_and_matrix_charts :
    ∃ m : ℕ, 1 ≤ m ∧
      (∀ a ∈ principalUnitSet F v m, ∃ t : (LocalField F v)ˣ,
        ((t ^ 3 : (LocalField F v)ˣ) : LocalField F v) = a) ∧
      (nhds (1 : LocalGL2 F v)).HasBasis (fun r : ℕ => m ≤ r)
        (fun r => (Gamma F v r : Set (LocalGL2 F v))) ∧
      ∀ r : ℕ, m ≤ r →
        IsCompact (Gamma F v r : Set (LocalGL2 F v)) ∧
        IsOpen (Gamma F v r : Set (LocalGL2 F v)) ∧
        ∀ g ∈ Gamma F v r,
          (∀ i : Fin 2, ∃ t : (LocalField F v)ˣ,
            ((t ^ 3 : (LocalField F v)ˣ) : LocalField F v) = g i i) ∧
          Matrix.GeneralLinearGroup.det g ∈ cubes F v := by
  obtain ⟨m, hm, hc⟩ := principal_units_eventually_cubes F v
  refine ⟨m, hm, hc m le_rfl, Gamma_nhds_basis F v m hm, ?_⟩
  intro r hr
  obtain ⟨hcompact, hopen⟩ := Gamma_compact_open F v r (hm.trans hr)
  refine ⟨hcompact, hopen, ?_⟩
  intro g hg
  obtain ⟨g₀, hg₀, rfl⟩ := hg
  have he := (mem_integerCongruence_iff F v r g₀).mp hg₀
  constructor
  · intro i
    apply hc r hr
    refine ⟨g₀ i i - 1, ?_, ?_⟩
    · simpa using he i i
    · simp [integerInclusion, Matrix.GeneralLinearGroup.map_apply]
  · have hd : (Matrix.GeneralLinearGroup.det g₀ : LocalIntegers F v) - 1 ∈
        maximalIdeal F v ^ r := by
      apply (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp
      have hk : Matrix.GeneralLinearGroup.map
          (Ideal.Quotient.mk (maximalIdeal F v ^ r)) g₀ = 1 := hg₀
      have hdet := congrArg Matrix.GeneralLinearGroup.det hk
      simpa [Matrix.GeneralLinearGroup.map_det] using
        congrArg (fun u : (LocalIntegers F v ⧸ maximalIdeal F v ^ r)ˣ =>
          (u : LocalIntegers F v ⧸ maximalIdeal F v ^ r)) hdet
    obtain ⟨t, ht⟩ := hc r hr (Matrix.GeneralLinearGroup.det
        (integerInclusion F v g₀) : LocalField F v) ⟨
      (Matrix.GeneralLinearGroup.det g₀ : LocalIntegers F v) - 1, hd, by
        simp [integerInclusion, Matrix.GeneralLinearGroup.map_det]⟩
    exact ⟨t, Units.ext ht⟩

end
end DedekindZetaZeroFree.KPLocalCube
