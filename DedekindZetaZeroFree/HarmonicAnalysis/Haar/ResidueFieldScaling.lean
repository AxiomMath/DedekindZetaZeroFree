module

public import Mathlib

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ValuativeRel Classical ENNReal Pointwise

namespace DedekindZetaZeroFree.IntrinsicHaarScaling

def residueCard (K : Type*) [Field K] [ValuativeRel K] : ℕ :=
  Nat.card (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)

def abs (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (x : K) : ℝ :=
  if x = 0 then 0 else
    (residueCard K : ℝ) ^ WithZero.log
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K x))

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]

theorem residue_index_measure (μ : Measure K) [μ.IsAddHaarMeasure] :
    (Nat.card (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) : ℝ≥0∞) *
      μ ((ValuativeRel.valuation K).integer.subtype ''
        (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation K).integer :
          Set ↥(ValuativeRel.valuation K).integer)) =
      μ ((ValuativeRel.valuation K).integer : Set K) := by
  classical
  let R := (ValuativeRel.valuation K).integer
  let κ := IsLocalRing.ResidueField R
  let r : R →+* κ := IsLocalRing.residue R
  letI : Fintype κ := Fintype.ofFinite κ
  letI : MeasurableSpace κ := ⊤
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have hR : MeasurableSet (R : Set K) := (Valued.isClosed_integer K).measurableSet
  let ν : Measure R := μ.comap R.subtype
  haveI : ν.IsAddLeftInvariant := Measure.IsAddLeftInvariant.comap μ
    (f := R.subtype.toAddMonoidHom) (MeasurableEmbedding.subtype_coe hR)
  have hr : Measurable r := by
    apply measurable_to_countable
    intro y
    have he : r ⁻¹' {r y} =
        (fun u : R => u - y) ⁻¹' (IsLocalRing.maximalIdeal R : Set R) := by
      ext u
      change r u = r y ↔ u - y ∈ IsLocalRing.maximalIdeal R
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
    rw [he]
    exact (IsNoetherianRing.isClosed_ideal _).measurableSet.preimage (by fun_prop)
  let ρ : Measure κ := ν.map r
  haveI : ρ.IsAddLeftInvariant := isAddLeftInvariant_map r.toAddMonoidHom.toAddHom hr
    IsLocalRing.residue_surjective
  have hmass : ρ Set.univ = μ (R : Set K) := by
    rw [Measure.map_apply hr MeasurableSet.univ, Set.preimage_univ]
    calc
      ν Set.univ = μ (Subtype.val '' (Set.univ : Set R)) := by
        exact comap_subtype_coe_apply hR μ Set.univ
      _ = μ (R : Set K) := by congr 1; ext x; simp
  have hsingle (x : κ) : ρ {x} = ρ {0} := by
    have he : (fun y : κ => -x + y) ⁻¹' {0} = {x} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h
      · linear_combination h
      · rw [h]; simp
    rw [← he, measure_preimage_add]
  have hsum : (Fintype.card κ : ℝ≥0∞) * ρ {0} = ρ Set.univ := by
    have H := sum_measure_singleton (μ := ρ) (s := Finset.univ)
    simp only [hsingle, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at H
    simpa using H
  have hzero : ρ {0} = μ (R.subtype '' (IsLocalRing.maximalIdeal R : Set R)) := by
    rw [Measure.map_apply hr (MeasurableSet.singleton 0)]
    have hset : r ⁻¹' {0} = (IsLocalRing.maximalIdeal R : Set R) := by
      ext x
      exact IsLocalRing.residue_eq_zero_iff x
    rw [hset]
    exact comap_subtype_coe_apply hR μ _
  simpa only [Nat.card_eq_fintype_card, hzero, hmass] using hsum

theorem uniformizer_image_integerRing
    (π : ↥(ValuativeRel.valuation K).integer) (hπ : Irreducible π) :
    (fun x : K => (π : K) * x) '' ((ValuativeRel.valuation K).integer : Set K) =
      (ValuativeRel.valuation K).integer.subtype ''
        (IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation K).integer :
          Set ↥(ValuativeRel.valuation K).integer) := by
  let R := (ValuativeRel.valuation K).integer
  change (fun x : K => (π : K) * x) '' (R : Set K) =
    R.subtype '' (IsLocalRing.maximalIdeal R : Set R)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨π * (⟨y, hy⟩ : R), ?_, rfl⟩
    rw [hπ.maximalIdeal_eq]
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    exact dvd_mul_right _ _
  · rintro ⟨y, hy, rfl⟩
    rw [hπ.maximalIdeal_eq] at hy
    rw [SetLike.mem_coe, Ideal.mem_span_singleton] at hy
    obtain ⟨z, rfl⟩ := hy
    exact ⟨z, z.property, rfl⟩

theorem uniformizer_image_measure (μ : Measure K) [μ.IsAddHaarMeasure]
    (π : ↥(ValuativeRel.valuation K).integer) (hπ : Irreducible π) :
    μ ((fun x : K => (π : K) * x) '' ((ValuativeRel.valuation K).integer : Set K)) =
      μ ((ValuativeRel.valuation K).integer : Set K) /
        (Nat.card (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) : ℝ≥0∞) := by
  rw [uniformizer_image_integerRing K π hπ]
  apply (ENNReal.eq_div_iff ?_ (ENNReal.natCast_ne_top _)).mpr
  · exact residue_index_measure K μ
  · exact_mod_cast Nat.card_pos (α := IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer).ne'

private lemma pseudo : TopologicalSpace.PseudoMetrizableSpace K := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NormedField K := Valued.toNormedField K (ValuativeRel.ValueGroupWithZero K)
  infer_instance
private lemma sigma : SigmaCompactSpace K := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  apply SigmaCompactSpace_iff_exists_compact_covering.mpr
  refine ⟨fun n => {x | ValuativeRel.valuation K x ≤ e.symm (WithZero.exp (n : ℤ))}, fun n => IsNonarchimedeanLocalField.isCompact_closedBall K _, ?_⟩
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x = 0
  · subst x; simp
  have hv : e (ValuativeRel.valuation K x) ≠ 0 := by simpa [e] using hx
  let l := WithZero.log (e (ValuativeRel.valuation K x))
  refine Set.mem_iUnion.mpr ⟨l.toNat, ?_⟩
  change ValuativeRel.valuation K x ≤ e.symm (WithZero.exp (l.toNat : ℤ))
  rw [← e.toOrderIso.le_iff_le]
  change e (ValuativeRel.valuation K x) ≤ e (e.symm (WithZero.exp (l.toNat : ℤ)))
  rw [e.apply_symm_apply, ← WithZero.exp_log hv, WithZero.exp_le_exp]
  change l ≤ (l.toNat : ℤ)
  omega
abbrev q := Nat.card (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)
private lemma q_pos : (0 : ℝ) < q K := by exact_mod_cast (Nat.card_pos (α := IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer))
private lemma q_gt : (1 : ℝ) < q K := by
  letI := Fintype.ofFinite (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer)
  exact_mod_cast (show 1 < q K from by simpa only [q, Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer))
private lemma apos {x : K} (hx : x ≠ 0) : 0 < abs K x := by
  simp only [abs, if_neg hx]
  exact zpow_pos (q_pos K) _
private lemma amul (x y : K) : abs K (x*y) = abs K x * abs K y := by
  by_cases hx : x = 0
  · subst x; simp [abs]
  by_cases hy : y = 0
  · subst y; simp [abs]
  have hvx : ValuativeRel.valuation K x ≠ 0 := by simpa using hx
  have hvy : ValuativeRel.valuation K y ≠ 0 := by simpa using hy
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hex : e (ValuativeRel.valuation K x) ≠ 0 := by simpa [e] using hvx
  have hey : e (ValuativeRel.valuation K y) ≠ 0 := by simpa [e] using hvy
  simp only [abs, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), _root_.map_mul]
  rw [WithZero.log_mul hex hey, zpow_add₀]
  exact (q_pos K).ne'
private lemma ale {x y : K} (hy : y ≠ 0) :
    abs K x ≤ abs K y ↔ ValuativeRel.valuation K x ≤ ValuativeRel.valuation K y := by
  by_cases hx : x = 0
  · subst x; simp only [abs, if_pos rfl, map_zero]; exact iff_of_true (le_of_lt (apos K hy)) bot_le
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hex : e (ValuativeRel.valuation K x) ≠ 0 := by simpa [e] using hx
  have hey : e (ValuativeRel.valuation K y) ≠ 0 := by simpa [e] using hy
  simp only [abs, if_neg hx, if_neg hy]
  change (q K : ℝ) ^ WithZero.log (e (ValuativeRel.valuation K x)) ≤ (q K : ℝ) ^ WithZero.log (e (ValuativeRel.valuation K y)) ↔ _
  rw [zpow_le_zpow_iff_right₀ (q_gt K)]
  change WithZero.log (e (ValuativeRel.valuation K x)) ≤ WithZero.log (e (ValuativeRel.valuation K y)) ↔ _
  rw [← e.toOrderIso.le_iff_le]
  change WithZero.log (e (ValuativeRel.valuation K x)) ≤ WithZero.log (e (ValuativeRel.valuation K y)) ↔ e (ValuativeRel.valuation K x) ≤ e (ValuativeRel.valuation K y)
  conv_rhs => rw [← WithZero.exp_log hex, ← WithZero.exp_log hey]
  exact WithZero.exp_le_exp.symm
private lemma ainv (x : K) : abs K x⁻¹ = (abs K x)⁻¹ := by
  by_cases hx : x = 0
  · subst x; simp [abs]
  simp only [abs, if_neg hx, if_neg (inv_ne_zero hx), map_inv₀, WithZero.log_inv, zpow_neg]
private lemma azpow (d : Kˣ) (k : ℤ) : abs K (↑(d ^ k) : K) = abs K (d : K) ^ k := by
  induction k using Int.induction_on with
  | zero => simp [abs]
  | succ k ih => rw [zpow_add_one, Units.val_mul, amul, ih, zpow_add_one₀ (apos K d.ne_zero).ne']
  | pred k ih => rw [zpow_sub_one, Units.val_mul, amul, ih, Units.val_inv_eq_inv_val, ainv, zpow_sub_one₀ (apos K d.ne_zero).ne']
private lemma ball_image (d : Kˣ) :
    d • ((ValuativeRel.valuation K).integer : Set K) = {x | abs K x ≤ abs K (d : K)} := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    apply (ale K d.ne_zero).mpr
    change ValuativeRel.valuation K ((d : K) * y) ≤ _
    rw [_root_.map_mul]
    exact mul_le_of_le_one_right zero_le hy
  · intro hx
    refine ⟨(d : K)⁻¹ * x, ?_, ?_⟩
    · change ValuativeRel.valuation K ((d : K)⁻¹ * x) ≤ 1
      rw [_root_.map_mul, map_inv₀]
      exact (inv_mul_le_iff₀ (bot_lt_iff_ne_bot.mpr ((Valuation.ne_zero_iff _).mpr d.ne_zero))).mpr (by simpa using (ale K d.ne_zero).mp hx)
    · change (d : K) * ((d : K)⁻¹ * x) = x
      field_simp
private lemma exists_pi : ∃ π : ↥(ValuativeRel.valuation K).integer, Irreducible π ∧ abs K (π : K) = (q K : ℝ) ^ (-1 : ℤ) := by
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  obtain ⟨x, hx⟩ := ValuativeRel.valuation_surjective (e.symm (WithZero.exp (-1 : ℤ)))
  have he : e (ValuativeRel.valuation K x) = WithZero.exp (-1 : ℤ) := by rw [hx]; simp
  have hx0 : x ≠ 0 := by intro H; rw [H, map_zero, map_zero] at he; exact (WithZero.exp_ne_zero he.symm)
  have hxle : ValuativeRel.valuation K x ≤ 1 := by
    apply e.toOrderIso.le_iff_le.mp
    change e (ValuativeRel.valuation K x) ≤ e 1
    rw [he, map_one, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by decide)
  let π : ↥(ValuativeRel.valuation K).integer := ⟨x, hxle⟩
  have hspan : IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation K).integer = Ideal.span {π} := by
    ext y
    change y ∈ IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation K).integer ↔ y ∈ (Ideal.span {π} : Set ↥(ValuativeRel.valuation K).integer)
    rw [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe]
    change ¬IsUnit y ↔ ValuativeRel.valuation K (y : K) ≤ ValuativeRel.valuation K x
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rw [← e.toOrderIso.lt_iff_lt, ← e.toOrderIso.le_iff_le]
    change e (ValuativeRel.valuation K (y : K)) < e 1 ↔ e (ValuativeRel.valuation K (y : K)) ≤ e (ValuativeRel.valuation K x)
    rw [map_one, he]
    by_cases hy : e (ValuativeRel.valuation K (y : K)) = 0
    · rw [hy]; simp
    · rw [← WithZero.exp_log hy, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
      omega
  refine ⟨π, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal π ?_ hspan, ?_⟩
  · intro H; apply hx0; exact congrArg Subtype.val H
  · change abs K x = _
    simp only [abs, if_neg hx0]
    change (q K : ℝ) ^ WithZero.log (e (ValuativeRel.valuation K x)) = _
    rw [he, WithZero.log_exp]
private lemma mass_scale (μ : Measure K) [μ.IsAddHaarMeasure] (d : Kˣ) :
    μ {x | abs K x ≤ abs K (d : K)} = (distribHaarChar K d : ℝ≥0∞) * μ ((ValuativeRel.valuation K).integer : Set K) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  have h := Measure.measure_isAddHaarMeasure_eq_smul_of_isOpen (DomMulAct.mk d • μ) μ (Valued.isOpen_integer K)
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ d] at h
  simp only [Measure.domSMul_apply, Equiv.symm_apply_apply, ENNReal.smul_def, smul_eq_mul] at h
  change μ (d • ((ValuativeRel.valuation K).integer : Set K)) = (distribHaarChar K d : ℝ≥0∞) * μ ((ValuativeRel.valuation K).integer : Set K) at h
  rw [ball_image K] at h
  exact h
private lemma mass_pos (μ : Measure K) [μ.IsAddHaarMeasure] :
    0 < μ.real ((ValuativeRel.valuation K).integer : Set K) := by
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  exact ENNReal.toReal_pos ((Valued.isOpen_integer K).measure_ne_zero μ ⟨0, by simp⟩) (IsNonarchimedeanLocalField.isCompact_closedBall K 1).measure_lt_top.ne
private lemma pi_char (μ : Measure K) [μ.IsAddHaarMeasure]
    (π : ↥(ValuativeRel.valuation K).integer) (hπ : Irreducible π) :
    (distribHaarChar K (Units.mk0 (π : K) (by exact_mod_cast hπ.ne_zero)) : ℝ) = (q K : ℝ)⁻¹ := by
  let d : Kˣ := Units.mk0 (π : K) (by exact_mod_cast hπ.ne_zero)
  have h := uniformizer_image_measure K μ π hπ
  have hset : (fun x : K => (π : K) * x) '' ((ValuativeRel.valuation K).integer : Set K) = d • ((ValuativeRel.valuation K).integer : Set K) := rfl
  rw [hset, ball_image K, mass_scale K] at h
  have ht := congrArg ENNReal.toReal h
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_div, ENNReal.toReal_natCast] at ht
  change (distribHaarChar K d : ℝ) * μ.real ((ValuativeRel.valuation K).integer : Set K) = μ.real ((ValuativeRel.valuation K).integer : Set K) / (q K : ℝ) at ht
  apply mul_right_cancel₀ (mass_pos K μ).ne'
  simpa [div_eq_mul_inv, mul_comm] using ht
private lemma char_abs (μ : Measure K) [μ.IsAddHaarMeasure] (c : Kˣ) :
    (distribHaarChar K c : ℝ) = abs K (c : K) := by
  obtain ⟨π, hπ, ha⟩ := exists_pi K
  let d : Kˣ := Units.mk0 (π : K) (by exact_mod_cast hπ.ne_zero)
  have hd : abs K (d : K) = (q K : ℝ) ^ (-1 : ℤ) := ha
  have hc := pi_char K μ π hπ
  let k := -WithZero.log (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (ValuativeRel.valuation K (c : K)))
  have hca : abs K (c : K) = (q K : ℝ) ^ (-k) := by simp only [abs, if_neg c.ne_zero, k, neg_neg]; rfl
  have hdk : abs K (↑(d ^ k) : K) = (q K : ℝ) ^ (-k) := by rw [azpow K, hd, ← zpow_mul]; simp
  have hm := congrArg ENNReal.toReal (mass_scale K μ c)
  have hn := congrArg ENNReal.toReal (mass_scale K μ (d ^ k))
  simp only [ENNReal.toReal_mul, ENNReal.coe_toReal] at hm hn
  rw [hca] at hm
  rw [hdk, _root_.map_zpow, NNReal.coe_zpow, hc, ← zpow_neg_one, ← zpow_mul, neg_one_mul] at hn
  have H := hm.symm.trans hn
  have H' := mul_right_cancel₀ (mass_pos K μ).ne' H
  rw [hca]
  exact H'

theorem map_mul (μ : Measure K) [μ.IsAddHaarMeasure] (c : K) (hc : c ≠ 0) :
    Measure.map (fun x : K => c * x) μ =
      (ENNReal.ofReal (abs K c))⁻¹ • μ := by
  let d := Units.mk0 c hc
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI := pseudo K
  letI := sigma K
  haveI : MeasureTheory.Measure.Regular μ := inferInstance
  haveI : MeasureTheory.Measure.Regular (DomMulAct.mk d⁻¹ • μ) := inferInstance
  have h := Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk d⁻¹ • μ) μ
  rw [addHaarScalarFactor_smul_eq_distribHaarChar μ] at h
  have hchar : (distribHaarChar K d : ℝ≥0∞) = ENNReal.ofReal (abs K c) := by
    change (distribHaarChar K d : ℝ≥0∞) = ENNReal.ofReal (abs K (d : K))
    rw [← char_abs K μ d, ENNReal.ofReal_coe_nnreal]
  rw [(distribHaarChar K).map_inv] at h
  have hmap : DomMulAct.mk d⁻¹ • μ = Measure.map (fun x : K => c * x) μ := rfl
  rw [hmap] at h
  ext s
  rw [h]
  simp only [Measure.smul_apply, NNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
    ENNReal.coe_inv (ne_of_gt distribHaarChar_pos), hchar]

end DedekindZetaZeroFree.IntrinsicHaarScaling

end
