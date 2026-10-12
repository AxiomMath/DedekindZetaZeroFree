module

public import DedekindZetaZeroFree.Moments.Reflected.BalancedThetaRowFiniteFibers
public import DedekindZetaZeroFree.ZeroDetection.Conductors.BalancedIdealSections
public import DedekindZetaZeroFree.Moments.Reflected.DyadicWeightBounds
public import DedekindZetaZeroFree.Analysis.LogarithmicPowerBounds

@[expose] public section

namespace DedekindZetaZeroFree
noncomputable section
open scoped NumberField Classical Pointwise

namespace ActualRowTransfer
variable {F : Type} [Field F] [NumberField F]

def rowIdeal (A : SArithmeticData F) (m : ThetaReflectionData.Row A) : A.Exterior :=
  A.exteriorIdealEquiv.symm ⟨Ideal.span {m.val}, by
    exact fun h => m.property (Ideal.span_singleton_eq_bot.mp h)⟩

def canonicalRow (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (u : A.Rˣ) (I : A.Exterior) : ThetaReflectionData.Row A :=
  ⟨(u : A.R) * D.generator I, mul_ne_zero u.ne_zero (D.generates I).1⟩

theorem span_rowIdeal (A : SArithmeticData F) (m : ThetaReflectionData.Row A) :
    Ideal.span {m.val} = A.extendIdeal (rowIdeal A m) := by
  have h : A.exteriorIdealEquiv (rowIdeal A m) =
      ⟨Ideal.span {m.val}, fun hh => m.property (Ideal.span_singleton_eq_bot.mp hh)⟩ := by
    rw [rowIdeal]
    exact Equiv.apply_symm_apply A.exteriorIdealEquiv _
  have h' : A.extendIdeal (rowIdeal A m) = Ideal.span {m.val} := by
    rw [← A.exteriorIdealEquiv_apply (rowIdeal A m)]
    exact congrArg Subtype.val h
  exact h'.symm

theorem exists_unit_mul_generator (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (m : ThetaReflectionData.Row A) :
    ∃ ε : A.Rˣ, m.val = (ε : A.R) * D.generator (rowIdeal A m) := by
  have hspan : Ideal.span {m.val} = Ideal.span {D.generator (rowIdeal A m)} := by
    rw [span_rowIdeal A m, (D.generates (rowIdeal A m)).2]
  obtain ⟨ε, hε⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  have hε' : (↑ε : A.R) * m.val = D.generator (rowIdeal A m) := by rw [mul_comm, hε]
  refine ⟨ε⁻¹, ?_⟩
  rw [← hε', ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

def dyadicRow (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (u : A.Rˣ) (h d : A.Exterior) : ThetaReflectionData.Row A :=
  ⟨(u : A.R) * D.generator h * D.generator d,
    mul_ne_zero (mul_ne_zero u.ne_zero (D.generates h).1) (D.generates d).1⟩

def UnitRepresentatives (A : SArithmeticData F) (U : Finset A.Rˣ) : Prop :=
  ∀ v : A.Rˣ, ∃! u : {u : A.Rˣ // u ∈ U}, ∃ w : A.Rˣ, v = u.val * w ^ 6

def AllowedSection (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (L : Subgroup A.V) : Prop :=
  ∀ I, A.IsAllowed L (ThetaReflectionData.rowUnit A
    ⟨D.generator I, (D.generates I).1⟩)

def idealUnitMass (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (U : Finset A.Rˣ) (X Z : ℝ) : ℝ :=
  ∑ u ∈ U, ∑' I : A.Exterior,
    if A.exteriorNorm I ≤ X then
      ‖ThetaReflectionData.forwardB A D (canonicalRow A D u I) Z‖ ^ 2 else 0

def DyadicBound (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (U : Finset A.Rˣ) (M Cstar : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 < K ∧
    ∀ Z P Q : ℝ, 1 ≤ Z → 1 ≤ P → 1 ≤ Q → P * Q ≤ Cstar * Z ^ M →
      ∀ u ∈ U,
        (∑' h : A.Exterior, ∑' d : A.Exterior,
          if Powerful h.val ∧ Squarefree d.val ∧ h.val ⊔ d.val = ⊤ ∧
              P ≤ A.exteriorNorm h ∧ A.exteriorNorm h < 2 * P ∧
              Q ≤ A.exteriorNorm d ∧ A.exteriorNorm d < 2 * Q then
            ‖ThetaReflectionData.forwardB A D (dyadicRow A D u h d) Z‖ ^ 2 else 0) ≤
          K * Z ^ δ * Real.sqrt P * (Q + Q ^ 2 * P / Z)

def rowShape (A : SArithmeticData F) (m : ThetaReflectionData.Row A) : A.G :=
  A.diagonal (ThetaReflectionData.rowUnit A m) /
    A.radialSection (A.exteriorNorm (rowIdeal A m))
      (A.exteriorNorm_pos (rowIdeal A m))

private theorem additive_continuous (A : SArithmeticData F) : Continuous A.localToAdditive := by
  unfold SArithmeticData.localToAdditive
  apply Continuous.prodMk <;> apply continuous_pi
  · intro w
    exact Units.continuous_val.comp ((continuous_apply w).comp continuous_fst)
  · intro v
    exact Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)
private theorem additive_diag (A : SArithmeticData F) (u : Fˣ) :
    A.localToAdditive (A.diagonal u) = sLocalDiagonal F A.Sf (u : F) := by
  ext w <;> rfl
private theorem same_ideal_unit (A : SArithmeticData F) (m n : ThetaReflectionData.Row A)
    (he : rowIdeal A m = rowIdeal A n) : ∃ v : A.Rˣ, m.val = v * n.val := by
  have hspan : Ideal.span {m.val} = Ideal.span {n.val} := by
    have h := congrArg (fun I => (A.exteriorIdealEquiv I).val) he
    simpa [rowIdeal] using h
  obtain ⟨v, hv⟩ := (Ideal.span_singleton_eq_span_singleton.mp hspan).symm
  exact ⟨v, by simpa only [mul_comm] using hv.symm⟩

theorem compactShape_idealFiber_bound (A : SArithmeticData F)
    (K : Set A.G) (hK : IsCompact K) :
    ∃ k₀ : ℕ, ∀ (rows : Finset (ThetaReflectionData.Row A)),
      (∀ m ∈ rows, rowShape A m ∈ K) → ∀ I : A.Exterior,
        (rows.filter (fun m => rowIdeal A m = I)).card ≤ k₀ := by
  classical
  let T := A.localToAdditive '' (K / K)
  have hKK : IsCompact (K / K) := by
    rw [← Set.image_div_prod]
    exact (hK.prod hK).image (continuous_fst.div' continuous_snd)
  have hT : IsCompact T := hKK.image (additive_continuous A)
  have hd : ProbeAdditive.balancedDilation F A.Sf 1 = 1 := by
    rw [← A.localToAdditive_radialSection 1 (by norm_num), A.radialSection_one]
    rfl
  have hf : {v : A.R | sLocalDiagonal F A.Sf (v : F) ∈ T}.Finite := by
    have h := probe_additive_box_rows_finite F A.Sf 1 T hT
    simpa only [ProbeAdditive.boxRows, hd, one_mul, Set.image_id'] using h
  let candidates := hf.toFinset
  refine ⟨candidates.card, ?_⟩
  intro rows hrows I
  let fs := rows.filter (fun m => rowIdeal A m = I)
  by_cases hn : fs.Nonempty
  · obtain ⟨n, hn⟩ := hn
    have hunit (m : fs) : ∃ v : A.Rˣ, m.val.val = v * n.val := by
      apply same_ideal_unit A
      exact (Finset.mem_filter.mp m.property).2.trans (Finset.mem_filter.mp hn).2.symm
    let v : fs → A.Rˣ := fun m => (hunit m).choose
    have hv (m : fs) : m.val.val = v m * n.val := (hunit m).choose_spec
    have hnorm (m : fs) : rowIdeal A m.val = rowIdeal A n :=
      (Finset.mem_filter.mp m.property).2.trans (Finset.mem_filter.mp hn).2.symm
    have hshape (m : fs) : A.diagonal (ThetaReflectionData.rowUnit A m.val) /
        A.diagonal (ThetaReflectionData.rowUnit A n) ∈ K / K := by
      have he : rowShape A m.val / rowShape A n =
          A.diagonal (ThetaReflectionData.rowUnit A m.val) /
            A.diagonal (ThetaReflectionData.rowUnit A n) := by
        unfold rowShape
        simp only [hnorm]
        exact div_div_div_cancel_right _ _ _
      rw [← he]
      exact Set.div_mem_div (hrows _ (Finset.mem_filter.mp m.property).1)
        (hrows _ (Finset.mem_filter.mp hn).1)
    have hc (m : fs) : (v m : A.R) ∈ candidates := by
      apply hf.mem_toFinset.mpr
      change sLocalDiagonal F A.Sf (((v m : A.R) : F)) ∈ T
      have he : ThetaReflectionData.rowUnit A m.val /
          ThetaReflectionData.rowUnit A n = Units.map (algebraMap A.R F).toMonoidHom (v m) := by
        apply Units.ext
        simp only [Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe,
          ThetaReflectionData.rowUnit, Units.val_mk0]
        change (m.val.val : F) / (n.val : F) = (((v m : A.R) : F))
        have h := congrArg (fun r : A.R => (r : F)) (hv m)
        change (m.val.val : F) = (((v m : A.R) : F)) * (n.val : F) at h
        rw [h]
        exact mul_div_cancel_right₀ _ (ThetaReflectionData.rowUnit A n).ne_zero
      refine ⟨A.diagonal (ThetaReflectionData.rowUnit A m.val) /
        A.diagonal (ThetaReflectionData.rowUnit A n), hshape m, ?_⟩
      rw [← map_div, he, additive_diag]
      rfl
    let f : fs → candidates := fun m => ⟨(v m : A.R), hc m⟩
    have hinj : Function.Injective f := by
      intro m₁ m₂ he
      have he' : (v m₁ : A.R) = (v m₂ : A.R) := congrArg Subtype.val he
      apply Subtype.ext
      apply Subtype.ext
      rw [hv m₁, hv m₂, he']
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj
  · change fs.card ≤ candidates.card
    rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    exact Nat.zero_le _

def InCanonicalFiber (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (u : A.Rˣ) (I : A.Exterior) (m : ThetaReflectionData.Row A) : Prop :=
  ∃ w : A.Rˣ, m = ThetaReflectionData.sixthTranslate A w (canonicalRow A D u I)

private theorem rowIdeal_canonical (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (u : A.Rˣ) (I : A.Exterior) :
    rowIdeal A (canonicalRow A D u I) = I := by
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  simp only [rowIdeal, Equiv.apply_symm_apply, canonicalRow]
  rw [Ideal.span_singleton_mul_left_unit u.isUnit, A.exteriorIdealEquiv_apply]
  exact (D.generates I).2

private theorem rowIdeal_sixth (A : SArithmeticData F) (w : A.Rˣ)
    (m : ThetaReflectionData.Row A) :
    rowIdeal A (ThetaReflectionData.sixthTranslate A w m) = rowIdeal A m := by
  unfold rowIdeal
  congr 1
  apply Subtype.ext
  exact Ideal.span_singleton_mul_left_unit (w.isUnit.pow 6) m.val

private theorem fiber_ideal (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (u : A.Rˣ) (I : A.Exterior)
    (m : ThetaReflectionData.Row A) (hm : InCanonicalFiber A D u I m) :
    rowIdeal A m = I := by
  obtain ⟨w, rfl⟩ := hm
  rw [rowIdeal_sixth, rowIdeal_canonical]

private theorem exists_fiber (A : SArithmeticData F)
    (D : ComparisonPoissonCoefficientData F A) (U : Finset A.Rˣ)
    (hU : UnitRepresentatives A U) (m : ThetaReflectionData.Row A) :
    ∃ u ∈ U, InCanonicalFiber A D u (rowIdeal A m) m := by
  have hspan : Ideal.span {m.val} = Ideal.span {D.generator (rowIdeal A m)} := by
    rw [(D.generates _).2, ← A.exteriorIdealEquiv_apply]
    simp [rowIdeal]
  obtain ⟨v, hv⟩ := (Ideal.span_singleton_eq_span_singleton.mp hspan).symm
  obtain ⟨u, ⟨w, hw⟩, _⟩ := hU v
  refine ⟨u.val, u.property, w, ?_⟩
  apply Subtype.ext
  change m.val = (w : A.R) ^ 6 * ((u.val : A.R) * D.generator (rowIdeal A m))
  rw [← hv, hw]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val]
  ring

private theorem boundedIdeals_finite (A : SArithmeticData F) (X : ℝ) :
    {I : A.Exterior | A.exteriorNorm I ≤ X}.Finite := by
  exact ((normBoundedIdeals_finite F X).preimage
    (f := fun I : A.Exterior => (⟨I.val, I.property.1⟩ : NonzeroIdeal F))
    (by intro I _ J _ h; apply Subtype.ext; exact congrArg (fun x : NonzeroIdeal F => x.val) h)).subset
    (by intro I hI; exact hI)

theorem multisetMass_le_idealUnitMass
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (hchar : ThetaReflectionData.SixthUnitCharacterCompatibility A D)
    (U : Finset A.Rˣ) (hU : UnitRepresentatives A U)
    (rows : Multiset (ThetaReflectionData.Row A)) (X Z : ℝ) (k₀ : ℕ)
    (hrows : ∀ m ∈ rows, A.exteriorNorm (rowIdeal A m) ≤ X)
    (hfiber : ∀ u ∈ U, ∀ I : A.Exterior,
      (rows.filter (InCanonicalFiber A D u I)).card ≤ k₀) :
    (rows.map (fun m => ‖ThetaReflectionData.forwardB A D m Z‖ ^ 2)).sum ≤
      (k₀ : ℝ) * idealUnitMass A D U X Z := by
  classical
  let ideals := (boundedIdeals_finite A X).toFinset
  let index : ThetaReflectionData.Row A → A.Rˣ × A.Exterior :=
    fun m => ((exists_fiber A D U hU m).choose, rowIdeal A m)
  have hidx (m : ThetaReflectionData.Row A) :
      (index m).1 ∈ U ∧ InCanonicalFiber A D (index m).1 (index m).2 m :=
    (exists_fiber A D U hU m).choose_spec
  have hm := balancedRow_finiteFiber_norm_sq_le rows (U ×ˢ ideals) index
    (fun m => ThetaReflectionData.forwardB A D m Z)
    (fun i => ThetaReflectionData.forwardB A D (canonicalRow A D i.1 i.2) Z)
    k₀ (by
      intro m hm
      exact Finset.mem_product.mpr ⟨(hidx m).1, by
        simpa [ideals, index] using hrows m hm⟩) (by
      intro i hi
      apply le_trans (Multiset.card_le_card ?_) (hfiber i.1 (Finset.mem_product.mp hi).1 i.2)
      letI : DecidablePred (fun x => index x = i) := fun _ => Classical.propDecidable _
      exact Multiset.monotone_filter_right rows
        (p := fun x => index x = i) (q := InCanonicalFiber A D i.1 i.2)
        (fun m he => by simpa [he] using (hidx m).2)) (by
      intro m _
      obtain ⟨w, hw⟩ := (hidx m).2
      exact (congrArg (fun r => ThetaReflectionData.forwardB A D r Z) hw).trans
        (ThetaReflectionData.forwardB_sixthTranslate A D hchar w _ Z))
  convert hm using 1
  congr 1
  unfold idealUnitMass
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro u hu
  rw [tsum_eq_sum (s := ideals)]
  · apply Finset.sum_congr rfl
    intro I hI
    simp only [ideals, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hI
    simp [hI]
  · intro I hI
    have hnot : ¬ A.exteriorNorm I ≤ X := by
      simpa [ideals] using hI
    simp [hnot]

theorem idealUnitMass_bound_of_dyadic
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (L : Subgroup A.V) (hL : A.IsSUnitIsotropicComplement H L)
    (hgen : AllowedSection A D L)
    (hchar : ThetaReflectionData.SixthUnitCharacterCompatibility A D)
    (U : Finset A.Rˣ) (hU : UnitRepresentatives A U)
    (M Cstar ε : ℝ) (hM : 1 < M) (hCstar : 0 < Cstar) (hε : 0 < ε)
    (hdyadic : DyadicBound A D U M Cstar) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℝ, 1 ≤ Z →
      idealUnitMass A D U (Cstar * Z ^ M) Z ≤ K * Z ^ (2 * M - 1 + ε) := by
  classical
  obtain ⟨B, hB, hBdyad⟩ := hdyadic (ε / 2) (by positivity)
  obtain ⟨T, hT, hweights⟩ := RepresentationTheory.ActualRowTransfer.sum_dyad_weights_bound
    M Cstar hM.le hCstar
  obtain ⟨C, hC, hlog⟩ := RepresentationTheory.ActualRowTransfer.log_square_le_rpow
    (ε / 2) (by positivity)
  refine ⟨((U.card : ℝ) + 1) * B * T * C, by positivity, ?_⟩
  intro Z hZ
  have hZpos : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  let indices := RepresentationTheory.ActualRowTransfer.dyadIndices (Cstar * Z ^ M)
  let weight : ℕ × ℕ → ℝ := fun pq => Real.sqrt ((2 : ℝ) ^ pq.1) *
    ((2 : ℝ) ^ pq.2 + ((2 : ℝ) ^ pq.2) ^ 2 * (2 : ℝ) ^ pq.1 / Z)
  have hlocal (u : A.Rˣ) (hu : u ∈ U) :
      (∑ pq ∈ indices, RepresentationTheory.ActualRowTransfer.rawDyadMass A D u Z pq.1 pq.2) ≤
        B * Z ^ (ε / 2) * (T * Z ^ (2 * M - 1) * (1 + Real.log Z) ^ 2) := by
    calc
      _ ≤ ∑ pq ∈ indices, B * Z ^ (ε / 2) * weight pq := by
        apply Finset.sum_le_sum
        intro pq hpq
        have hrange : (2 : ℝ) ^ pq.1 * (2 : ℝ) ^ pq.2 ≤ Cstar * Z ^ M :=
          (Finset.mem_filter.mp hpq).2
        simpa [RepresentationTheory.ActualRowTransfer.rawDyadMass, dyadicRow, weight, mul_assoc]
          using hBdyad Z ((2 : ℝ) ^ pq.1) ((2 : ℝ) ^ pq.2) hZ
            (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num)) hrange u hu
      _ = B * Z ^ (ε / 2) * (∑ pq ∈ indices, weight pq) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ B * Z ^ (ε / 2) *
          (T * Z ^ (2 * M - 1) * (1 + Real.log Z) ^ 2) := by
        apply mul_le_mul_of_nonneg_left (hweights Z hZ)
        positivity
  have hcover := RepresentationTheory.ActualRowTransfer.canonical_mass_le_sum_dyads
    A D hCl H L hL hgen hchar U (Cstar * Z ^ M) Z (by positivity)
  change idealUnitMass A D U (Cstar * Z ^ M) Z ≤
    ∑ u ∈ U, ∑ pq ∈ indices, RepresentationTheory.ActualRowTransfer.rawDyadMass A D u Z pq.1 pq.2
    at hcover
  calc
    idealUnitMass A D U (Cstar * Z ^ M) Z ≤
        ∑ u ∈ U, ∑ pq ∈ indices,
          RepresentationTheory.ActualRowTransfer.rawDyadMass A D u Z pq.1 pq.2 := hcover
    _ ≤ ∑ u ∈ U, B * Z ^ (ε / 2) *
        (T * Z ^ (2 * M - 1) * (1 + Real.log Z) ^ 2) :=
      Finset.sum_le_sum hlocal
    _ = (U.card : ℝ) * B * Z ^ (ε / 2) * T * Z ^ (2 * M - 1) *
        (1 + Real.log Z) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ (U.card : ℝ) * B * Z ^ (ε / 2) * T * Z ^ (2 * M - 1) *
        (C * Z ^ (ε / 2)) := by
      apply mul_le_mul_of_nonneg_left (hlog Z hZ)
      positivity
    _ = (U.card : ℝ) * B * T * C * Z ^ (2 * M - 1 + ε) := by
      rw [show 2 * M - 1 + ε = ε / 2 + (2 * M - 1) + ε / 2 by ring,
        Real.rpow_add hZpos, Real.rpow_add hZpos]
      ring
    _ ≤ ((U.card : ℝ) + 1) * B * T * C * Z ^ (2 * M - 1 + ε) := by
      gcongr
      exact le_add_of_nonneg_right zero_le_one

theorem balancedRowMass_bound_of_dyadic
    (A : SArithmeticData F) (D : ComparisonPoissonCoefficientData F A)
    (hCl : Subsingleton (ClassGroup A.R)) (H : A.V → A.V → Fˣ)
    (L : Subgroup A.V) (hL : A.IsSUnitIsotropicComplement H L)
    (hgen : AllowedSection A D L)
    (hchar : ThetaReflectionData.SixthUnitCharacterCompatibility A D)
    (U : Finset A.Rˣ) (hU : UnitRepresentatives A U)
    (Kshape : Set A.G) (hKshape : IsCompact Kshape)
    (M Cstar ε : ℝ) (hM : 1 < M) (hCstar : 0 < Cstar) (hε : 0 < ε)
    (hdyadic : DyadicBound A D U M Cstar) :
    ∃ K : ℝ, 0 < K ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ rows : Finset (ThetaReflectionData.Row A),
        (∀ m ∈ rows, rowShape A m ∈ Kshape ∧
          A.exteriorNorm (rowIdeal A m) ≤ Cstar * Z ^ M) →
        (∑ m ∈ rows, ‖ThetaReflectionData.forwardB A D m Z‖ ^ 2) ≤
          K * Z ^ (2 * M - 1 + ε) := by
  classical
  obtain ⟨k₀, hk₀⟩ := compactShape_idealFiber_bound A Kshape hKshape
  obtain ⟨C, hC, hbound⟩ := idealUnitMass_bound_of_dyadic A D hCl H L hL
    hgen hchar U hU M Cstar ε hM hCstar hε hdyadic
  refine ⟨((k₀ : ℝ) + 1) * C, by positivity, ?_⟩
  intro Z hZ rows hrows
  have hfiber : ∀ u ∈ U, ∀ I : A.Exterior,
      (rows.val.filter (InCanonicalFiber A D u I)).card ≤ k₀ + 1 := by
    intro u _ I
    apply le_trans (Multiset.card_le_card ?_) ((hk₀ rows
      (fun m hm => (hrows m hm).1) I).trans (Nat.le_succ k₀))
    change rows.val.filter (InCanonicalFiber A D u I) ≤
      rows.val.filter (fun m => rowIdeal A m = I)
    exact Multiset.monotone_filter_right rows.val
      (fun m hm => fiber_ideal A D u I m hm)
  have hmass := multisetMass_le_idealUnitMass A D hchar U hU rows.val
    (Cstar * Z ^ M) Z (k₀ + 1)
    (fun m hm => (hrows m hm).2) hfiber
  have hmul := mul_le_mul_of_nonneg_left (hbound Z hZ)
    (Nat.cast_nonneg (α := ℝ) (k₀ + 1))
  calc
    (∑ m ∈ rows, ‖ThetaReflectionData.forwardB A D m Z‖ ^ 2) =
        (rows.val.map (fun m => ‖ThetaReflectionData.forwardB A D m Z‖ ^ 2)).sum := rfl
    _ ≤ ((k₀ + 1 : ℕ) : ℝ) * idealUnitMass A D U (Cstar * Z ^ M) Z := hmass
    _ ≤ ((k₀ + 1 : ℕ) : ℝ) * (C * Z ^ (2 * M - 1 + ε)) := hmul
    _ = ((k₀ : ℝ) + 1) * C * Z ^ (2 * M - 1 + ε) := by
      push_cast
      ring

end ActualRowTransfer
end
end DedekindZetaZeroFree
