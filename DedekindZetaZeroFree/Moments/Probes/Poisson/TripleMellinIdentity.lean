module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FrequencySupport

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.PoissonIdentity

noncomputable section

open DedekindZetaZeroFree NumberField MeasureTheory PoissonKernel
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (D : FixedData S η)

def repRows : Set D.Row :=
  {u | ∃ h : u.toFrequency.u ≠ 0,
    (⟨u.toFrequency.u, h⟩ : ThetaReflectionData.Row D.recipe.A) ∈ D.recipe.probe.frequencies.reps}

def rowIntegral (u : D.Row) (Z : ℝ) : ℂ :=
  comparisonVerticalIntegral 4 (fun ξ => wzIntegral D u ξ 4 2 Z)

def rowIntegrand (u : D.Row) (Z : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  K D u ((4 : ℂ) + (t.1 : ℂ) * Complex.I) ((4 : ℂ) + (t.2.1 : ℂ) * Complex.I)
    ((2 : ℂ) + (t.2.2 : ℂ) * Complex.I) Z

theorem principalRows_inter_repRows_finite : (principalRows D ∩ repRows D).Finite := by
  apply Set.Subsingleton.finite
  intro a ha b hb
  exact ActualRowCount.principal_row_unique D ha.1 hb.1

theorem dyadRows_inter_repRows_finite (U : ℝ) : (dyadRows D U ∩ repRows D).Finite :=
  (ActualRowCount.dyadRows_finite D U).subset Set.inter_subset_left

open PoissonInitialBridge

theorem repRows_eq_univ : repRows D = Set.univ :=
  Set.eq_univ_of_forall fun u => u.isRep

def repEquiv : repRows D ≃ D.Row where
  toFun u := u.val
  invFun u := ⟨u, u.isRep⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem countable_row : Countable D.Row := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI : Countable D.recipe.A.R := by infer_instance
  exact (ActualRowCount.row_u_injective D).countable

def complementKernel (Z : ℝ) (t : ℝ × ℝ × ℝ) : ℂ :=
  ∑' i : ↥(PoissonFrequencyDecomposition.allowedIndices D)ᶜ,
    NormalizedProbe.initialTripleMellinSummand D.recipe.probe
      (Scales.xScale Z) (Scales.yScale Z) Z i.val t

theorem Iscale_eq_sum_rowIntegral (Z : ℝ) (hZ : 0 < Z) :
    (∀ u ∈ repRows D, Integrable (rowIntegrand D u Z)) ∧
    Summable (fun u : repRows D => ∫ t : ℝ × ℝ × ℝ, ‖rowIntegrand D u.val Z t‖) ∧
    (∀ u ∈ repRows D,
      rowIntegral D u Z = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, rowIntegrand D u Z t) ∧
    Summable (fun u : repRows D => rowIntegral D u.val Z) ∧
    Summable (fun i : ↥(PoissonFrequencyDecomposition.allowedIndices D)ᶜ => ∫ t : ℝ × ℝ × ℝ,
      ‖NormalizedProbe.initialTripleMellinSummand D.recipe.probe
        (Scales.xScale Z) (Scales.yScale Z) Z i.val t‖) ∧
    Integrable (complementKernel D Z) ∧
    PoissonFrequencyDecomposition.omittedSum D Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, complementKernel D Z t ∧
    D.Iscale Z = (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
      (∫ t : ℝ × ℝ × ℝ, ∑' u : repRows D, rowIntegrand D u.val Z t) +
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, complementKernel D Z t ∧
    D.Iscale Z = ∑' u : repRows D, rowIntegral D u.val Z +
      PoissonFrequencyDecomposition.omittedSum D Z := by
  letI := countable_row D
  obtain ⟨hint0, hnorm0, h30, hsumrow0, hcn, _, hci, homit, hsplit0⟩ :=
    PoissonFrequencyDecomposition.Iscale_eq_rows_add_omitted D Z hZ
  have hint : ∀ u : D.Row, Integrable (rowIntegrand D u Z) := fun u => hint0 u
  have hnorm : Summable (fun u : D.Row => ∫ t : ℝ × ℝ × ℝ, ‖rowIntegrand D u Z t‖) := hnorm0
  have h3 : ∀ u : D.Row, rowIntegral D u Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, rowIntegrand D u Z t := fun u => h30 u
  have hsumrow : Summable (fun u : D.Row => rowIntegral D u Z) := hsumrow0
  have hsplit : D.Iscale Z = ∑' u : D.Row, rowIntegral D u Z +
      PoissonFrequencyDecomposition.omittedSum D Z := hsplit0
  have hci' : Integrable (complementKernel D Z) := hci
  have homit' : PoissonFrequencyDecomposition.omittedSum D Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, complementKernel D Z t := homit
  have hI := integral_tsum_of_summable_integral_norm
    (F := fun (u : D.Row) (t : ℝ × ℝ × ℝ) => rowIntegrand D u Z t) hint hnorm
  have hsumInt : ∑' u : D.Row, rowIntegral D u Z =
      (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, ∑' u : D.Row, rowIntegrand D u Z t := by
    calc ∑' u : D.Row, rowIntegral D u Z
        = ∑' u : D.Row, (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, rowIntegrand D u Z t :=
          tsum_congr h3
      _ = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∑' u : D.Row, ∫ t : ℝ × ℝ × ℝ, rowIntegrand D u Z t :=
          tsum_mul_left
      _ = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, ∑' u : D.Row, rowIntegrand D u Z t :=
          congrArg (fun x => (2 * (Real.pi : ℂ))⁻¹ ^ 3 * x) hI
  have hrepI : ∀ t : ℝ × ℝ × ℝ, ∑' u : repRows D, rowIntegrand D u.val Z t =
      ∑' u : D.Row, rowIntegrand D u Z t :=
    fun t => (repEquiv D).tsum_eq (fun u => rowIntegrand D u Z t)
  have hrepR : ∑' u : repRows D, rowIntegral D u.val Z = ∑' u : D.Row, rowIntegral D u Z :=
    (repEquiv D).tsum_eq (fun u => rowIntegral D u Z)
  refine ⟨fun u _ => hint u, (Equiv.summable_iff (repEquiv D)).mpr hnorm,
    fun u _ => h3 u, (Equiv.summable_iff (repEquiv D)).mpr hsumrow, hcn, hci', homit', ?_, ?_⟩
  · calc D.Iscale Z = ∑' u : D.Row, rowIntegral D u Z +
          PoissonFrequencyDecomposition.omittedSum D Z := hsplit
      _ = (2 * (Real.pi : ℂ))⁻¹ ^ 3 * (∫ t : ℝ × ℝ × ℝ, ∑' u : D.Row, rowIntegrand D u Z t) +
          (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, complementKernel D Z t := by
          exact congrArg₂ (· + ·) hsumInt homit'
      _ = (2 * (Real.pi : ℂ))⁻¹ ^ 3 *
          (∫ t : ℝ × ℝ × ℝ, ∑' u : repRows D, rowIntegrand D u.val Z t) +
          (2 * (Real.pi : ℂ))⁻¹ ^ 3 * ∫ t : ℝ × ℝ × ℝ, complementKernel D Z t := by
          simp only [hrepI]
  · rw [hrepR]
    exact hsplit

theorem Iscale_eq_principal_add_nonprincipal (Z : ℝ) (hZ : 0 < Z) :
    D.Iscale Z = J D (principalRows D ∩ repRows D) 4 4 2 Z +
      ∑' u : (repRows D \ principalRows D : Set D.Row), rowIntegral D u.val Z +
      PoissonFrequencyDecomposition.omittedSum D Z := by
  obtain ⟨_, _, _, hsumrow, _, _, _, _, h7⟩ := Iscale_eq_sum_rowIntegral D Z hZ
  have hsum : Summable (fun u : D.Row => rowIntegral D u Z) :=
    (Equiv.summable_iff (repEquiv D)).mp hsumrow
  have hpr : principalRows D = {ActualRowCount.principalRow D} := by
    ext r
    exact ActualRowCount.u_eq_one_iff D
  have hJ : J D (principalRows D ∩ repRows D) 4 4 2 Z =
      rowIntegral D (ActualRowCount.principalRow D) Z := by
    rw [repRows_eq_univ, Set.inter_univ, hpr]
    unfold J
    rw [finsum_mem_singleton]
    rfl
  have hset : (repRows D \ principalRows D : Set D.Row) =
      ({ActualRowCount.principalRow D} : Set D.Row)ᶜ := by
    rw [repRows_eq_univ, hpr, Set.compl_eq_univ_diff]
  have hnp : ∑' u : (repRows D \ principalRows D : Set D.Row), rowIntegral D u.val Z =
      ∑' u : D.Row, if u = ActualRowCount.principalRow D then 0 else rowIntegral D u Z := by
    rw [hset]
    refine (tsum_subtype (({ActualRowCount.principalRow D} : Set D.Row)ᶜ)
      (fun u => rowIntegral D u Z)).trans (tsum_congr fun u => ?_)
    by_cases h : u = ActualRowCount.principalRow D
    · simp [Set.indicator_apply, h]
    · simp [Set.indicator_apply, h]
  have hrep : ∑' u : repRows D, rowIntegral D u.val Z = ∑' u : D.Row, rowIntegral D u Z :=
    (repEquiv D).tsum_eq (fun u => rowIntegral D u Z)
  rw [h7, hrep, hJ, hnp]
  exact congrArg (fun x => x + PoissonFrequencyDecomposition.omittedSum D Z)
    (hsum.tsum_eq_add_tsum_ite (ActualRowCount.principalRow D))

private def Tset (k : ℕ) : Set D.Row :=
  (dyadRows D ((2 : ℝ) ^ k) ∩ repRows D) \ principalRows D

private theorem dyad_unique {q : ℝ} {j k : ℕ} (hj1 : (2 : ℝ) ^ j ≤ q) (hj2 : q < 2 * 2 ^ j)
    (hk1 : (2 : ℝ) ^ k ≤ q) (hk2 : q < 2 * 2 ^ k) : j = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : (2 : ℝ) ^ (j + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) h
    rw [pow_succ] at h'
    linarith
  · have h' : (2 : ℝ) ^ (k + 1) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) h
    rw [pow_succ] at h'
    linarith

theorem nonprincipal_eq_sum_dyads (Z : ℝ) (hZ : 0 < Z) :
    Summable (fun k : ℕ =>
      J D ((dyadRows D ((2 : ℝ) ^ k) ∩ repRows D) \ principalRows D) 4 4 2 Z) ∧
    ∑' u : (repRows D \ principalRows D : Set D.Row), rowIntegral D u.val Z =
      ∑' k : ℕ, J D ((dyadRows D ((2 : ℝ) ^ k) ∩ repRows D) \ principalRows D) 4 4 2 Z := by
  obtain ⟨_, _, _, hsumrow, _, _, _, _, _⟩ := Iscale_eq_sum_rowIntegral D Z hZ
  have hsum : Summable (fun u : D.Row => rowIntegral D u Z) :=
    (Equiv.summable_iff (repEquiv D)).mp hsumrow
  have hTfin : ∀ k, (Tset D k).Finite := fun k =>
    ((ActualRowCount.dyadRows_finite D ((2 : ℝ) ^ k)).subset
      (fun x hx => hx.1.1))
  let φ : (Σ k : ℕ, ↥(Tset D k)) → D.Row := fun p => p.2.val
  have hφinj : Function.Injective φ := by
    rintro ⟨k, x, hx⟩ ⟨k', x', hx'⟩ h
    have h' : x = x' := h
    subst h'
    have hk : k = k' := dyad_unique hx.1.1.1 hx.1.1.2 hx'.1.1.1 hx'.1.1.2
    subst hk
    rfl
  have hrange : Set.range φ = (repRows D \ principalRows D : Set D.Row) := by
    ext r
    constructor
    · rintro ⟨⟨k, x, hx⟩, rfl⟩
      exact ⟨hx.1.2, hx.2⟩
    · rintro ⟨hr1, hr2⟩
      obtain ⟨k, hk⟩ := ActualRowCount.exists_dyad D r
      exact ⟨⟨k, r, ⟨⟨hk, hr1⟩, hr2⟩⟩, rfl⟩
  have hg : Summable (fun p : (Σ k : ℕ, ↥(Tset D k)) => rowIntegral D (φ p) Z) :=
    hsum.comp_injective hφinj
  have hfib : ∀ k, ∑' c : ↥(Tset D k), rowIntegral D c.val Z =
      J D ((dyadRows D ((2 : ℝ) ^ k) ∩ repRows D) \ principalRows D) 4 4 2 Z := by
    intro k
    have hf := hTfin k
    have hJdef : J D (Tset D k) 4 4 2 Z = ∑ᶠ u ∈ Tset D k, rowIntegral D u Z := rfl
    show _ = J D (Tset D k) 4 4 2 Z
    rw [hJdef, finsum_mem_def]
    refine (tsum_subtype (Tset D k) (fun u => rowIntegral D u Z)).trans ?_
    exact tsum_eq_finsum (hf.subset (Set.support_indicator_subset))
  have hfun : (fun k : ℕ => ∑' c : ↥(Tset D k), rowIntegral D c.val Z) =
      fun k : ℕ => J D ((dyadRows D ((2 : ℝ) ^ k) ∩ repRows D) \ principalRows D) 4 4 2 Z :=
    funext hfib
  refine ⟨?_, ?_⟩
  · rw [← hfun]
    exact hg.sigma
  · rw [← hrange, tsum_range (fun u => rowIntegral D u Z) hφinj, hg.tsum_sigma, ← hfun]

end

end DedekindZetaZeroFree.Quantitative.PoissonIdentity
