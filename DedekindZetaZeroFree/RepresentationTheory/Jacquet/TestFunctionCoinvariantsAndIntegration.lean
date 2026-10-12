module

public import DedekindZetaZeroFree.HarmonicAnalysis.Schwartz.LocalCosetExpansions

@[expose] public section

noncomputable section

set_option maxHeartbeats 400000

namespace DedekindZetaZeroFree.KPJacquetOpenTestFunction

open MeasureTheory KPJacquetStepFunction

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def translation (y : K) : CcLC K E →ₗ[ℂ] CcLC K E where
  toFun φ := ⟨LocallyConstant.comap ⟨fun x => x + y, continuous_id.add continuous_const⟩ φ.val,
    by exact φ.property.comp_homeomorph (Homeomorph.addRight y)⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

@[simp] theorem value_translation (y : K) (φ : CcLC K E) (x : K) :
    value (translation y φ) x = value φ (x + y) := rfl

def translationRepresentation : Representation ℂ (Multiplicative K) (CcLC K E) where
  toFun y := translation (Multiplicative.toAdd y)
  map_one' := by
    ext φ x
    simp [translation, LocallyConstant.comap]
  map_mul' := by
    intro x y
    ext φ z
    simp [translation, LocallyConstant.comap, add_assoc, add_comm, add_left_comm]

def translationRelations (ψ : Multiplicative K →* ℂˣ) : Submodule ℂ (CcLC K E) :=
  rootRelationSpan translationRepresentation (MonoidHom.id (Multiplicative K)) ψ

theorem translationRelations_eq_span (ψ : Multiplicative K →* ℂˣ) :
    translationRelations (E := E) ψ = Submodule.span ℂ
      (Set.range fun p : K × CcLC K E =>
        translation p.1 p.2 - (ψ (Multiplicative.ofAdd p.1) : ℂ) • p.2) := by
  unfold translationRelations rootRelationSpan
  apply congrArg (Submodule.span ℂ)
  ext f
  constructor
  · rintro ⟨⟨y, φ⟩, rfl⟩
    exact ⟨(Multiplicative.toAdd y, φ), rfl⟩
  · rintro ⟨⟨y, φ⟩, rfl⟩
    exact ⟨(Multiplicative.ofAdd y, φ), rfl⟩

abbrev TranslationCoinvariants (ψ : Multiplicative K →* ℂˣ) :=
  RootCoinvariants (translationRepresentation (K := K) (E := E))
    (MonoidHom.id (Multiplicative K)) ψ

abbrev OrdinaryTranslationCoinvariants (K E : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [AddCommGroup E] [Module ℂ E] :=
  TranslationCoinvariants (E := E) (1 : Multiplicative K →* ℂˣ)

def coinvariantsMk (ψ : Multiplicative K →* ℂˣ) :
    CcLC K E →ₗ[ℂ] TranslationCoinvariants (E := E) ψ :=
  rootCoinvariantsMk (translationRepresentation (K := K) (E := E))
    (MonoidHom.id (Multiplicative K)) ψ

def compactOpenBump (H : AddSubgroup K) (hHopen : IsOpen (H : Set K))
    (hHcompact : IsCompact (H : Set K)) (e : E) : CcLC K E :=
  ⟨(LocallyConstant.const K e).indicator ⟨H.isClosed_of_isOpen hHopen, hHopen⟩, by
    apply HasCompactSupport.of_support_subset_isCompact hHcompact
    intro x hx
    by_contra hn
    exact hx (Set.indicator_of_notMem hn _)⟩

@[simp] theorem value_compactOpenBump (H : AddSubgroup K)
    (hHopen : IsOpen (H : Set K)) (hHcompact : IsCompact (H : Set K))
    (e : E) (x : K) :
    value (compactOpenBump H hHopen hHcompact e) x =
      (H : Set K).indicator (fun _ => e) x := rfl

section Integration

variable [MeasurableSpace K] [BorelSpace K]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [FiniteDimensional ℂ V]

def characterIntegral (ψ : Multiplicative K →* ℂˣ) (hψ : Continuous ψ)
    (μ : Measure K) [μ.IsAddHaarMeasure] : CcLC K V →ₗ[ℂ] V where
  toFun φ := ∫ x, ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) • value φ x ∂μ
  map_add' := by
    intro φ η
    change (∫ x, _ • (value φ x + value η x) ∂μ) = _
    simp_rw [smul_add]
    exact integral_add (integrable_inverse_character_smul φ ψ hψ μ)
      (integrable_inverse_character_smul η ψ hψ μ)
  map_smul' := by
    intro c φ
    change (∫ x, _ • (c • value φ x) ∂μ) = _
    simp_rw [smul_comm _ c]
    exact integral_smul c _

@[simp] theorem characterIntegral_apply (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure] (φ : CcLC K V) :
    characterIntegral ψ hψ μ φ =
      ∫ x, ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) • value φ x ∂μ := rfl

private theorem integral_bump (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (ho : IsOpen (H : Set K)) (hc : IsCompact (H : Set K))
    (e : V) : (∫ x, value (compactOpenBump H ho hc e) x ∂μ) =
      (μ.real (H : Set K) : ℂ) • e := by
  rw [show value (compactOpenBump H ho hc e) = (H : Set K).indicator (fun _ => e) from rfl,
    integral_indicator ho.measurableSet, setIntegral_const]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

private theorem integral_coset (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (ho : IsOpen (H : Set K)) (hc : IsCompact (H : Set K))
    (a : K) (e : V) :
    (∫ x, (additiveCoset H a).indicator (fun _ => e) x ∂μ) =
      (μ.real (H : Set K) : ℂ) • e := by
  have he : (additiveCoset H a).indicator (fun _ => e) =
      fun x => value (compactOpenBump H ho hc e) (x + -a) := by
    classical
    ext x
    change (if x - a ∈ H then e else 0) = (if x + -a ∈ H then e else 0)
    rw [sub_eq_add_neg]
  rw [he, integral_add_right_eq_self, integral_bump]

private theorem integrable_coset (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (ho : IsOpen (H : Set K)) (hc : IsCompact (H : Set K))
    (a : K) (e : V) :
    Integrable ((additiveCoset H a).indicator (fun _ => e)) μ := by
  have he : (additiveCoset H a).indicator (fun _ => e) =
      value (translation (-a) (compactOpenBump H ho hc e)) := by
    classical
    ext x
    change (if x - a ∈ H then e else 0) = (if x + -a ∈ H then e else 0)
    rw [sub_eq_add_neg]
  rw [he]
  exact KPJacquetStepFunction.integrable _ μ

theorem characterIntegral_finite_coset_expansion
    (ψ : Multiplicative K →* ℂˣ) (hψ : Continuous ψ)
    (μ : Measure K) [μ.IsAddHaarMeasure] (φ : CcLC K V)
    (H : AddSubgroup K) (hHopen : IsOpen (H : Set K))
    (hHcompact : IsCompact (H : Set K))
    (hHψ : ∀ h ∈ H, ψ (Multiplicative.ofAdd h) = 1)
    (n : ℕ) (a : Fin n → K) (e : Fin n → V)
    (hφ : ∀ x : K, value φ x =
      ∑ i : Fin n, (additiveCoset H (a i)).indicator (fun _ => e i) x) :
    characterIntegral ψ hψ μ φ = (μ.real (H : Set K) : ℂ) •
      ∑ i : Fin n, ((ψ (Multiplicative.ofAdd (a i)) : ℂ)⁻¹) • e i := by
  classical
  have ht (b : K) (v : V) (x : K) :
      ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) •
        (additiveCoset H b).indicator (fun _ => v) x =
      (additiveCoset H b).indicator (fun _ =>
        ((ψ (Multiplicative.ofAdd b) : ℂ)⁻¹) • v) x := by
    by_cases hx : x ∈ additiveCoset H b
    · have hp : ψ (Multiplicative.ofAdd x) = ψ (Multiplicative.ofAdd b) := by
        have hm := hHψ (x - b) hx
        have he : x = (x - b) + b := sub_add_cancel x b |>.symm
        rw [he, ofAdd_add, map_mul, hm, one_mul]
      simp [Set.indicator_of_mem hx, hp]
    · simp [Set.indicator_of_notMem hx]
  simp only [characterIntegral_apply, hφ, Finset.smul_sum, ht]
  rw [integral_finset_sum _ (fun i _ => integrable_coset μ H hHopen hHcompact _ _)]
  simp only [integral_coset μ H hHopen hHcompact, Finset.smul_sum]

theorem characterIntegral_translation (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure]
    (y : K) (φ : CcLC K V) :
    characterIntegral ψ hψ μ (translation y φ) =
      (ψ (Multiplicative.ofAdd y) : ℂ) • characterIntegral ψ hψ μ φ := by
  have hp (x : K) :
      ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) • value φ (x + y) =
      (ψ (Multiplicative.ofAdd y) : ℂ) •
        (((ψ (Multiplicative.ofAdd (x + y)) : ℂ)⁻¹) • value φ (x + y)) := by
    have hm : (ψ (Multiplicative.ofAdd (x + y)) : ℂ) =
        (ψ (Multiplicative.ofAdd x) : ℂ) * (ψ (Multiplicative.ofAdd y) : ℂ) := by
      rw [ofAdd_add, map_mul, Units.val_mul]
    rw [hm, smul_smul]
    congr 1
    field_simp
  simp only [characterIntegral_apply, value_translation, hp]
  rw [integral_smul]
  congr 1
  exact integral_add_right_eq_self
    (fun x => ((ψ (Multiplicative.ofAdd x) : ℂ)⁻¹) • value φ x) y

def normalizedBump (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (hHopen : IsOpen (H : Set K))
    (hHcompact : IsCompact (H : Set K)) (e : V) : CcLC K V :=
  (μ.real (H : Set K) : ℂ)⁻¹ • compactOpenBump H hHopen hHcompact e

@[simp] theorem value_normalizedBump (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (hHopen : IsOpen (H : Set K))
    (hHcompact : IsCompact (H : Set K)) (e : V) (x : K) :
    value (normalizedBump μ H hHopen hHcompact e) x =
      (μ.real (H : Set K) : ℂ)⁻¹ • (H : Set K).indicator (fun _ => e) x := by
  rfl

private theorem volume_ne_zero (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (ho : IsOpen (H : Set K)) (hc : IsCompact (H : Set K)) :
    (μ.real (H : Set K) : ℂ) ≠ 0 := by
  obtain ⟨hp, hf⟩ := compactOpen_volume_pos_lt_top μ H ho hc
  exact_mod_cast (ENNReal.toReal_pos hp.ne' hf.ne).ne'

private theorem default_level :
    ∃ U : AddSubgroup K, IsOpen (U : Set K) ∧ IsCompact (U : Set K) := by
  let U := (ValuativeRel.valuation K).leAddSubgroup 1
  refine ⟨U, ?_, IsNonarchimedeanLocalField.isCompact_closedBall K 1⟩
  change IsOpen {x | ValuativeRel.valuation K x ≤ 1}
  simpa only [Valuation.restrict_le_one_iff] using Valuation.isOpen_closedBall (v := ValuativeRel.valuation K) (r := 1) one_ne_zero

theorem characterIntegral_normalizedBump (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure]
    (H : AddSubgroup K) (hHopen : IsOpen (H : Set K))
    (hHcompact : IsCompact (H : Set K))
    (hHψ : ∀ h ∈ H, ψ (Multiplicative.ofAdd h) = 1) (e : V) :
    characterIntegral ψ hψ μ (normalizedBump μ H hHopen hHcompact e) = e := by
  have hb : characterIntegral ψ hψ μ (compactOpenBump H hHopen hHcompact e) =
      (μ.real (H : Set K) : ℂ) • e := by
    simpa [additiveCoset] using characterIntegral_finite_coset_expansion ψ hψ μ
      (compactOpenBump H hHopen hHcompact e) H hHopen hHcompact hHψ
      1 (fun _ => 0) (fun _ => e) (by intro x; simp [value_compactOpenBump, additiveCoset])
  rw [normalizedBump, map_smul, hb, smul_smul,
    inv_mul_cancel₀ (volume_ne_zero μ H hHopen hHcompact), one_smul]

theorem characterIntegral_surjective (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure] :
    Function.Surjective (characterIntegral (V := V) ψ hψ μ) := by
  obtain ⟨U, ho, hc⟩ := default_level (K := K)
  obtain ⟨H, _, hHo, hHc, hHψ, _⟩ :=
    exists_character_adapted_expansion (0 : CcLC K V) U ho hc ψ hψ
  intro e
  exact ⟨normalizedBump μ H hHo hHc e,
    characterIntegral_normalizedBump ψ hψ μ H hHo hHc hHψ e⟩

 def bumpMap (H : AddSubgroup K) (ho : IsOpen (H : Set K))
    (hc : IsCompact (H : Set K)) : V →ₗ[ℂ] CcLC K V where
  toFun := compactOpenBump H ho hc
  map_add' := by
    intro e f
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change (H : Set K).indicator (fun _ => e + f) x =
      (H : Set K).indicator (fun _ => e) x + (H : Set K).indicator (fun _ => f) x
    by_cases hx : x ∈ H <;> simp [Set.indicator, hx]
  map_smul' := by
    intro c e
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change (H : Set K).indicator (fun _ => c • e) x =
      c • (H : Set K).indicator (fun _ => e) x
    by_cases hx : x ∈ H <;> simp [Set.indicator, hx]

private theorem class_expansion (ψ : Multiplicative K →* ℂˣ)
    (φ : CcLC K V) (H : AddSubgroup K)
    (ho : IsOpen (H : Set K)) (hc : IsCompact (H : Set K))
    (n : ℕ) (a : Fin n → K) (e : Fin n → V)
    (he : ∀ x, value φ x =
      ∑ i : Fin n, (additiveCoset H (a i)).indicator (fun _ => e i) x) :
    coinvariantsMk ψ φ = coinvariantsMk ψ
      (compactOpenBump H ho hc (∑ i : Fin n, ((ψ (Multiplicative.ofAdd (a i)) : ℂ)⁻¹) • e i)) := by
  classical
  have hφ : φ = ∑ i : Fin n, translation (-a i) (compactOpenBump H ho hc (e i)) := by
    apply Subtype.ext
    apply LocallyConstant.ext
    intro x
    change value φ x = _
    rw [he]
    rw [Submodule.coe_sum]
    have hs := map_sum (LocallyConstant.coeFnAddMonoidHom (X := K) (Y := V))
      (fun i : Fin n => (translation (-a i) (compactOpenBump H ho hc (e i))).val) Finset.univ
    have hsx := congrFun hs x
    simp only [LocallyConstant.coeFnAddMonoidHom_apply, Finset.sum_apply] at hsx
    change (∑ i : Fin n, (additiveCoset H (a i)).indicator (fun _ => e i) x) = _
    rw [hsx]
    change (∑ i : Fin n, (additiveCoset H (a i)).indicator (fun _ => e i) x) =
      ∑ i : Fin n, value (translation (-a i) (compactOpenBump H ho hc (e i))) x
    apply Finset.sum_congr rfl
    intro i _
    change (if x - a i ∈ H then e i else 0) = (if x + -a i ∈ H then e i else 0)
    rw [sub_eq_add_neg]
  have hq (i : Fin n) :
      coinvariantsMk ψ (translation (-a i) (compactOpenBump H ho hc (e i))) =
      ((ψ (Multiplicative.ofAdd (a i)) : ℂ)⁻¹) •
        coinvariantsMk ψ (compactOpenBump H ho hc (e i)) := by
    have hh := rootCoinvariantsMk_equivariant (translationRepresentation (K := K) (E := V))
        (MonoidHom.id (Multiplicative K)) ψ (Multiplicative.ofAdd (-a i))
        (compactOpenBump H ho hc (e i))
    change coinvariantsMk ψ (translation (-a i) (compactOpenBump H ho hc (e i))) =
      (ψ (Multiplicative.ofAdd (-a i)) : ℂ) •
        coinvariantsMk ψ (compactOpenBump H ho hc (e i)) at hh
    rw [ofAdd_neg, map_inv, Units.val_inv_eq_inv_val] at hh
    exact hh
  rw [hφ, map_sum]
  simp_rw [hq]
  have hm := map_sum ((coinvariantsMk ψ).comp (bumpMap (V := V) H ho hc))
    (fun i : Fin n => ((ψ (Multiplicative.ofAdd (a i)) : ℂ)⁻¹) • e i) Finset.univ
  change coinvariantsMk ψ (compactOpenBump H ho hc _) =
    ∑ i : Fin n, coinvariantsMk ψ ((bumpMap H ho hc)
      (((ψ (Multiplicative.ofAdd (a i)) : ℂ)⁻¹) • e i)) at hm
  simp only [map_smul] at hm
  exact hm.symm

theorem characterIntegral_ker (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure] :
    LinearMap.ker (characterIntegral (V := V) ψ hψ μ) =
      translationRelations (E := V) ψ := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨U, ho, hc⟩ := default_level (K := K)
    obtain ⟨H, _, hHo, hHc, hHψ, _, n, a, e, _, he⟩ :=
      exists_character_adapted_expansion φ U ho hc ψ hψ
    have hi := characterIntegral_finite_coset_expansion ψ hψ μ φ H hHo hHc hHψ n a e he
    have hz : (∑ i : Fin n, ((ψ (Multiplicative.ofAdd (a i)) : ℂ)⁻¹) • e i) = 0 := by
      have h0 : characterIntegral ψ hψ μ φ = 0 := hφ
      rw [h0] at hi
      exact (smul_eq_zero.mp hi.symm).resolve_left (volume_ne_zero μ H hHo hHc)
    have hq := class_expansion ψ φ H hHo hHc n a e he
    rw [hz] at hq
    have hb : compactOpenBump H hHo hHc (0 : V) = 0 := (bumpMap H hHo hHc).map_zero
    rw [hb, map_zero] at hq
    change φ ∈ rootRelationSpan (translationRepresentation (K := K) (E := V))
      (MonoidHom.id (Multiplicative K)) ψ
    rw [← rootCoinvariantsMk_ker, LinearMap.mem_ker]
    exact hq
  · rw [translationRelations_eq_span, Submodule.span_le]
    rintro _ ⟨⟨y, φ⟩, rfl⟩
    change characterIntegral ψ hψ μ
      (translation y φ - (ψ (Multiplicative.ofAdd y) : ℂ) • φ) = 0
    rw [map_sub, map_smul, characterIntegral_translation, sub_self]

def coinvariantsIntegral (ψ : Multiplicative K →* ℂˣ) (hψ : Continuous ψ)
    (μ : Measure K) [μ.IsAddHaarMeasure] :
    TranslationCoinvariants (E := V) ψ →ₗ[ℂ] V :=
  rootCoinvariantsLift (translationRepresentation (K := K) (E := V))
    (MonoidHom.id (Multiplicative K)) ψ
    ⟨characterIntegral ψ hψ μ, by
      intro t φ
      exact characterIntegral_translation ψ hψ μ (Multiplicative.toAdd t) φ⟩

@[simp] theorem coinvariantsIntegral_mk (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure] (φ : CcLC K V) :
    coinvariantsIntegral ψ hψ μ (coinvariantsMk ψ φ) = characterIntegral ψ hψ μ φ := rfl

theorem coinvariantsIntegral_bijective (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure] :
    Function.Bijective (coinvariantsIntegral (V := V) ψ hψ μ) := by
  constructor
  · intro x y hxy
    obtain ⟨φ, rfl⟩ := rootCoinvariantsMk_surjective
      (translationRepresentation (K := K) (E := V)) (MonoidHom.id _) ψ x
    obtain ⟨η, rfl⟩ := rootCoinvariantsMk_surjective
      (translationRepresentation (K := K) (E := V)) (MonoidHom.id _) ψ y
    have hm : φ - η ∈ LinearMap.ker (characterIntegral ψ hψ μ) := by
      rw [LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr hxy
    rw [characterIntegral_ker, translationRelations, ← rootCoinvariantsMk_ker,
      LinearMap.mem_ker, map_sub] at hm
    exact sub_eq_zero.mp hm
  · intro e
    obtain ⟨φ, hφ⟩ := characterIntegral_surjective ψ hψ μ e
    exact ⟨coinvariantsMk ψ φ, hφ⟩

def coinvariantsEquiv (ψ : Multiplicative K →* ℂˣ) (hψ : Continuous ψ)
    (μ : Measure K) [μ.IsAddHaarMeasure] :
    TranslationCoinvariants (E := V) ψ ≃ₗ[ℂ] V :=
  LinearEquiv.ofBijective (coinvariantsIntegral ψ hψ μ)
    (coinvariantsIntegral_bijective ψ hψ μ)

@[simp] theorem coinvariantsEquiv_mk (ψ : Multiplicative K →* ℂˣ)
    (hψ : Continuous ψ) (μ : Measure K) [μ.IsAddHaarMeasure] (φ : CcLC K V) :
    coinvariantsEquiv ψ hψ μ (coinvariantsMk ψ φ) = characterIntegral ψ hψ μ φ := rfl

def ordinaryIntegral (μ : Measure K) [μ.IsAddHaarMeasure] : CcLC K V →ₗ[ℂ] V :=
  characterIntegral 1 (by fun_prop) μ

@[simp] theorem ordinaryIntegral_apply (μ : Measure K) [μ.IsAddHaarMeasure]
    (φ : CcLC K V) : ordinaryIntegral μ φ = ∫ x, value φ x ∂μ := by
  simp [ordinaryIntegral, characterIntegral_apply]

def localAbs (a : Kˣ) : ℝ :=
  (addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) : ℝ)

def dilateWith (a : Kˣ) (A : V →ₗ[ℂ] V) (φ : CcLC K V) : CcLC K V :=
  ⟨LocallyConstant.map A (LocallyConstant.comap
      ⟨fun x => (↑a : K)⁻¹ * x, continuous_const.mul continuous_id⟩ φ.val), by
    exact (φ.property.comp_homeomorph
      (Homeomorph.mulLeft₀ (↑a : K)⁻¹ (inv_ne_zero (Units.ne_zero a)))).comp_left A.map_zero⟩

@[simp] theorem value_dilateWith (a : Kˣ) (A : V →ₗ[ℂ] V)
    (φ : CcLC K V) (x : K) :
    value (dilateWith a A φ) x = A (value φ ((↑a : K)⁻¹ * x)) := rfl

theorem ordinaryIntegral_dilateWith (μ : Measure K) [μ.IsAddHaarMeasure]
    (a : Kˣ) (A : V →ₗ[ℂ] V) (φ : CcLC K V) :
    ordinaryIntegral μ (dilateWith a A φ) =
      (localAbs a : ℂ) • A (ordinaryIntegral μ φ) := by
  letI : SecondCountableTopology K := by
    letI := IsTopologicalAddGroup.rightUniformSpace K
    letI := isUniformAddGroup_of_addCommGroup (G := K)
    letI : (Valued.v (R := K)).RankOne :=
      { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K).comp
          MonoidWithZeroHom.ValueGroup₀.embedding
        strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
          MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
    open scoped Valued in
      haveI : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
      exact inferInstance
  let T := ContinuousAddEquiv.mulLeft a
  let m := addEquivAddHaarChar T
  have hm := addEquivAddHaarChar_smul_map μ T.symm
  rw [addEquivAddHaarChar_symm] at hm
  have hmap : μ.map T.symm = m • μ := by
    have hh := congrArg (fun ν : Measure K => m • ν) hm
    simpa [m, smul_smul, mul_inv_cancel₀ (addEquivAddHaarChar_pos T).ne'] using hh
  have hi : (∫ x, value φ ((↑a : K)⁻¹ * x) ∂μ) =
      (localAbs a : ℂ) • ordinaryIntegral μ φ := by
    have hh := integral_map_equiv (μ := μ) T.symm.toMeasurableEquiv (value φ)
    have he : ⇑T.symm.toMeasurableEquiv = fun x : K => (↑a : K)⁻¹ * x := by
      ext x
      change (ContinuousAddEquiv.mulLeft a).symm x = (↑a : K)⁻¹ * x
      apply (ContinuousAddEquiv.mulLeft a).injective
      simp [mul_assoc, Units.ne_zero a]
    rw [he] at hh
    have heT : ⇑T.symm = fun x : K => (↑a : K)⁻¹ * x := he
    rw [heT] at hmap
    rw [← hh, hmap, integral_smul_nnreal_measure, ordinaryIntegral_apply]
    exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _
  rw [ordinaryIntegral_apply]
  change (∫ x, A (value φ ((↑a : K)⁻¹ * x)) ∂μ) = _
  have hiφ : Integrable (fun x => value φ ((↑a : K)⁻¹ * x)) μ := by
    exact KPJacquetStepFunction.integrable (dilateWith a (LinearMap.id) φ) μ
  change (∫ x, (LinearMap.toContinuousLinearMap A)
    (value φ ((↑a : K)⁻¹ * x)) ∂μ) = _
  rw [ContinuousLinearMap.integral_comp_comm _ hiφ, hi]
  exact (LinearMap.toContinuousLinearMap A).map_smul _ _

end Integration

end DedekindZetaZeroFree.KPJacquetOpenTestFunction

end
