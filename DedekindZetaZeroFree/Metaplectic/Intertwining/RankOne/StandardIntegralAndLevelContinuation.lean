module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.RankOne.RootParameterCompactPicture

@[expose] public section

namespace DedekindZetaZeroFree.KPRankOneShellContinuation

open scoped Valued
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPRankOneRootParameter
open KPLocalPrincipalSeries KPRankOneRootParameter KPLocalStoneVonNeumann

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

def sourceSign : Sign → Sign := id

def targetSign : Sign → Sign
  | .plus => .minus
  | .minus => .plus

def sourceParameter (ε : Sign) (s : ℂ) : ℂ :=
  if ε = .plus then s else -s

def targetParameter (ε : Sign) (s : ℂ) : ℂ := -(sourceParameter ε s)

def convergenceHalfPlane (ε : Sign) (s : ℂ) : Prop :=
  if ε = .plus then -(1 / 6 : ℝ) < s.re else s.re < -(1 / 6 : ℝ)

def evaluationUnit (ε : Sign) (s : ℂ) : ℂˣ :=
  if ε = .plus then rUnit K s else (rUnit K s)⁻¹

def denominator (ε : Sign) (s : ℂ) : ℂ :=
  if ε = .plus then 1 - t K s else
    1 - (residueCardinality K : ℂ) * (r K s)⁻¹ ^ 6

def kernelW (A : LocalBorelData (K := K) (G := G) T) : Sign → G
  | .plus => A.liftedW⁻¹
  | .minus => A.liftedW

def standardIntegralCoordinate
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (μ : Measure K) (ε : Sign) (s : ℂ)
    (φ : compactPicture A P I (sourceSign ε)) (g : G) (h : H) : ℂ :=
  ∫ x : K,
    ((compactTrivialization A P I (sourceSign ε) (sourceParameter ε s) φ).val
      (kernelW K A ε * (A.upperRoot (Multiplicative.ofAdd x) : G) * g)).val h ∂μ

abbrev LevelLaurentOperator
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G) (ε : Sign) :=
  ℤ →₀ (compactLevel A P I (sourceSign ε) J →ₗ[ℂ]
    compactLevel A P I (targetSign ε) J)

def evaluate (A : LocalBorelData (K := K) (G := G) T)
    (P : Polarization T) (I : IwasawaData A) (J : CompactOpenLevel G)
    (ε : Sign) (p : LevelLaurentOperator K A P I J ε) (u : ℂˣ) :
    compactLevel A P I (sourceSign ε) J →ₗ[ℂ]
      compactLevel A P I (targetSign ε) J :=
  p.sum (fun n M => ((u : ℂ) ^ n) • M)

def IsLevelNumerator
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G) (μ : Measure K)
    (ε : Sign) (p : LevelLaurentOperator K A P I J ε) : Prop :=
  ∀ (s : ℂ), convergenceHalfPlane ε s →
    ∀ (φ : compactLevel A P I (sourceSign ε) J)
      (k : I.compact.toOpenSubgroup) (h : H),
      ((evaluate K A P I J ε p (evaluationUnit K ε s) φ :
        compactPicture A P I (targetSign ε)).val k).val h =
        denominator K ε s *
          standardIntegralCoordinate K A P I μ ε s
            (φ : compactPicture A P I (sourceSign ε)) (k : G) h

def continuedLevel
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G) (ε : Sign)
    (p : LevelLaurentOperator K A P I J ε) (s : ℂ) :
    compactLevel A P I (sourceSign ε) J →ₗ[ℂ]
      compactLevel A P I (targetSign ε) J :=
  (denominator K ε s)⁻¹ • evaluate K A P I J ε p (evaluationUnit K ε s)

theorem continuedLevel_eq_integral
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G)
    (μ : Measure K) (ε : Sign)
    (p : LevelLaurentOperator K A P I J ε)
    (hp : IsLevelNumerator K A P I J μ ε p)
    (s : ℂ) (hs : convergenceHalfPlane ε s)
    (hd : denominator K ε s ≠ 0)
    (φ : compactLevel A P I (sourceSign ε) J)
    (k : I.compact.toOpenSubgroup) (h : H) :
    ((continuedLevel K A P I J ε p s φ :
      compactPicture A P I (targetSign ε)).val k).val h =
      standardIntegralCoordinate K A P I μ ε s
        (φ : compactPicture A P I (sourceSign ε)) (k : G) h := by
  change (denominator K ε s)⁻¹ *
    ((evaluate K A P I J ε p (evaluationUnit K ε s) φ :
      compactPicture A P I (targetSign ε)).val k).val h = _
  rw [hp s hs φ k h, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]

def transportToSections
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (s : ℂ)
    (B : compactPicture A P I (sourceSign ε) →ₗ[ℂ]
      compactPicture A P I (targetSign ε)) :
    sectionSpace A P (sourceSign ε) (sourceParameter ε s) →ₗ[ℂ]
      sectionSpace A P (targetSign ε) (targetParameter ε s) :=
  (compactTrivialization A P I (targetSign ε) (targetParameter ε s)).toLinearMap.comp
    (B.comp (compactTrivialization A P I
      (sourceSign ε) (sourceParameter ε s)).symm.toLinearMap)

theorem convergence_iff_geometric
    (ε : Sign) (s : ℂ) :
    convergenceHalfPlane ε s ↔
      (if ε = .plus then ‖t K s‖ < 1 else ‖(t K s)⁻¹‖ < 1) := by
  have hl : 0 < Real.log (residueCardinality K : ℝ) := by
    apply Real.log_pos
    exact_mod_cast Finite.one_lt_card (α := 𝓀[K])
  have ht : ‖t K s‖ = Real.exp ((-1 - 6 * s.re) * Real.log (residueCardinality K : ℝ)) := by
    have hq : 0 < (residueCardinality K : ℝ) := by exact_mod_cast Nat.card_pos (α := 𝓀[K])
    simp only [t, r, norm_mul, norm_inv, norm_pow, Complex.norm_natCast, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
      Complex.ofReal_im, mul_zero, sub_zero]
    rw [← Real.exp_nat_mul, show (residueCardinality K : ℝ)⁻¹ = Real.exp (-Real.log (residueCardinality K : ℝ)) by rw [Real.exp_neg, Real.exp_log hq], ← Real.exp_add]
    congr 1
    ring
  cases ε with
  | plus =>
    simp only [convergenceHalfPlane, if_pos rfl, if_true, ht, Real.exp_lt_one_iff,
      mul_neg_iff, not_lt_of_ge hl.le, and_false, false_or, hl, and_true]
    constructor <;> intro hs <;> linarith
  | minus =>
    simp only [convergenceHalfPlane, reduceCtorEq, if_false, norm_inv, ht,
      ← Real.exp_neg, Real.exp_lt_one_iff, neg_neg_iff_pos, mul_pos_iff_of_pos_right hl]
    constructor <;> intro hs <;> linarith

theorem denominator_ne_zero_at_zero (ε : Sign) :
    denominator K ε 0 ≠ 0 := by
  have hq : (residueCardinality K : ℂ) ≠ 1 := by
    exact_mod_cast (ne_of_gt (Finite.one_lt_card (α := 𝓀[K])))
  cases ε <;> simp [denominator, t, r, sub_ne_zero, hq, Ne.symm hq, inv_eq_one]

private theorem laurent_zero (p : LaurentPolynomial ℂ)
    (U : Set ℂˣ) (hU : U.Infinite)
    (hp : ∀ u ∈ U, LaurentPolynomial.eval₂ (RingHom.id ℂ) u p = 0) : p = 0 := by
  obtain ⟨n, f, hf⟩ := LaurentPolynomial.exists_T_pow p
  have hroots : {x : ℂ | f.eval x = (0 : Polynomial ℂ).eval x}.Infinite := by
    apply (hU.image (f := fun u : ℂˣ => (u : ℂ)) Units.val_injective.injOn).mono
    rintro x ⟨u, hu, rfl⟩
    have he := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ) u) hf
    simp only [map_mul, LaurentPolynomial.eval₂_toLaurent, Polynomial.eval₂_id,
      hp u hu, zero_mul, Polynomial.eval_zero] at he ⊢
    exact he
  have hz := Polynomial.eq_of_infinite_eval_eq f 0 hroots
  rw [hz, map_zero] at hf
  exact (IsUnit.mul_left_inj (LaurentPolynomial.isUnit_T (R := ℂ) (n : ℤ))).mp (by simpa using hf.symm)

 def scalarLaurent {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℤ →₀ V) (l : V →ₗ[ℂ] ℂ) : LaurentPolynomial ℂ :=
  p.sum (fun n v => LaurentPolynomial.C (l v) * LaurentPolynomial.T n)

private theorem scalarLaurent_coeff {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℤ →₀ V) (l : V →ₗ[ℂ] ℂ) (n : ℤ) :
    (scalarLaurent p l).coeff n = l (p n) := by
  classical
  simp only [scalarLaurent, ← LaurentPolynomial.single_eq_C_mul_T,
    Finsupp.sum, AddMonoidAlgebra.coeff_sum, Finsupp.finset_sum_apply,
    AddMonoidAlgebra.coeff_single]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b hb hbn
    simp [hbn]
  · intro hn
    simp [Finsupp.notMem_support_iff.mp hn]

private theorem scalarLaurent_eval {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (p : ℤ →₀ V) (l : V →ₗ[ℂ] ℂ) (u : ℂˣ) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) u (scalarLaurent p l) =
      l (p.sum (fun n v => (u : ℂ) ^ n • v)) := by
  classical
  simp only [scalarLaurent, Finsupp.sum, map_sum,
    LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, Units.val_zpow_eq_zpow_val,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  exact mul_comm _ _
private theorem evaluation_norm (ε : Sign) (x : ℝ) :
    ‖(evaluationUnit K ε (x : ℂ) : ℂ)‖ =
      Real.exp ((if ε = .plus then -x else x) * Real.log (residueCardinality K : ℝ)) := by
  cases ε with
  | plus =>
    change ‖r K (x : ℂ)‖ = _
    simp only [r, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero,
      evaluationUnit, if_true]
  | minus =>
    change ‖(r K (x : ℂ))⁻¹‖ = _
    simp only [r, norm_inv, Complex.norm_exp, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.neg_im, Complex.ofReal_im, mul_zero, sub_zero,
      ← Real.exp_neg, neg_mul, neg_neg, reduceCtorEq, if_false]

private theorem evaluation_infinite (ε : Sign) :
    {u : ℂˣ | ∃ s : ℂ, convergenceHalfPlane ε s ∧ evaluationUnit K ε s = u}.Infinite := by
  let a : ℕ → ℝ := fun n => if ε = .plus then (n : ℝ) else -(n : ℝ) - 1
  have ha : Function.Injective a := by
    intro m n h
    dsimp [a] at h
    cases ε <;> simp only [if_true, if_false, reduceCtorEq] at h
    · exact_mod_cast h
    · have : (m : ℝ) = (n : ℝ) := by linarith
      exact_mod_cast this
  have hl : Real.log (residueCardinality K : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.log_pos
    exact_mod_cast Finite.one_lt_card (α := 𝓀[K])
  have hinj : Function.Injective (fun n => evaluationUnit K ε (a n : ℂ)) := by
    intro m n h
    apply ha
    have he := congrArg (fun u : ℂˣ => ‖(u : ℂ)‖) h
    rw [evaluation_norm, evaluation_norm] at he
    have he := Real.exp_injective he
    have he' := (mul_left_inj' hl).mp he
    cases ε <;> simpa using he'
  apply (Set.infinite_range_of_injective hinj).mono
  rintro u ⟨n, rfl⟩
  refine ⟨(a n : ℂ), ?_, rfl⟩
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  cases ε <;> simp only [a, convergenceHalfPlane, if_true, if_false,
    reduceCtorEq, Complex.ofReal_re] <;> linarith

 def scalarCoordinate
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G) (ε : Sign)
    (φ : compactLevel A P I (sourceSign ε) J)
    (k : I.compact.toOpenSubgroup) (h : H) :
    (compactLevel A P I (sourceSign ε) J →ₗ[ℂ]
      compactLevel A P I (targetSign ε) J) →ₗ[ℂ] ℂ where
  toFun M := ((M φ : compactPicture A P I (targetSign ε)).val k).val h
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

theorem level_numerator_compatible
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J J' : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup)
    (hJ' : (J'.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup)
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation K).integer : Set K) = 1)
    (ζ : (valuation K).integer) (hζ : IsPrimitiveRoot ζ 3)
    (ε : Sign)
    (p : LevelLaurentOperator K A P I J ε)
    (p' : LevelLaurentOperator K A P I J' ε)
    (hp : IsLevelNumerator K A P I J μ ε p)
    (hp' : IsLevelNumerator K A P I J' μ ε p')
    (φ : compactLevel A P I (sourceSign ε) J)
    (φ' : compactLevel A P I (sourceSign ε) J')
    (hφ : (φ : compactPicture A P I (sourceSign ε)) =
      (φ' : compactPicture A P I (sourceSign ε))) (n : ℤ) :
    ((p n) φ : compactPicture A P I (targetSign ε)) =
      ((p' n) φ' : compactPicture A P I (targetSign ε)) := by
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  let l := scalarCoordinate K A P I J ε φ k h
  let l' := scalarCoordinate K A P I J' ε φ' k h
  have hz : scalarLaurent p l - scalarLaurent p' l' = 0 := by
    apply laurent_zero _ _ (evaluation_infinite K ε)
    rintro u ⟨s, hs, rfl⟩
    rw [map_sub, scalarLaurent_eval, scalarLaurent_eval, sub_eq_zero]
    change ((evaluate K A P I J ε p (evaluationUnit K ε s) φ :
      compactPicture A P I (targetSign ε)).val k).val h =
        ((evaluate K A P I J' ε p' (evaluationUnit K ε s) φ' :
          compactPicture A P I (targetSign ε)).val k).val h
    rw [hp s hs φ k h, hp' s hs φ' k h, hφ]
  have he := congrArg (fun q : LaurentPolynomial ℂ => q.coeff n) (sub_eq_zero.mp hz)
  rw [scalarLaurent_coeff, scalarLaurent_coeff] at he
  exact he

theorem level_numerator_unique
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G)
    (μ : Measure K) (ε : Sign)
    (p p' : LevelLaurentOperator K A P I J ε)
    (hp : IsLevelNumerator K A P I J μ ε p)
    (hp' : IsLevelNumerator K A P I J μ ε p') : p = p' := by
  apply Finsupp.ext
  intro n
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  let l := scalarCoordinate K A P I J ε φ k h
  have hz : scalarLaurent p l - scalarLaurent p' l = 0 := by
    apply laurent_zero _ _ (evaluation_infinite K ε)
    rintro u ⟨s, hs, rfl⟩
    rw [map_sub, scalarLaurent_eval, scalarLaurent_eval, sub_eq_zero]
    change ((evaluate K A P I J ε p (evaluationUnit K ε s) φ :
      compactPicture A P I (targetSign ε)).val k).val h =
        ((evaluate K A P I J ε p' (evaluationUnit K ε s) φ :
          compactPicture A P I (targetSign ε)).val k).val h
    rw [hp s hs φ k h, hp' s hs φ k h]
  have he := congrArg (fun q : LaurentPolynomial ℂ => q.coeff n) (sub_eq_zero.mp hz)
  rw [scalarLaurent_coeff, scalarLaurent_coeff] at he
  exact he

def lowerRootCoordinate (A : LocalBorelData (K := K) (G := G) T) (x : K) : G :=
  A.liftedW⁻¹ * (A.upperRoot (Multiplicative.ofAdd x) : G) * A.liftedW

theorem lowerRootCoordinate_uniform_cutoff
    (A : LocalBorelData (K := K) (G := G) T)
    (I : IwasawaData A) (J : CompactOpenLevel G) :
    ∀ᶠ x : K in nhds 0, ∀ k : I.compact.toOpenSubgroup,
      (k : G)⁻¹ * lowerRootCoordinate K A x * (k : G) ∈ J.toOpenSubgroup := by
  have hc : Continuous (lowerRootCoordinate K A) := by
    unfold lowerRootCoordinate
    exact ((continuous_const.mul (continuous_subtype_val.comp
      (A.upperRoot_continuous.comp continuous_ofAdd))).mul continuous_const)
  have hK : IsCompact (Set.univ : Set I.compact.toOpenSubgroup) := by
    exact isCompact_iff_isCompact_univ.mp I.compact.isCompact
  suffices he : ∀ᶠ x : K in nhds 0, ∀ k ∈ (Set.univ : Set I.compact.toOpenSubgroup),
      (k : G)⁻¹ * lowerRootCoordinate K A x * (k : G) ∈ J.toOpenSubgroup by
    simpa only [Set.mem_univ, forall_const] using he
  apply hK.eventually_forall_of_forall_eventually
  intro k hk
  have hh : Continuous (fun z : K × I.compact.toOpenSubgroup =>
      (z.2 : G)⁻¹ * lowerRootCoordinate K A z.1 * (z.2 : G)) := by
    fun_prop
  have hval : (fun z : K × I.compact.toOpenSubgroup =>
      (z.2 : G)⁻¹ * lowerRootCoordinate K A z.1 * (z.2 : G)) (0, k) = 1 := by
    simp [lowerRootCoordinate]
  filter_upwards [(hh.continuousAt.preimage_mem_nhds (by
    simpa [hval] using
      J.toOpenSubgroup.isOpen.mem_nhds J.toOpenSubgroup.one_mem))] with z hz
  exact hz

theorem denominator_ne_zero_of_convergence (ε : Sign) (s : ℂ)
    (hs : convergenceHalfPlane ε s) : denominator K ε s ≠ 0 := by
  have ht := (convergence_iff_geometric K ε s).mp hs
  cases ε with
  | plus =>
    change 1 - t K s ≠ 0
    simp only [if_pos rfl] at ht
    intro he
    have he : t K s = 1 := (sub_eq_zero.mp he).symm
    simpa [he] using ht
  | minus =>
    have he : (residueCardinality K : ℂ) * (r K s)⁻¹ ^ 6 = (t K s)⁻¹ := by
      simp [t, mul_inv_rev, inv_pow, mul_comm]
    change 1 - (residueCardinality K : ℂ) * (r K s)⁻¹ ^ 6 ≠ 0
    rw [he]
    simp only [reduceCtorEq, if_false] at ht
    intro hz
    have hz : (t K s)⁻¹ = 1 := (sub_eq_zero.mp hz).symm
    simpa [hz] using ht

theorem continuedLevel_eq_integral_of_convergence
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J : CompactOpenLevel G)
    (μ : Measure K) (ε : Sign)
    (p : LevelLaurentOperator K A P I J ε)
    (hp : IsLevelNumerator K A P I J μ ε p)
    (s : ℂ) (hs : convergenceHalfPlane ε s)
    (φ : compactLevel A P I (sourceSign ε) J)
    (k : I.compact.toOpenSubgroup) (h : H) :
    ((continuedLevel K A P I J ε p s φ :
      compactPicture A P I (targetSign ε)).val k).val h =
      standardIntegralCoordinate K A P I μ ε s
        (φ : compactPicture A P I (sourceSign ε)) (k : G) h :=
  continuedLevel_eq_integral K A P I J μ ε p hp s hs
    (denominator_ne_zero_of_convergence K ε s hs) φ k h

theorem continuedLevel_compatible
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (J J' : CompactOpenLevel G)
    (hJ : (J.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup)
    (hJ' : (J'.toOpenSubgroup : Subgroup G) ≤ I.compact.toOpenSubgroup)
    (μ : Measure K) [μ.IsAddHaarMeasure]
    (hμ : μ ((valuation K).integer : Set K) = 1)
    (ζ : (valuation K).integer) (hζ : IsPrimitiveRoot ζ 3)
    (ε : Sign)
    (p : LevelLaurentOperator K A P I J ε)
    (p' : LevelLaurentOperator K A P I J' ε)
    (hp : IsLevelNumerator K A P I J μ ε p)
    (hp' : IsLevelNumerator K A P I J' μ ε p')
    (φ : compactLevel A P I (sourceSign ε) J)
    (φ' : compactLevel A P I (sourceSign ε) J')
    (hφ : (φ : compactPicture A P I (sourceSign ε)) =
      (φ' : compactPicture A P I (sourceSign ε))) (s : ℂ) :
    (continuedLevel K A P I J ε p s φ : compactPicture A P I (targetSign ε)) =
      (continuedLevel K A P I J' ε p' s φ' : compactPicture A P I (targetSign ε)) := by
  apply Subtype.ext
  funext k
  apply Subtype.ext
  funext h
  let l := scalarCoordinate K A P I J ε φ k h
  let l' := scalarCoordinate K A P I J' ε φ' k h
  have he : scalarLaurent p l = scalarLaurent p' l' := by
    apply LaurentPolynomial.ext
    intro n
    rw [scalarLaurent_coeff, scalarLaurent_coeff]
    exact congrArg (fun v : compactPicture A P I (targetSign ε) => (v.val k).val h)
      (level_numerator_compatible K A P I J J' hJ hJ' μ hμ ζ hζ ε p p' hp hp' φ φ' hφ n)
  have hv := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ) (evaluationUnit K ε s)) he
  rw [scalarLaurent_eval, scalarLaurent_eval] at hv
  change (denominator K ε s)⁻¹ *
    ((evaluate K A P I J ε p (evaluationUnit K ε s) φ :
      compactPicture A P I (targetSign ε)).val k).val h =
    (denominator K ε s)⁻¹ *
      ((evaluate K A P I J' ε p' (evaluationUnit K ε s) φ' :
        compactPicture A P I (targetSign ε)).val k).val h
  exact congrArg ((denominator K ε s)⁻¹ * ·) hv

private theorem section_locallyConstant
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (ε : Sign) (s : ℂ) (f : sectionSpace A P ε s) : IsLocallyConstant f.val := by
  obtain ⟨J, hJ⟩ := f.property.2
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hc : Continuous (fun y : G => g⁻¹ * y) := continuous_const.mul continuous_id
  have hmem : ∀ᶠ y : G in nhds g, g⁻¹ * y ∈ J :=
    hc.continuousAt.preimage_mem_nhds (by simpa using J.isOpen.mem_nhds J.one_mem)
  filter_upwards [hmem] with y hy
  have he := congrFun (hJ (g⁻¹ * y) hy) g
  simpa [vectorRightTranslation] using he

theorem standardIntegral_integrand_locallyConstant
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (ε : Sign) (s : ℂ)
    (φ : compactPicture A P I (sourceSign ε)) (g : G) (h : H) :
    IsLocallyConstant (fun x : K =>
      ((compactTrivialization A P I (sourceSign ε) (sourceParameter ε s) φ).val
        (kernelW K A ε * (A.upperRoot (Multiplicative.ofAdd x) : G) * g)).val h) := by
  let f := compactTrivialization A P I (sourceSign ε) (sourceParameter ε s) φ
  have hl := (section_locallyConstant K A P _ _ f).comp (fun v : InducedModule P => v.val h)
  apply hl.comp_continuous
  exact (continuous_const.mul (continuous_subtype_val.comp
    (A.upperRoot_continuous.comp continuous_ofAdd))).mul continuous_const

theorem standardIntegral_integrableOn_compact
    (A : LocalBorelData (K := K) (G := G) T) (P : Polarization T)
    (I : IwasawaData A) (μ : Measure K) [μ.IsAddHaarMeasure]
    (ε : Sign) (s : ℂ) (φ : compactPicture A P I (sourceSign ε))
    (g : G) (h : H) (C : Set K) (hC : IsCompact C) (hmC : MeasurableSet C) :
    IntegrableOn (fun x : K =>
      ((compactTrivialization A P I (sourceSign ε) (sourceParameter ε s) φ).val
        (kernelW K A ε * (A.upperRoot (Multiplicative.ofAdd x) : G) * g)).val h) C μ := by
  exact (standardIntegral_integrand_locallyConstant K A P I ε s φ g h).continuous.continuousOn.integrableOn_compact' hC hmC

end
end DedekindZetaZeroFree.KPRankOneShellContinuation

section

namespace DedekindZetaZeroFree.KPRankOneShellContinuation

open scoped Valued
open MeasureTheory ValuativeRel KPLocalPrincipalSeries KPRankOneRootParameter
open KPLocalPrincipalSeries KPRankOneRootParameter KPLocalStoneVonNeumann

noncomputable section

variable (K : Type*) [Field K] [CharZero K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [MeasurableSpace K] [BorelSpace K]
variable {G H D : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CommGroup D] [Finite D]
variable {T : LocalHeisenbergData H D}

private theorem r_diff : Differentiable ℂ (r K) := by
  unfold r
  fun_prop

 theorem eval_diff (ε : Sign) :
    Differentiable ℂ (fun s => (evaluationUnit K ε s : ℂ)) := by
  cases ε with
  | plus =>
    change Differentiable ℂ (r K)
    exact r_diff K
  | minus =>
    change Differentiable ℂ (fun s => (r K s)⁻¹)
    exact (r_diff K).inv (fun s => Complex.exp_ne_zero _)

 theorem denom_diff (ε : Sign) :
    Differentiable ℂ (denominator K ε) := by
  cases ε with
  | plus =>
    unfold denominator t r
    simp only [if_pos rfl, if_true]
    fun_prop
  | minus =>
    unfold denominator
    simp only [reduceCtorEq, if_false]
    apply Differentiable.sub (differentiable_const _)
    apply Differentiable.mul (differentiable_const _)
    apply Differentiable.pow
    exact (r_diff K).inv (fun s => Complex.exp_ne_zero _)

end
end DedekindZetaZeroFree.KPRankOneShellContinuation

end
