module

public import DedekindZetaZeroFree.Adeles.RestrictedProduct.LocalTopology
public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms

@[expose] public section

section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace DedekindZetaZeroFree.KPChamberRowProducts

open NumberField IsDedekindDomain Matrix
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def finiteRowFactor (r : Fin 2 → F)
    (A : GL (Fin 2) (AdeleRing (RingOfIntegers F) F))
    (v : HeightOneSpectrum (RingOfIntegers F)) : ℝ :=
  let ev := (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)
  let A_v := GeneralLinearGroup.map ev A
  let r_v := fun i => (algebraMap F (v.adicCompletion F)) (r i)
  (max (‖∑ i : Fin 2, r_v i * (A_v : Matrix (Fin 2) (Fin 2) _) i 0‖)
    (‖∑ i : Fin 2, r_v i * (A_v : Matrix (Fin 2) (Fin 2) _) i 1‖)) /
    Real.sqrt ‖(GeneralLinearGroup.det A_v : v.adicCompletion F)‖

def infiniteRowFactor (r : Fin 2 → F)
    (A : GL (Fin 2) (AdeleRing (RingOfIntegers F) F))
    (v : InfinitePlace F) : ℝ :=
  let ev := (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v).comp
    (RingHom.fst _ _)
  let A_v := GeneralLinearGroup.map ev A
  let r_v := fun i => (algebraMap F v.Completion) (r i)
  (Real.sqrt ((‖∑ i : Fin 2, r_v i * (A_v : Matrix (Fin 2) (Fin 2) _) i 0‖)^2 +
      (‖∑ i : Fin 2, r_v i * (A_v : Matrix (Fin 2) (Fin 2) _) i 1‖)^2) /
    Real.sqrt ‖(GeneralLinearGroup.det A_v : v.Completion)‖) ^
      (if NumberField.InfinitePlace.IsReal v then 1 else 2)

def rowProduct (r : Fin 2 → F)
    (A : GL (Fin 2) (AdeleRing (RingOfIntegers F) F)) : ℝ :=
  (∏ v : InfinitePlace F, infiniteRowFactor F r A v) *
    ∏ᶠ v : HeightOneSpectrum (RingOfIntegers F), finiteRowFactor F r A v

 def mx {K : Type*} [NormedField K] (r : Fin 2 → K) : ℝ := max ‖r 0‖ ‖r 1‖
 def en {K : Type*} [NormedField K] (r : Fin 2 → K) : ℝ := Real.sqrt (‖r 0‖ ^ 2 + ‖r 1‖ ^ 2)
 def eb {K : Type*} [NormedField K] (A : GL (Fin 2) K) : ℝ :=
  max 1 (max (max ‖A 0 0‖ ‖A 0 1‖) (max ‖A 1 0‖ ‖A 1 1‖))
private lemma eb_one {K : Type*} [NormedField K] (A : GL (Fin 2) K) : 1 ≤ eb A := le_max_left _ _
private lemma eb_entry {K : Type*} [NormedField K] (A : GL (Fin 2) K) (i j : Fin 2) : ‖A i j‖ ≤ eb A := by
  fin_cases i <;> fin_cases j <;> unfold eb <;> bound
private lemma mx_nonneg {K : Type*} [NormedField K] (r : Fin 2 → K) : 0 ≤ mx r := (norm_nonneg _).trans (le_max_left _ _)
private lemma mx_le_en {K : Type*} [NormedField K] (r : Fin 2 → K) : mx r ≤ en r := by
  apply max_le <;> apply Real.le_sqrt_of_sq_le <;> nlinarith [sq_nonneg ‖r 0‖, sq_nonneg ‖r 1‖]
private lemma en_le_two_mx {K : Type*} [NormedField K] (r : Fin 2 → K) : en r ≤ 2 * mx r := by
  have h0 : ‖r 0‖ ≤ mx r := le_max_left _ _
  have h1 : ‖r 1‖ ≤ mx r := le_max_right _ _
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact mul_nonneg (by norm_num) (mx_nonneg r)
  · nlinarith [norm_nonneg (r 0), norm_nonneg (r 1), mx_nonneg r]
private lemma mx_mul {K : Type*} [NormedField K] (r : Fin 2 → K) (A : GL (Fin 2) K) :
    mx (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) ≤ 2 * eb A * mx r := by
  suffices h : ∀ j : Fin 2, ‖(r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) j‖ ≤ 2 * eb A * mx r from max_le (h 0) (h 1)
  intro j
  dsimp [vecMul, dotProduct]
  rw [Fin.sum_univ_two]
  all_goals
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    have h0 : ‖r 0‖ ≤ mx r := le_max_left _ _
    have h1 : ‖r 1‖ ≤ mx r := le_max_right _ _
    have he0 := eb_entry A 0 j
    have he1 := eb_entry A 1 j
    have hb : 0 ≤ eb A := (by norm_num : (0:ℝ) ≤ 1).trans (eb_one A)
    nlinarith [mul_le_mul h0 he0 (norm_nonneg _) (mx_nonneg r), mul_le_mul h1 he1 (norm_nonneg _) (mx_nonneg r)]
private lemma mx_mul_ultra {K : Type*} [NormedField K] [IsUltrametricDist K]
    (r : Fin 2 → K) (A : GL (Fin 2) K) :
    mx (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) ≤ eb A * mx r := by
  apply max_le <;> dsimp [vecMul, dotProduct] <;> rw [Fin.sum_univ_two]
  all_goals
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    apply max_le <;> rw [norm_mul]
    · exact (mul_le_mul (show ‖r 0‖ ≤ mx r from le_max_left _ _) (eb_entry A 0 _) (norm_nonneg _) (mx_nonneg r)).trans_eq (mul_comm _ _)
    · exact (mul_le_mul (show ‖r 1‖ ≤ mx r from le_max_right _ _) (eb_entry A 1 _) (norm_nonneg _) (mx_nonneg r)).trans_eq (mul_comm _ _)
private lemma en_mul {K : Type*} [NormedField K] (r : Fin 2 → K) (A : GL (Fin 2) K) :
    en (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) ≤ 4 * eb A * en r := by
  calc
    _ ≤ 2 * mx (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) := en_le_two_mx _
    _ ≤ 2 * (2 * eb A * mx r) := mul_le_mul_of_nonneg_left (mx_mul r A) (by norm_num)
    _ ≤ 4 * eb A * en r := by nlinarith [mul_le_mul_of_nonneg_left (mx_le_en r) (show 0 ≤ eb A by linarith [eb_one A])]
 def dn {K : Type*} [NormedField K] (A : GL (Fin 2) K) : ℝ := Real.sqrt ‖(GeneralLinearGroup.det A : K)‖
private lemma dn_pos {K : Type*} [NormedField K] (A : GL (Fin 2) K) : 0 < dn A := Real.sqrt_pos.mpr (norm_pos_iff.mpr (Units.ne_zero _))
 def cc {K : Type*} [NormedField K] (A : GL (Fin 2) K) : ℝ := max 1 (max (eb A / dn A) (eb A⁻¹ * dn A))
private lemma cc_one {K : Type*} [NormedField K] (A : GL (Fin 2) K) : 1 ≤ cc A := le_max_left _ _
private lemma mx_bounds {K : Type*} [NormedField K] [IsUltrametricDist K]
    (r : Fin 2 → K) (A : GL (Fin 2) K) :
    mx r ≤ cc A * (mx (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) / dn A) ∧
    mx (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) / dn A ≤ cc A * mx r := by
  have h1 : eb A / dn A ≤ cc A := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : eb A⁻¹ * dn A ≤ cc A := (le_max_right _ _).trans (le_max_right _ _)
  have hp := dn_pos A
  constructor
  · have hh := mx_mul_ultra (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) A⁻¹
    rw [vecMul_vecMul, A.mul_inv, vecMul_one] at hh
    calc
      _ ≤ eb A⁻¹ * mx (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) := hh
      _ = (eb A⁻¹ * dn A) * (mx (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) / dn A) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 (div_nonneg (mx_nonneg _) hp.le)
  · calc
      _ ≤ eb A * mx r / dn A := div_le_div_of_nonneg_right (mx_mul_ultra r A) hp.le
      _ = (eb A / dn A) * mx r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (mx_nonneg r)
private lemma en_nonneg {K : Type*} [NormedField K] (r : Fin 2 → K) : 0 ≤ en r := Real.sqrt_nonneg _
private lemma en_bounds {K : Type*} [NormedField K]
    (r : Fin 2 → K) (A : GL (Fin 2) K) :
    en r ≤ (4 * cc A) * (en (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) / dn A) ∧
    en (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) / dn A ≤ (4 * cc A) * en r := by
  have h1 : eb A / dn A ≤ cc A := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : eb A⁻¹ * dn A ≤ cc A := (le_max_right _ _).trans (le_max_right _ _)
  have hp := dn_pos A
  constructor
  · have hh := en_mul (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) A⁻¹
    rw [vecMul_vecMul, A.mul_inv, vecMul_one] at hh
    calc
      _ ≤ 4 * eb A⁻¹ * en (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) := hh
      _ = (4 * (eb A⁻¹ * dn A)) * (en (r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) / dn A) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num)) (div_nonneg (en_nonneg _) hp.le)
  · calc
      _ ≤ 4 * eb A * en r / dn A := div_le_div_of_nonneg_right (en_mul r A) hp.le
      _ = (4 * (eb A / dn A)) * en r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) (en_nonneg r)
private lemma cc_good {K : Type*} [NormedField K] (A : GL (Fin 2) K)
    (h : ∀ i j, ‖A i j‖ ≤ 1) (hi : ∀ i j, ‖A⁻¹ i j‖ ≤ 1)
    (hd : ‖(GeneralLinearGroup.det A : K)‖ = 1) : cc A = 1 := by
  have he : eb A = 1 := max_eq_left (max_le (max_le (h 0 0) (h 0 1)) (max_le (h 1 0) (h 1 1)))
  have hei : eb A⁻¹ = 1 := max_eq_left (max_le (max_le (hi 0 0) (hi 0 1)) (max_le (hi 1 0) (hi 1 1)))
  have hdn : dn A = 1 := by unfold dn; rw [hd, Real.sqrt_one]
  simp only [cc, he, hei, hdn, div_one, mul_one, max_self]
private lemma continuous_cc {K : Type*} [NormedField K] : Continuous (cc (K := K)) := by
  have hentry (i j : Fin 2) : Continuous (fun A : GL (Fin 2) K => ‖A i j‖) :=
    (Units.continuous_val.matrix_elem i j).norm
  have he : Continuous (eb (K := K)) := continuous_const.max (((hentry 0 0).max (hentry 0 1)).max ((hentry 1 0).max (hentry 1 1)))
  have hd : Continuous (dn (K := K)) := by unfold dn; fun_prop
  exact continuous_const.max ((he.div hd (fun A => ne_of_gt (dn_pos A))).max ((he.comp continuous_inv).mul hd))

 abbrev V := HeightOneSpectrum (RingOfIntegers F)
 abbrev AG := GL (Fin 2) (AdeleRing (RingOfIntegers F) F)
 def fe (v : V F) : AdeleRing (RingOfIntegers F) F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)
 def ae (v : InfinitePlace F) : AdeleRing (RingOfIntegers F) F →+* v.Completion :=
  (Pi.evalRingHom _ v).comp (RingHom.fst _ _)
 def fc (A : AG F) (v : V F) : ℝ := cc (GeneralLinearGroup.map (fe F v) A)
 def ac (A : AG F) (v : InfinitePlace F) : ℝ :=
  (4 * cc (GeneralLinearGroup.map (ae F v) A)) ^ (if v.IsReal then 1 else 2)
private lemma finite_one (r : Fin 2 → F) (v : V F) :
    finiteRowFactor F r 1 v = mx (fun i => algebraMap F (v.adicCompletion F) (r i)) := by
  simp [finiteRowFactor, mx, Fin.sum_univ_two, Matrix.one_apply]
private lemma infinite_one (r : Fin 2 → F) (v : InfinitePlace F) :
    infiniteRowFactor F r 1 v = en (fun i => algebraMap F v.Completion (r i)) ^ (if v.IsReal then 1 else 2) := by
  simp [infiniteRowFactor, en, Fin.sum_univ_two, Matrix.one_apply]
private lemma finite_nonneg (r : Fin 2 → F) (A : AG F) (v : V F) : 0 ≤ finiteRowFactor F r A v := by
  exact div_nonneg ((norm_nonneg _).trans (le_max_left _ _)) (Real.sqrt_nonneg _)
private lemma infinite_nonneg (r : Fin 2 → F) (A : AG F) (v : InfinitePlace F) : 0 ≤ infiniteRowFactor F r A v := by
  exact pow_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) _
private lemma finite_bounds (r : Fin 2 → F) (A : AG F) (v : V F) :
    finiteRowFactor F r 1 v ≤ fc F A v * finiteRowFactor F r A v ∧
    finiteRowFactor F r A v ≤ fc F A v * finiteRowFactor F r 1 v := by
  rw [finite_one]
  exact mx_bounds _ _
private lemma infinite_bounds (r : Fin 2 → F) (A : AG F) (v : InfinitePlace F) :
    infiniteRowFactor F r 1 v ≤ ac F A v * infiniteRowFactor F r A v ∧
    infiniteRowFactor F r A v ≤ ac F A v * infiniteRowFactor F r 1 v := by
  rw [infinite_one]
  change en (fun i => algebraMap F v.Completion (r i)) ^ (if v.IsReal then 1 else 2) ≤ ac F A v * (en ((fun i => algebraMap F v.Completion (r i)) ᵥ* (GeneralLinearGroup.map (ae F v) A : Matrix (Fin 2) (Fin 2) v.Completion)) / dn (GeneralLinearGroup.map (ae F v) A)) ^ (if v.IsReal then 1 else 2) ∧ (en ((fun i => algebraMap F v.Completion (r i)) ᵥ* (GeneralLinearGroup.map (ae F v) A : Matrix (Fin 2) (Fin 2) v.Completion)) / dn (GeneralLinearGroup.map (ae F v) A)) ^ (if v.IsReal then 1 else 2) ≤ ac F A v * en (fun i => algebraMap F v.Completion (r i)) ^ (if v.IsReal then 1 else 2)
  have h := en_bounds (fun i => algebraMap F v.Completion (r i)) (GeneralLinearGroup.map (ae F v) A)
  constructor
  · simpa only [ac, infiniteRowFactor, en, dn, ae, vecMul, dotProduct, ← mul_pow] using pow_le_pow_left₀ (en_nonneg _) h.1 (if v.IsReal then 1 else 2)
  · simpa only [ac, infiniteRowFactor, en, dn, ae, vecMul, dotProduct, ← mul_pow] using pow_le_pow_left₀ (div_nonneg (en_nonneg _) (dn_pos _).le) h.2 (if v.IsReal then 1 else 2)
private lemma finite_baseline_support (r : Fin 2 → F) (hr : r ≠ 0) :
    ∀ᶠ v : V F in Filter.cofinite, finiteRowFactor F r 1 v = 1 := by
  have hn (a : F) (ha : a ≠ 0) : ∀ᶠ v : V F in Filter.cofinite,
      ‖algebraMap F (v.adicCompletion F) a‖ = 1 := by
    exact Filter.eventually_cofinite.mpr
      (Function.HasFiniteMulSupport.fun_comp_of_injective
        FinitePlace.equivHeightOneSpectrum.symm.injective
        (FinitePlace.hasFiniteMulSupport ha))
  have hb (a : F) : ∀ᶠ v : V F in Filter.cofinite,
      ‖algebraMap F (v.adicCompletion F) a‖ ≤ 1 := by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hn a ha).mono (fun _ h => h.le)
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := Function.ne_iff.mp hr
  filter_upwards [hb (r 0), hb (r 1), hn (r i) hi] with v h0 h1 hi
  rw [finite_one]
  apply le_antisymm (max_le h0 h1)
  fin_cases i
  · rw [← hi]; exact le_max_left _ _
  · rw [← hi]; exact le_max_right _ _
private lemma integral_norm (v : V F) (x : v.adicCompletion F)
    (h : x ∈ v.adicCompletionIntegers F) : ‖x‖ ≤ 1 := by
  rw [FinitePlace.norm_def]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).mpr h
 def gd (S : Finset (V F)) (B : AG F) : Prop :=
  (∀ i j v, v ∉ S → (B i j).2 v ∈ v.adicCompletionIntegers F) ∧
  (∀ i j v, v ∉ S → (B⁻¹ i j).2 v ∈ v.adicCompletionIntegers F) ∧
  (∀ v, v ∉ S → ((GeneralLinearGroup.det B : AdeleRing (RingOfIntegers F) F).2 v) ∈ v.adicCompletionIntegers F) ∧
  (∀ v, v ∉ S → ((GeneralLinearGroup.det B⁻¹ : AdeleRing (RingOfIntegers F) F).2 v) ∈ v.adicCompletionIntegers F)
private lemma gd_cc (S : Finset (V F)) (B : AG F) (h : gd F S B) (v : V F) (hv : v ∉ S) : fc F B v = 1 := by
  apply cc_good
  · intro i j; exact integral_norm F v _ (h.1 i j v hv)
  · intro i j; exact integral_norm F v _ (h.2.1 i j v hv)
  · have hd := integral_norm F v _ (h.2.2.1 v hv)
    have hi := integral_norm F v _ (h.2.2.2 v hv)
    have he : ‖(GeneralLinearGroup.det (GeneralLinearGroup.map (fe F v) B) : v.adicCompletion F)‖ *
        ‖(GeneralLinearGroup.det (GeneralLinearGroup.map (fe F v) B⁻¹) : v.adicCompletion F)‖ = 1 := by
      rw [← norm_mul]
      have hh := (GeneralLinearGroup.det (GeneralLinearGroup.map (fe F v) B)).mul_inv
      simpa [← Units.val_mul, ← map_mul] using congrArg (fun x : v.adicCompletion F => ‖x‖) hh
    change ‖(GeneralLinearGroup.det (GeneralLinearGroup.map (fe F v) B) : v.adicCompletion F)‖ ≤ 1 at hd
    change ‖(GeneralLinearGroup.det (GeneralLinearGroup.map (fe F v) B⁻¹) : v.adicCompletion F)‖ ≤ 1 at hi
    nlinarith [norm_nonneg (GeneralLinearGroup.det (GeneralLinearGroup.map (fe F v) B) : v.adicCompletion F)]
private lemma exists_gd (A : AG F) : ∃ S, gd F S A := by
  have h : ∀ᶠ v : V F in Filter.cofinite,
      (∀ i j, (A i j).2 v ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, (A⁻¹ i j).2 v ∈ v.adicCompletionIntegers F) ∧
      (GeneralLinearGroup.det A : AdeleRing (RingOfIntegers F) F).2 v ∈ v.adicCompletionIntegers F ∧
      (GeneralLinearGroup.det A⁻¹ : AdeleRing (RingOfIntegers F) F).2 v ∈ v.adicCompletionIntegers F := by
    exact (Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => (A i j).2.property))).and
      ((Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => (A⁻¹ i j).2.property))).and
        ((GeneralLinearGroup.det A : AdeleRing (RingOfIntegers F) F).2.property.and
          (GeneralLinearGroup.det A⁻¹ : AdeleRing (RingOfIntegers F) F).2.property))
  obtain ⟨S, hS⟩ := Filter.eventually_cofinite.mp h |>.exists_finset
  refine ⟨S, ?_⟩
  have hh (v : V F) (hv : v ∉ S) := not_not.mp (show ¬ ¬ _ from fun hn => hv ((hS v).mpr hn))
  exact ⟨fun i j v hv => (hh v hv).1 i j, fun i j v hv => (hh v hv).2.1 i j,
    fun v hv => (hh v hv).2.2.1, fun v hv => (hh v hv).2.2.2⟩

private lemma finite_support (r : Fin 2 → F) (hr : r ≠ 0) (A : AG F) :
    (finiteRowFactor F r A).HasFiniteMulSupport := by
  obtain ⟨S, hS⟩ := exists_gd F A
  apply Filter.eventually_cofinite.mp
  filter_upwards [finite_baseline_support F r hr, (S.finite_toSet.compl_mem_cofinite)] with v hv hvS
  have h := finite_bounds F r A v
  rw [gd_cc F S A hS v hvS, hv, one_mul, one_mul] at h
  exact le_antisymm h.2 h.1
private lemma continuous_fc (v : V F) : Continuous (fun B : AG F => fc F B v) := by
  apply continuous_cc.comp
  apply Units.continuous_iff.mpr
  constructor
  · apply continuous_matrix
    intro i j
    exact (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (Units.continuous_val.matrix_elem i j))
  · apply continuous_matrix
    intro i j
    exact (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp (Units.continuous_coe_inv.matrix_elem i j))
private lemma continuous_ac (v : InfinitePlace F) : Continuous (fun B : AG F => ac F B v) := by
  have h : Continuous (fun B : AG F => GeneralLinearGroup.map (ae F v) B) := by
    apply Units.continuous_iff.mpr
    constructor
    · apply continuous_matrix
      intro i j
      exact (continuous_apply v).comp (continuous_fst.comp (Units.continuous_val.matrix_elem i j))
    · apply continuous_matrix
      intro i j
      exact (continuous_apply v).comp (continuous_fst.comp (Units.continuous_coe_inv.matrix_elem i j))
  exact (continuous_const.mul (continuous_cc.comp h)).pow _
private lemma gd_open (S : Finset (V F)) : IsOpen {B : AG F | gd F S B} := by
  have hopen : IsOpen {a : FiniteAdeleRing (RingOfIntegers F) F |
      ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_imp_mem (KPAdelicTopology.completionIntegers_isOpen F)
  have he (i j : Fin 2) : IsOpen {B : AG F | ∀ v, v ∉ S → (B i j).2 v ∈ v.adicCompletionIntegers F} :=
    hopen.preimage (continuous_snd.comp (Units.continuous_val.matrix_elem i j))
  have hei (i j : Fin 2) : IsOpen {B : AG F | ∀ v, v ∉ S → (B⁻¹ i j).2 v ∈ v.adicCompletionIntegers F} :=
    hopen.preimage (continuous_snd.comp (Units.continuous_coe_inv.matrix_elem i j))
  have hd : Continuous (fun B : AG F => (GeneralLinearGroup.det B : AdeleRing (RingOfIntegers F) F)) := by
    simp_rw [GeneralLinearGroup.val_det_apply]
    exact Units.continuous_val.matrix_det
  have ho := hopen.preimage (continuous_snd.comp hd)
  have hoi := hopen.preimage (continuous_snd.comp (hd.comp continuous_inv))
  unfold gd
  simp only [Set.setOf_and, Set.setOf_forall]
  simpa only [Set.setOf_forall, Function.comp_def, Set.preimage_setOf_eq, Set.preimage_iInter] using
    (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite (he i)).inter
      ((isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite (hei i)).inter (ho.inter hoi))
 def gc (S : Finset (V F)) (B : AG F) : ℝ := (∏ v : InfinitePlace F, ac F B v) * ∏ v ∈ S, fc F B v
private lemma gc_one (S : Finset (V F)) (B : AG F) : 1 ≤ gc F S B := by
  have hf (v : V F) : 1 ≤ fc F B v := cc_one _
  have ha (v : InfinitePlace F) : 1 ≤ ac F B v := one_le_pow₀ (by linarith [cc_one (GeneralLinearGroup.map (ae F v) B)])
  exact one_le_mul_of_one_le_of_one_le
    (Finset.one_le_prod₀ (fun v _ => ha v)) (Finset.one_le_prod₀ (fun v _ => hf v))
private lemma continuous_gc (S : Finset (V F)) : Continuous (gc F S) :=
  (continuous_finsetProd _ (fun v _ => continuous_ac F v)).mul
    (continuous_finsetProd _ (fun v _ => continuous_fc F v))
private lemma global_bounds (S : Finset (V F)) (B : AG F) (hB : gd F S B)
    (r : Fin 2 → F) (hr : r ≠ 0) :
    rowProduct F r 1 ≤ gc F S B * rowProduct F r B ∧
    rowProduct F r B ≤ gc F S B * rowProduct F r 1 := by
  have hf : (fc F B).HasFiniteMulSupport := by
    apply Set.Finite.subset S.finite_toSet
    intro v hv
    by_contra h
    exact hv (gd_cc F S B hB v h)
  have he : ∏ᶠ v, fc F B v = ∏ v ∈ S, fc F B v := finprod_eq_prod_of_mulSupport_subset _ (by
    intro v hv
    by_contra h
    exact hv (gd_cc F S B hB v h))
  have hs := finite_support F r hr B
  have hs1 := finite_support F r hr 1
  have hfc (v : V F) : 0 ≤ fc F B v := le_trans (by norm_num) (cc_one _)
  have hac (v : InfinitePlace F) : 0 ≤ ac F B v := pow_nonneg (by linarith [cc_one (GeneralLinearGroup.map (ae F v) B)]) _
  have hn : 0 ≤ ∏ᶠ v, finiteRowFactor F r B v := finprod_nonneg (finite_nonneg F r B)
  have hn1 : 0 ≤ ∏ᶠ v, finiteRowFactor F r 1 v := finprod_nonneg (finite_nonneg F r 1)
  have hna : 0 ≤ ∏ v : InfinitePlace F, infiniteRowFactor F r B v := Finset.prod_nonneg (fun v _ => infinite_nonneg F r B v)
  have hna1 : 0 ≤ ∏ v : InfinitePlace F, infiniteRowFactor F r 1 v := Finset.prod_nonneg (fun v _ => infinite_nonneg F r 1 v)
  have hb1 : ∏ᶠ v, finiteRowFactor F r 1 v ≤ (∏ v ∈ S, fc F B v) * ∏ᶠ v, finiteRowFactor F r B v := by
    rw [← he, ← finprod_mul_distrib hf hs]
    exact finprod_le_finprod₀ hs1 (finite_nonneg F r 1) (hf.mul hs) (fun v => (finite_bounds F r B v).1)
  have hb2 : ∏ᶠ v, finiteRowFactor F r B v ≤ (∏ v ∈ S, fc F B v) * ∏ᶠ v, finiteRowFactor F r 1 v := by
    rw [← he, ← finprod_mul_distrib hf hs1]
    exact finprod_le_finprod₀ hs (finite_nonneg F r B) (hf.mul hs1) (fun v => (finite_bounds F r B v).2)
  have ha1 : (∏ v : InfinitePlace F, infiniteRowFactor F r 1 v) ≤ (∏ v : InfinitePlace F, ac F B v) * ∏ v : InfinitePlace F, infiniteRowFactor F r B v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ => infinite_nonneg F r 1 v) (fun v _ => (infinite_bounds F r B v).1)
  have ha2 : (∏ v : InfinitePlace F, infiniteRowFactor F r B v) ≤ (∏ v : InfinitePlace F, ac F B v) * ∏ v : InfinitePlace F, infiniteRowFactor F r 1 v := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun v _ => infinite_nonneg F r B v) (fun v _ => (infinite_bounds F r B v).2)
  constructor
  · simpa only [gc, rowProduct, mul_mul_mul_comm] using mul_le_mul ha1 hb1 hn1 (mul_nonneg (Finset.prod_nonneg (fun v _ => hac v)) hna)
  · simpa only [gc, rowProduct, mul_mul_mul_comm] using mul_le_mul ha2 hb2 hn (mul_nonneg (Finset.prod_nonneg (fun v _ => hac v)) hna1)

theorem local_rowProduct_bounds
    (A : GL (Fin 2) (AdeleRing (RingOfIntegers F) F)) :
    ∃ U : Set (GL (Fin 2) (AdeleRing (RingOfIntegers F) F)),
      IsOpen U ∧ A ∈ U ∧ ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
        ∀ (r : Fin 2 → F), r ≠ 0 → ∀ B ∈ U,
          m * rowProduct F r 1 ≤ rowProduct F r B ∧
            rowProduct F r B ≤ M * rowProduct F r 1 := by
  obtain ⟨S, hS⟩ := exists_gd F A
  let C := gc F S A + 1
  have hC : 1 ≤ C := by dsimp [C]; linarith [gc_one F S A]
  have hCp : 0 < C := lt_of_lt_of_le (by norm_num) hC
  let U : Set (AG F) := {B | gd F S B} ∩ {B | gc F S B < C}
  refine ⟨U, (gd_open F S).inter (isOpen_lt (continuous_gc F S) continuous_const),
    ⟨hS, by dsimp [C]; linarith⟩, C⁻¹, C, inv_pos.mpr hCp, ?_, ?_⟩
  · exact (inv_le_one_of_one_le₀ hC).trans hC
  · intro r hr B hB
    have h := global_bounds F S B hB.1 r hr
    have hn : 0 ≤ rowProduct F r B := mul_nonneg
      (Finset.prod_nonneg (fun v _ => infinite_nonneg F r B v))
      (finprod_nonneg (finite_nonneg F r B))
    have hn1 : 0 ≤ rowProduct F r 1 := mul_nonneg
      (Finset.prod_nonneg (fun v _ => infinite_nonneg F r 1 v))
      (finprod_nonneg (finite_nonneg F r 1))
    constructor
    · have hh : rowProduct F r 1 ≤ C * rowProduct F r B := h.1.trans (mul_le_mul_of_nonneg_right hB.2.le hn)
      exact (inv_mul_le_iff₀ hCp).mpr hh
    · exact h.2.trans (mul_le_mul_of_nonneg_right hB.2.le hn1)

end DedekindZetaZeroFree.KPChamberRowProducts

end

end

section

namespace DedekindZetaZeroFree.KPChamberRowProducts

open Matrix

noncomputable instance projectiveTopology
    (n : Type*) [Fintype n] [DecidableEq n]
    (R : Type*) [CommRing R] [TopologicalSpace R] :
    TopologicalSpace (ProjGenLinGroup n R) := by
  unfold ProjGenLinGroup
  infer_instance

theorem projective_mk_isOpenMap
    (n : Type*) [Fintype n] [DecidableEq n]
    (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    IsOpenMap (ProjGenLinGroup.mk : GL n R → ProjGenLinGroup n R) := by
  change IsOpenMap (QuotientGroup.mk : GL n R → GL n R ⧸ Subgroup.center (GL n R))
  exact QuotientGroup.isOpenMap_coe

end DedekindZetaZeroFree.KPChamberRowProducts

end

section

namespace DedekindZetaZeroFree.KPChamberRowProducts

theorem compact_bounds_of_local
    {X Y : Type*} [TopologicalSpace Y]
    (base : X → ℝ) (hbase : ∀ x, 0 ≤ base x) (h : X → Y → ℝ)
    (hloc : ∀ y : Y, ∃ U : Set Y, IsOpen U ∧ y ∈ U ∧
      ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
        ∀ x : X, ∀ z ∈ U,
          m * base x ≤ h x z ∧ h x z ≤ M * base x)
    (C : Set Y) (hC : IsCompact C) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ x : X, ∀ y ∈ C,
        m * base x ≤ h x y ∧ h x y ≤ M * base x := by
  classical
  choose U hU hy m M hm hmM hb using hloc
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover U hU
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hy y⟩)
  have hf : ∀ s : Finset Y, ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ i ∈ s, ∀ x : X, ∀ z ∈ U i,
        a * base x ≤ h x z ∧ h x z ≤ b * base x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        exact ⟨1, 1, zero_lt_one, le_rfl, by simp⟩
    | @insert i s hi ih =>
        obtain ⟨a, b, ha, hab, hs⟩ := ih
        refine ⟨min (m i) a, max (M i) b, lt_min (hm i) ha,
          le_trans (min_le_left _ _) (le_trans (hmM i) (le_max_left _ _)), ?_⟩
        intro j hj x z hz
        rcases Finset.mem_insert.mp hj with rfl | hj
        · obtain ⟨hl, hu⟩ := hb j x z hz
          exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_left _ _) (hbase x)) hl,
            le_trans hu (mul_le_mul_of_nonneg_right (le_max_left _ _) (hbase x))⟩
        · obtain ⟨hl, hu⟩ := hs j hj x z hz
          exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (hbase x)) hl,
            le_trans hu (mul_le_mul_of_nonneg_right (le_max_right _ _) (hbase x))⟩
  obtain ⟨a, b, ha, hab, hs⟩ := hf t
  refine ⟨a, b, ha, hab, ?_⟩
  intro x y hyC
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp (ht hyC)
  exact hs i hi x y hyi

end DedekindZetaZeroFree.KPChamberRowProducts

end

section

noncomputable section

namespace DedekindZetaZeroFree.KPChamberHeight

open NumberField IsDedekindDomain Matrix
open scoped Classical

variable (F : Type) [Field F] [NumberField F]

abbrev RatGL := GL (Fin 2) F
abbrev RatPGL := ProjGenLinGroup (Fin 2) F
abbrev Adele := AdeleRing (RingOfIntegers F) F
abbrev AdelGL := GL (Fin 2) (Adele F)
abbrev AdelPGL := ProjGenLinGroup (Fin 2) (Adele F)
abbrev Line := Projectivization F (Fin 2 → F)

noncomputable instance adelPGLTopology : TopologicalSpace (AdelPGL F) := by
  unfold AdelPGL ProjGenLinGroup
  infer_instance

noncomputable def rationalDiagonal : RatPGL F →* AdelPGL F :=
  ProjGenLinGroup.map (algebraMap F (Adele F))

 def liftRat (g : RatPGL F) : RatGL F := Quotient.out g
 def liftAdel (g : AdelPGL F) : AdelGL F := Quotient.out g

 theorem row_ne_zero (A : RatGL F) :
    (fun i : Fin 2 => (A : Matrix (Fin 2) (Fin 2) F) 1 i) ≠ 0 := by
  intro h
  have hi := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 1) A.mul_inv
  have hz : ∀ i, (A : Matrix (Fin 2) (Fin 2) F) 1 i = 0 :=
    fun i => congrFun h i
  simpa [Matrix.mul_apply, hz] using hi

noncomputable def bottomRow (g : RatPGL F) : Line F :=
  Projectivization.mk F
    (fun i => ((liftRat F g : Matrix (Fin 2) (Fin 2) F) 1 i))
    (row_ne_zero F (liftRat F g))

def borel : Subgroup (RatPGL F) :=
  Subgroup.closure
    {g | ∃ A : RatGL F, ProjGenLinGroup.mk A = g ∧
      (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}

abbrev BruhatIndex := Quotient (QuotientGroup.rightRel (borel F))

theorem bottomRow_mk (A : RatGL F) :
    bottomRow F (ProjGenLinGroup.mk A) =
      Projectivization.mk F (fun i => (A : Matrix (Fin 2) (Fin 2) F) 1 i)
        (row_ne_zero F A) := by
  have h : ProjGenLinGroup.mk (liftRat F (ProjGenLinGroup.mk A)) =
      ProjGenLinGroup.mk A := Quotient.out_eq _
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  unfold bottomRow
  apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
  refine ⟨u⁻¹, ?_⟩
  funext i
  have hi := congrArg (fun B : RatGL F =>
    (B : Matrix (Fin 2) (Fin 2) F) 1 i) hu
  change (↑u⁻¹ : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 i = _
  have hi' : (liftRat F (ProjGenLinGroup.mk A) : Matrix (Fin 2) (Fin 2) F) 1 i *
      (u : F) = (A : Matrix (Fin 2) (Fin 2) F) 1 i := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.mul_diagonal] using hi
  rw [← hi']
  simp [mul_comm, mul_left_comm, mul_assoc]
private theorem upperTri_mul_row (A G : RatGL F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (fun j => ((A * G : RatGL F) : Matrix (Fin 2) (Fin 2) F) 1 j)
      = (A : Matrix (Fin 2) (Fin 2) F) 1 1 •
        (fun j => (G : Matrix (Fin 2) (Fin 2) F) 1 j) := by
  funext j
  fin_cases j <;>
    simp [GeneralLinearGroup.coe_mul, Matrix.mul_apply, hA, Fin.sum_univ_two]

private theorem upperTri_11_ne_zero (A : RatGL F)
    (hA : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) :
    (A : Matrix (Fin 2) (Fin 2) F) 1 1 ≠ 0 := by
  have hd := GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_two] at hd
  intro h
  exact hd (by rw [hA, h]; ring)

private theorem bottomRow_borel_mul (b x : RatPGL F) (hb : b ∈ borel F) :
    bottomRow F (b * x) = bottomRow F x := by
  refine Subgroup.closure_induction
    (k := {g | ∃ A : RatGL F, ProjGenLinGroup.mk A = g ∧
      (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0})
    (p := fun b _ => ∀ y, bottomRow F (b * y) = bottomRow F y)
    ?_ ?_ ?_ ?_ hb x
  · rintro g ⟨A, rfl, hA⟩ y
    rw [show y = ProjGenLinGroup.mk (liftRat F y) from (Quotient.out_eq y).symm, ← map_mul,
      bottomRow_mk, bottomRow_mk]
    refine (Projectivization.mk_eq_mk_iff F _ _ _ _).2
      ⟨Units.mk0 _ (upperTri_11_ne_zero F A hA), (upperTri_mul_row F A (liftRat F y) hA).symm⟩
  · intro y; simp
  · intro p q _ _ hp hq y
    rw [mul_assoc, hp (q * y), hq y]
  · intro p _ hp y
    have h := hp (p⁻¹ * y)
    rw [← mul_assoc, mul_inv_cancel, one_mul] at h
    exact h.symm

private theorem bottomRow_respect (x y : RatPGL F)
    (h : QuotientGroup.rightRel (borel F) x y) :
    bottomRow F x = bottomRow F y := by
  have hb : y * x⁻¹ ∈ borel F := (QuotientGroup.rightRel_apply).1 h
  have hy : y = (y * x⁻¹) * x := by group
  rw [hy, bottomRow_borel_mul F _ x hb]

theorem rational_bruhat_index :
    ∃ e : BruhatIndex F ≃ Line F,
      ∀ g : RatPGL F, e (Quotient.mk (QuotientGroup.rightRel (borel F)) g) = bottomRow F g := by
  let f : BruhatIndex F → Line F :=
    Quotient.lift (fun g => bottomRow F g) (fun a b h => bottomRow_respect F a b h)
  have hf : ∀ g, f (Quotient.mk (QuotientGroup.rightRel (borel F)) g) = bottomRow F g :=
    fun g => Quotient.lift_mk _ _ g
  have hinj : Function.Injective f := by
    intro x y hxy
    rw [← Quotient.out_eq x, ← Quotient.out_eq y] at hxy
    simp only [hf] at hxy
    have hrow : Projectivization.mk F
        (fun i => (liftRat F (Quotient.out x) : Matrix (Fin 2) (Fin 2) F) 1 i)
        (row_ne_zero F (liftRat F (Quotient.out x))) =
        Projectivization.mk F
        (fun i => (liftRat F (Quotient.out y) : Matrix (Fin 2) (Fin 2) F) 1 i)
        (row_ne_zero F (liftRat F (Quotient.out y))) := by
      have hx' : ProjGenLinGroup.mk (liftRat F (Quotient.out x)) = Quotient.out x := Quotient.out_eq _
      have hy' : ProjGenLinGroup.mk (liftRat F (Quotient.out y)) = Quotient.out y := Quotient.out_eq _
      have e1 : Projectivization.mk F
          (fun i => (liftRat F (Quotient.out x) : Matrix (Fin 2) (Fin 2) F) 1 i)
          (row_ne_zero F (liftRat F (Quotient.out x))) = bottomRow F (Quotient.out x) :=
        (bottomRow_mk F (liftRat F (Quotient.out x))).symm.trans (congrArg (bottomRow F) hx')
      have e2 : Projectivization.mk F
          (fun i => (liftRat F (Quotient.out y) : Matrix (Fin 2) (Fin 2) F) 1 i)
          (row_ne_zero F (liftRat F (Quotient.out y))) = bottomRow F (Quotient.out y) :=
        (bottomRow_mk F (liftRat F (Quotient.out y))).symm.trans (congrArg (bottomRow F) hy')
      exact e1.trans (hxy.trans e2.symm)
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).1 hrow
    have hmem : Quotient.out y * (Quotient.out x)⁻¹ ∈ borel F := by
      let G : RatGL F := liftRat F (Quotient.out x)
      let G' : RatGL F := liftRat F (Quotient.out y)
      have hG : ProjGenLinGroup.mk G = Quotient.out x := Quotient.out_eq _
      have hG' : ProjGenLinGroup.mk G' = Quotient.out y := Quotient.out_eq _
      have hB : ProjGenLinGroup.mk (G' * G⁻¹) = Quotient.out y * (Quotient.out x)⁻¹ := by
        rw [map_mul, map_inv, hG, hG']
      rw [← hB]
      apply Subgroup.subset_closure
      refine ⟨G' * G⁻¹, rfl, ?_⟩
      rw [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      have hrow' : ∀ j, (G' : Matrix (Fin 2) (Fin 2) F) 1 j =
          (a : F)⁻¹ * (G : Matrix (Fin 2) (Fin 2) F) 1 j := by
        intro j
        have hh := congrFun ha j
        simp only [Units.smul_def, Pi.smul_apply, smul_eq_mul] at hh
        rw [← hh, ← mul_assoc, inv_mul_cancel₀ (Units.ne_zero a), one_mul]
      rw [hrow' 0, hrow' 1]
      have hgg : (G : Matrix (Fin 2) (Fin 2) F) 1 0 * (G⁻¹ : Matrix (Fin 2) (Fin 2) F) 0 0
          + (G : Matrix (Fin 2) (Fin 2) F) 1 1 * (G⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
        have hh2 := congrArg (fun M : RatGL F => (M : Matrix (Fin 2) (Fin 2) F) 1 0)
          (mul_inv_cancel G)
        rw [GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          GeneralLinearGroup.coe_one, Matrix.one_apply] at hh2
        norm_num at hh2
        exact hh2
      rw [GeneralLinearGroup.coe_inv]
      linear_combination (a : F)⁻¹ * hgg
    rw [← Quotient.out_eq x, ← Quotient.out_eq y]
    exact Quotient.sound ((QuotientGroup.rightRel_apply).2 hmem)
  have hsurj : Function.Surjective f := by
    intro ℓ
    obtain ⟨r, hr, rfl⟩ : ∃ r hr, Projectivization.mk F r hr = ℓ :=
      ⟨ℓ.rep, ℓ.rep_nonzero, ℓ.mk_rep⟩
    by_cases h1 : r 1 = 0
    · refine ⟨Quotient.mk _ (ProjGenLinGroup.mk
        (GeneralLinearGroup.mkOfDetNeZero !![0, 1; r 0, r 1] ?_)), ?_⟩
      · have h0 : r 0 ≠ 0 := by
          intro h0
          exact hr (by funext i; fin_cases i <;> simp [h1, h0])
        simpa [Matrix.det_fin_two, h1] using h0
      · rw [hf, bottomRow_mk]
        refine (Projectivization.mk_eq_mk_iff F _ _ _ _).2 ⟨1, ?_⟩
        funext i
        fin_cases i <;> simp
    · refine ⟨Quotient.mk _ (ProjGenLinGroup.mk
        (GeneralLinearGroup.mkOfDetNeZero !![1, 0; r 0, r 1] ?_)), ?_⟩
      · simpa [Matrix.det_fin_two] using h1
      · rw [hf, bottomRow_mk]
        refine (Projectivization.mk_eq_mk_iff F _ _ _ _).2 ⟨1, ?_⟩
        funext i
        fin_cases i <;> simp
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun g => ?_⟩
  change f (Quotient.mk (QuotientGroup.rightRel (borel F)) g) = bottomRow F g
  exact hf g

def rowAction {R : Type*} [CommRing R]
    (r : Fin 2 → R) (A : GL (Fin 2) R) (j : Fin 2) : R :=
  ∑ i : Fin 2, r i * (A : Matrix (Fin 2) (Fin 2) R) i j

def infiniteEval (v : InfinitePlace F) : Adele F →+* v.Completion :=
  (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v).comp (RingHom.fst _ _)

def finiteEval (v : HeightOneSpectrum (RingOfIntegers F)) :
    Adele F →+* v.adicCompletion F :=
  (RestrictedProduct.evalRingHom _ v).comp (RingHom.snd _ _)

noncomputable def finiteFactor (r : Fin 2 → F) (A : AdelGL F)
    (v : HeightOneSpectrum (RingOfIntegers F)) : ℝ :=
  let A_v := GeneralLinearGroup.map (finiteEval F v) A
  let r_v := fun i => (algebraMap F (v.adicCompletion F)) (r i)
  (max (‖rowAction r_v A_v 0‖) (‖rowAction r_v A_v 1‖)) /
    Real.sqrt (‖((GeneralLinearGroup.det A_v : (v.adicCompletion F)ˣ) : v.adicCompletion F)‖)

noncomputable def infiniteDegree (v : InfinitePlace F) : ℕ :=
  if NumberField.InfinitePlace.IsReal v then 1 else 2

noncomputable def infiniteFactor (r : Fin 2 → F) (A : AdelGL F)
    (v : InfinitePlace F) : ℝ :=
  let A_v := GeneralLinearGroup.map (infiniteEval F v) A
  let r_v := fun i => (algebraMap F v.Completion) (r i)
  (Real.sqrt (‖rowAction r_v A_v 0‖ ^ 2 + ‖rowAction r_v A_v 1‖ ^ 2) /
    Real.sqrt (‖((GeneralLinearGroup.det A_v : v.Completionˣ) : v.Completion)‖)) ^
      infiniteDegree F v

private theorem eventual_entry (x : Adele F) : ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
    ‖finiteEval F v x‖ ≤ 1 := by
  filter_upwards [FiniteAdeleRing.cofinite_mem_adicCompletionIntegers x.2] with v hv
  rw [FinitePlace.norm_def]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv
  exact_mod_cast (WithZeroMulInt.toNNReal_le_one_iff (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v)).mpr hv
private theorem eventual_unit (x : (Adele F)ˣ) : ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
    ‖finiteEval F v x‖ = 1 := by
  have h := (FiniteAdeleRing.isUnit_iff.mp ((RingHom.snd _ _).isUnit_map x.isUnit)).2
  filter_upwards [h] with v hv
  rw [FinitePlace.norm_def]
  change Valued.v (finiteEval F v (x : Adele F)) = 1 at hv
  rw [hv]
  simp
private theorem row_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (r : Fin 2 → K) (A : GL (Fin 2) K) (hA : ∀ i j, ‖(A : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ∀ j, ‖rowAction r A j‖ ≤ max ‖r 0‖ ‖r 1‖ := by
  intro j
  simp only [rowAction, Fin.sum_univ_two]
  apply (IsUltrametricDist.norm_add_le_max _ _).trans
  apply max_le
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hA 0 j)).trans (le_max_left _ _)
  · rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hA 1 j)).trans (le_max_right _ _)
private theorem row_norm_eq {K : Type*} [NormedField K] [IsUltrametricDist K]
    (r : Fin 2 → K) (A : GL (Fin 2) K)
    (hA : ∀ i j, ‖(A : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hiA : ∀ i j, ‖((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    max ‖rowAction r A 0‖ ‖rowAction r A 1‖ = max ‖r 0‖ ‖r 1‖ := by
  apply le_antisymm (max_le (row_le r A hA 0) (row_le r A hA 1))
  have he : rowAction (rowAction r A) A⁻¹ = r := by
    change ((r ᵥ* (A : Matrix (Fin 2) (Fin 2) K)) ᵥ* ((A⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) = r
    rw [Matrix.vecMul_vecMul, A.mul_inv, Matrix.vecMul_one]
  have h0 := row_le (rowAction r A) A⁻¹ hiA 0
  have h1 := row_le (rowAction r A) A⁻¹ hiA 1
  rw [he] at h0 h1
  exact max_le h0 h1

theorem finiteFactor_eventually_one (r : Fin 2 → F) (hr : r ≠ 0)
    (A : AdelGL F) :
    ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
      finiteFactor F r A v = 1 := by
  have hn (a : F) (ha : a ≠ 0) : ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
      ‖algebraMap F (v.adicCompletion F) a‖ = 1 := by
    exact Filter.eventually_cofinite.mpr
      (Function.HasFiniteMulSupport.fun_comp_of_injective
        FinitePlace.equivHeightOneSpectrum.symm.injective
        (FinitePlace.hasFiniteMulSupport ha))
  have hb (a : F) : ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
      ‖algebraMap F (v.adicCompletion F) a‖ ≤ 1 := by
    by_cases ha : a = 0
    · simp [ha]
    · exact (hn a ha).mono (fun _ h => h.le)
  obtain ⟨i, hi⟩ : ∃ i, r i ≠ 0 := Function.ne_iff.mp hr
  have hm : ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
      max ‖algebraMap F (v.adicCompletion F) (r 0)‖
        ‖algebraMap F (v.adicCompletion F) (r 1)‖ = 1 := by
    filter_upwards [hb (r 0), hb (r 1), hn (r i) hi] with v h0 h1 hi
    apply le_antisymm (max_le h0 h1)
    fin_cases i
    · rw [← hi]; exact le_max_left _ _
    · rw [← hi]; exact le_max_right _ _
  have hA : ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
      ∀ i j, ‖finiteEval F v ((A : Matrix (Fin 2) (Fin 2) (Adele F)) i j)‖ ≤ 1 := by
    exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      eventual_entry F ((A : Matrix (Fin 2) (Fin 2) (Adele F)) i j)))
  have hiA : ∀ᶠ v : HeightOneSpectrum (RingOfIntegers F) in Filter.cofinite,
      ∀ i j, ‖finiteEval F v (((A⁻¹ : AdelGL F) : Matrix (Fin 2) (Fin 2) (Adele F)) i j)‖ ≤ 1 := by
    exact Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j =>
      eventual_entry F (((A⁻¹ : AdelGL F) : Matrix (Fin 2) (Fin 2) (Adele F)) i j)))
  filter_upwards [hm, hA, hiA, eventual_unit F (GeneralLinearGroup.det A)] with v hm hA hiA hd
  unfold finiteFactor
  dsimp only
  have hiAv : ∀ i j, ‖(((GeneralLinearGroup.map (finiteEval F v) A)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j‖ ≤ 1 := by
    rw [← map_inv]
    exact hiA
  rw [row_norm_eq _ _ hA hiAv, hm]
  have hdv : ‖(GeneralLinearGroup.det (GeneralLinearGroup.map (finiteEval F v) A) : v.adicCompletion F)‖ = 1 := by
    change ‖((finiteEval F v).mapMatrix (A : Matrix (Fin 2) (Fin 2) (Adele F))).det‖ = 1
    rw [← RingHom.map_det]
    exact hd
  rw [hdv, Real.sqrt_one, div_one]

noncomputable def rowHeight (r : Fin 2 → F) (A : AdelGL F) : ℝ :=
  (∏ v : InfinitePlace F, infiniteFactor F r A v) *
    ∏ᶠ v : HeightOneSpectrum (RingOfIntegers F), finiteFactor F r A v

noncomputable def height (ℓ : Line F) (g : AdelPGL F) : ℝ :=
  rowHeight F ℓ.rep (liftAdel F g)

private theorem row_smul {K : Type*} [Field K] (f : F →+* K)
    (r : Fin 2 → F) (a : F) (A : GL (Fin 2) K) (i : Fin 2) :
    rowAction (fun j => f ((a • r) j)) A i = f a * rowAction (fun j => f (r j)) A i := by
  simp [rowAction, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
  ring

private theorem finiteFactor_smul (r : Fin 2 → F) (a : F) (A : AdelGL F)
    (v : HeightOneSpectrum (RingOfIntegers F)) :
    finiteFactor F (a • r) A v =
      ‖algebraMap F (v.adicCompletion F) a‖ * finiteFactor F r A v := by
  unfold finiteFactor
  dsimp only
  rw [row_smul, row_smul, norm_mul, norm_mul, ← mul_max_of_nonneg _ _ (norm_nonneg _)]
  ring

private theorem infiniteFactor_smul (r : Fin 2 → F) (a : F) (A : AdelGL F)
    (v : InfinitePlace F) :
    infiniteFactor F (a • r) A v =
      (v a) ^ v.mult * infiniteFactor F r A v := by
  unfold infiniteFactor
  dsimp only
  rw [row_smul, row_smul, norm_mul, norm_mul]
  have he : ∀ b c d : ℝ, (b*c)^2+(b*d)^2 = b^2*(c^2+d^2) := by intros; ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [mul_div_assoc, mul_pow]
  have hn : ‖algebraMap F v.Completion a‖ = v a :=
    InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm a)
  rw [hn]
  rfl

theorem rowHeight_smul (r : Fin 2 → F) (hr : r ≠ 0)
    (a : F) (ha : a ≠ 0) (A : AdelGL F) :
    rowHeight F (a • r) A = rowHeight F r A := by
  have hf : Function.HasFiniteMulSupport (finiteFactor F r A) :=
    Filter.eventually_cofinite.mp (finiteFactor_eventually_one F r hr A)
  have ha' : Function.HasFiniteMulSupport
      (fun v : HeightOneSpectrum (RingOfIntegers F) =>
        ‖algebraMap F (v.adicCompletion F) a‖) :=
    Function.HasFiniteMulSupport.fun_comp_of_injective
      FinitePlace.equivHeightOneSpectrum.symm.injective
      (FinitePlace.hasFiniteMulSupport ha)
  have hp : (∏ v : InfinitePlace F, v a ^ v.mult) *
      (∏ᶠ v : HeightOneSpectrum (RingOfIntegers F),
        ‖algebraMap F (v.adicCompletion F) a‖) = 1 := by
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F))]
    have he : ∀ v : FinitePlace F,
        ‖algebraMap F ((FinitePlace.equivHeightOneSpectrum v).adicCompletion F) a‖ = v a := by
      intro v
      change FinitePlace.equivHeightOneSpectrum.symm (FinitePlace.equivHeightOneSpectrum v) a = v a
      rw [Equiv.symm_apply_apply]
    simp_rw [he]
    exact NumberField.prod_abs_eq_one ha
  unfold rowHeight
  simp_rw [finiteFactor_smul, infiniteFactor_smul]
  rw [Finset.prod_mul_distrib, finprod_mul_distrib ha' hf]
  calc
    _ = ((∏ v : InfinitePlace F, v a ^ v.mult) *
        (∏ᶠ v : HeightOneSpectrum (RingOfIntegers F),
          ‖algebraMap F (v.adicCompletion F) a‖)) *
        ((∏ v : InfinitePlace F, infiniteFactor F r A v) *
          ∏ᶠ v : HeightOneSpectrum (RingOfIntegers F), finiteFactor F r A v) := by ring
    _ = _ := by rw [hp, one_mul]

private theorem row_scalar {K : Type*} [CommRing K]
    (r : Fin 2 → K) (A : GL (Fin 2) K) (u : Kˣ) (i : Fin 2) :
    rowAction r (A * GeneralLinearGroup.scalar (Fin 2) u) i =
      (u : K) * rowAction r A i := by
  simp [rowAction, GeneralLinearGroup.coe_scalar, Matrix.scalar, Matrix.mul_diagonal,
    Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  ring
private theorem det_scalar_norm {K : Type*} [NormedField K]
    (A : GL (Fin 2) K) (u : Kˣ) :
    Real.sqrt ‖((GeneralLinearGroup.det (A * GeneralLinearGroup.scalar (Fin 2) u)) : K)‖ =
      ‖(u : K)‖ * Real.sqrt ‖((GeneralLinearGroup.det A) : K)‖ := by
  simp only [map_mul, GeneralLinearGroup.det_scalar, Fintype.card_fin,
    Units.val_mul, Units.val_pow_eq_pow_val, norm_mul, norm_pow]
  rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  ring
private theorem finite_scalar {F : Type} [Field F] [NumberField F]
    (r : Fin 2 → F) (A : AdelGL F) (u : (Adele F)ˣ)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finiteFactor F r (A * GeneralLinearGroup.scalar (Fin 2) u) v =
      finiteFactor F r A v := by
  unfold finiteFactor
  rw [(GeneralLinearGroup.map _).map_mul, GeneralLinearGroup.map_scalar]
  dsimp only
  rw [row_scalar, row_scalar, det_scalar_norm, norm_mul, norm_mul,
    ← mul_max_of_nonneg _ _ (norm_nonneg _)]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (Units.ne_zero _))
private theorem infinite_scalar {F : Type} [Field F] [NumberField F]
    (r : Fin 2 → F) (A : AdelGL F) (u : (Adele F)ˣ)
    (v : NumberField.InfinitePlace F) :
    infiniteFactor F r (A * GeneralLinearGroup.scalar (Fin 2) u) v =
      infiniteFactor F r A v := by
  unfold infiniteFactor
  rw [(GeneralLinearGroup.map _).map_mul, GeneralLinearGroup.map_scalar]
  dsimp only
  rw [row_scalar, row_scalar, det_scalar_norm, norm_mul, norm_mul]
  have he : ∀ a b c : ℝ, (a*b)^2+(a*c)^2 = a^2*(b^2+c^2) := by intros; ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  rw [mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (Units.ne_zero _))]

theorem rowHeight_scalar_invariant (r : Fin 2 → F) (A B : AdelGL F)
    (h : ProjGenLinGroup.mk A = ProjGenLinGroup.mk B) :
    (∀ v, finiteFactor F r A v = finiteFactor F r B v) ∧
      (∀ v, infiniteFactor F r A v = infiniteFactor F r B v) := by
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp h
  subst B
  exact ⟨fun v => (finite_scalar r A u v).symm,
    fun v => (infinite_scalar r A u v).symm⟩

theorem height_mk (r : Fin 2 → F) (hr : r ≠ 0) (A : AdelGL F) :
    height F (Projectivization.mk F r hr) (ProjGenLinGroup.mk A) =
      rowHeight F r A := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep F r hr
  have hA : ProjGenLinGroup.mk (liftAdel F (ProjGenLinGroup.mk A)) =
      ProjGenLinGroup.mk A := Quotient.out_eq _
  obtain ⟨hfin, hinf⟩ := rowHeight_scalar_invariant F r _ A hA
  have h₁ : rowHeight F r (liftAdel F (ProjGenLinGroup.mk A)) = rowHeight F r A := by
    unfold rowHeight
    rw [Finset.prod_congr rfl (fun i _ => hinf i), finprod_congr hfin]
  unfold height
  rw [← hu]
  change rowHeight F ((u : F) • r) _ = _
  rw [rowHeight_smul F r hr (u : F) u.ne_zero, h₁]

private theorem local_row_ne_zero {K : Type*} [Field K]
    (f : F →+* K) (r : Fin 2 → F) (hr : r ≠ 0) (A : GL (Fin 2) K) :
    rowAction (fun i => f (r i)) A ≠ 0 := by
  intro h
  have he : (fun i => f (r i)) = 0 :=
    Matrix.eq_zero_of_vecMul_eq_zero (GeneralLinearGroup.det_ne_zero A) h
  apply hr
  funext i
  exact f.injective (by simpa using congrFun he i)

private theorem norm_max_pos {K : Type*} [NormedField K]
    (r : Fin 2 → K) (hr : r ≠ 0) : 0 < max ‖r 0‖ ‖r 1‖ := by
  have hn : r 0 ≠ 0 ∨ r 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hr
    funext i
    fin_cases i <;> simp [h]
  rcases hn with hn | hn
  · exact lt_of_lt_of_le (norm_pos_iff.mpr hn) (le_max_left _ _)
  · exact lt_of_lt_of_le (norm_pos_iff.mpr hn) (le_max_right _ _)

private theorem finiteFactor_pos (r : Fin 2 → F) (hr : r ≠ 0) (A : AdelGL F)
    (v : HeightOneSpectrum (RingOfIntegers F)) : 0 < finiteFactor F r A v := by
  unfold finiteFactor
  exact div_pos
    (norm_max_pos _ (local_row_ne_zero F (algebraMap F _) r hr _))
    (Real.sqrt_pos.mpr (norm_pos_iff.mpr (Units.ne_zero _)))

private theorem infiniteFactor_pos (r : Fin 2 → F) (hr : r ≠ 0) (A : AdelGL F)
    (v : InfinitePlace F) : 0 < infiniteFactor F r A v := by
  unfold infiniteFactor
  apply pow_pos
  apply div_pos
  · apply Real.sqrt_pos.mpr
    have hp := norm_max_pos _
      (local_row_ne_zero F (algebraMap F v.Completion) r hr
        (GeneralLinearGroup.map (infiniteEval F v) A))
    have h0 := norm_nonneg
      (rowAction (fun i => (algebraMap F v.Completion) (r i))
        (GeneralLinearGroup.map (infiniteEval F v) A) 0)
    have h1 := norm_nonneg
      (rowAction (fun i => (algebraMap F v.Completion) (r i))
        (GeneralLinearGroup.map (infiniteEval F v) A) 1)
    rcases lt_max_iff.mp hp with h | h <;> nlinarith
  · exact Real.sqrt_pos.mpr (norm_pos_iff.mpr (Units.ne_zero _))

theorem rowHeight_pos (r : Fin 2 → F) (hr : r ≠ 0) (A : AdelGL F) :
    0 < rowHeight F r A := by
  unfold rowHeight
  exact mul_pos (Finset.prod_pos (fun v _ => infiniteFactor_pos F r hr A v))
    (finprod_induction (fun x : ℝ => 0 < x) zero_lt_one
      (fun _ _ => mul_pos) (fun v => finiteFactor_pos F r hr A v))

theorem height_pos (ℓ : Line F) (g : AdelPGL F) : 0 < height F ℓ g := by
  exact rowHeight_pos F ℓ.rep ℓ.rep_nonzero (liftAdel F g)

private theorem fin_one (r : Fin 2 → F) (v : HeightOneSpectrum (RingOfIntegers F)) :
  finiteFactor F r 1 v = max ((FinitePlace.equivHeightOneSpectrum.symm v) (r 0)) ((FinitePlace.equivHeightOneSpectrum.symm v) (r 1)) := by
  simp [finiteFactor, rowAction, GeneralLinearGroup.coe_one, Matrix.one_apply]
  rfl
private theorem inf_one (r : Fin 2 → F) (v : InfinitePlace F) :
  infiniteFactor F r 1 v = (Real.sqrt ((v (r 0))^2 + (v (r 1))^2)) ^ v.mult := by
  have hn (a : F) : ‖algebraMap F v.Completion a‖ = v a :=
    InfinitePlace.Completion.norm_coe v ((WithAbs.equiv v.1).symm a)
  simp [infiniteFactor, rowAction, GeneralLinearGroup.coe_one, Matrix.one_apply, hn]
  rfl
private theorem mulHeight_formula (r : Fin 2 → F) (hr : r ≠ 0) :
    Height.mulHeight r = (∏ v : InfinitePlace F, (max (v (r 0)) (v (r 1))) ^ v.mult) *
      ∏ᶠ v : HeightOneSpectrum (RingOfIntegers F), max ((FinitePlace.equivHeightOneSpectrum.symm v) (r 0)) ((FinitePlace.equivHeightOneSpectrum.symm v) (r 1)) := by
  rw [NumberField.mulHeight_eq hr]
  have hs (f : Fin 2 → ℝ) : (⨆ i, f i) = max (f 0) (f 1) := by
    apply le_antisymm
    · apply ciSup_le; intro i; fin_cases i
      · exact le_max_left _ _
      · exact le_max_right _ _
    · exact max_le (le_ciSup (Set.finite_range f).bddAbove 0) (le_ciSup (Set.finite_range f).bddAbove 1)
  simp only [hs]
  rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F))]
  congr 1
  apply finprod_congr
  intro v
  rw [Equiv.symm_apply_apply]
private theorem euclidean_bounds (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    max a b ≤ Real.sqrt (a^2 + b^2) ∧
    Real.sqrt (a^2 + b^2) ≤ 2 * max a b := by
  have hm : 0 ≤ max a b := ha.trans (le_max_left _ _)
  have hs := Real.sq_sqrt (show 0 ≤ a^2+b^2 by positivity)
  have hs0 := Real.sqrt_nonneg (a^2+b^2)
  have hma := le_max_left a b
  have hmb := le_max_right a b
  constructor
  · apply max_le <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · nlinarith [sq_nonneg (max a b - a), sq_nonneg (max a b - b)]

theorem height_one_compare :
    ∃ C_F : ℝ, 0 < C_F ∧ ∀ ℓ : Line F,
      1 ≤ height F ℓ 1 ∧
        Projectivization.mulHeight ℓ ≤ height F ℓ 1 ∧
        height F ℓ 1 ≤ C_F * Projectivization.mulHeight ℓ := by
  let CF : ℝ := ∏ v : InfinitePlace F, (2 : ℝ)^v.mult
  refine ⟨CF, Finset.prod_pos (fun _ _ => by positivity), ?_⟩
  intro ℓ
  induction ℓ using Projectivization.ind with
  | h r hr =>
    rw [← ProjGenLinGroup.mk_one (n := Fin 2) (R := Adele F), height_mk,
      Projectivization.mulHeight_mk]
    have hp : 0 ≤ ∏ᶠ v : HeightOneSpectrum (RingOfIntegers F),
        max ((FinitePlace.equivHeightOneSpectrum.symm v) (r 0))
          ((FinitePlace.equivHeightOneSpectrum.symm v) (r 1)) := by
      exact finprod_nonneg (fun v => (AbsoluteValue.nonneg _ _).trans (le_max_left _ _))
    have hl : Height.mulHeight r ≤ rowHeight F r 1 := by
      rw [mulHeight_formula F r hr]
      unfold rowHeight
      simp_rw [fin_one, inf_one]
      apply mul_le_mul_of_nonneg_right _ hp
      apply Finset.prod_le_prod₀
      · intro v _; positivity
      · intro v _
        exact pow_le_pow_left₀ (by positivity)
          (euclidean_bounds _ _ (AbsoluteValue.nonneg _ _) (AbsoluteValue.nonneg _ _)).1 _
    have hu : rowHeight F r 1 ≤ CF * Height.mulHeight r := by
      rw [mulHeight_formula F r hr]
      unfold rowHeight
      simp_rw [fin_one, inf_one]
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ hp
      change _ ≤ (∏ v : InfinitePlace F, (2 : ℝ)^v.mult) * _
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_le_prod₀
      · intro v _; positivity
      · intro v _
        rw [← mul_pow]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _)
          (euclidean_bounds _ _ (AbsoluteValue.nonneg _ _) (AbsoluteValue.nonneg _ _)).2 _
    exact ⟨(Height.one_le_mulHeight r).trans hl, hl, hu⟩

theorem compact_uniform_height (C : Set (AdelPGL F)) (hC : IsCompact C) :
    ∃ m M : ℝ, 0 < m ∧ m ≤ M ∧
      ∀ (ℓ : Line F) (g : AdelPGL F), g ∈ C →
        m * height F ℓ 1 ≤ height F ℓ g ∧
          height F ℓ g ≤ M * height F ℓ 1 := by
  apply KPChamberRowProducts.compact_bounds_of_local
    (fun ℓ : Line F => height F ℓ 1)
    (fun ℓ => (height_pos F ℓ 1).le) (height F) ?_ C hC
  intro g
  let A : AdelGL F := liftAdel F g
  have hA : ProjGenLinGroup.mk A = g := Quotient.out_eq _
  obtain ⟨U, hU, hAU, m, M, hm, hmM, hb⟩ :=
    KPChamberRowProducts.local_rowProduct_bounds F A
  refine ⟨ProjGenLinGroup.mk '' U, ?_, ?_, m, M, hm, hmM, ?_⟩
  · exact KPChamberRowProducts.projective_mk_isOpenMap
      (Fin 2) (Adele F) U hU
  · exact ⟨A, hAU, hA⟩
  · intro ℓ z hz
    obtain ⟨B, hBU, rfl⟩ := hz
    induction ℓ using Projectivization.ind with
    | h r hr =>
      have he (D : AdelGL F) : KPChamberRowProducts.rowProduct F r D =
          rowHeight F r D := rfl
      have h := hb r hr B hBU
      rw [he 1, he B] at h
      rw [height_mk,
        ← ProjGenLinGroup.mk_one (n := Fin 2) (R := Adele F), height_mk]
      exact h

end DedekindZetaZeroFree.KPChamberHeight

end

end
