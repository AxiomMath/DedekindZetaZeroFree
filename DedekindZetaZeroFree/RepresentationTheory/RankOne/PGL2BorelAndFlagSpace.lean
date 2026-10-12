module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.CompactQuotientInductionAdmissibility
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.CompletionBallMass

@[expose] public section

section

noncomputable section

namespace DedekindZetaZeroFree.KPRankOneInductionRaw

open scoped Topology NNReal Matrix OnePoint Classical
open IsDedekindDomain NumberField MeasureTheory

variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (RingOfIntegers F))

abbrev LocalField := v.adicCompletion F
abbrev GL2 := Matrix.GeneralLinearGroup (Fin 2) (LocalField F v)
abbrev PGL2 := Matrix.ProjGenLinGroup (Fin 2) (LocalField F v)

instance pglTopology : TopologicalSpace (PGL2 F v) := by
  unfold PGL2 Matrix.ProjGenLinGroup
  infer_instance

instance pglTopologicalGroup : IsTopologicalGroup (PGL2 F v) := by
  letI : IsTopologicalGroup (GL2 F v) := by
    change IsTopologicalGroup (Matrix (Fin 2) (Fin 2) (LocalField F v))ˣ
    infer_instance
  unfold PGL2 Matrix.ProjGenLinGroup
  exact QuotientGroup.instIsTopologicalGroup (Subgroup.center (GL2 F v))

private lemma mul_scalar_apply (A : GL2 F v) (u : (LocalField F v)ˣ) (i j : Fin 2) :
    (A * Matrix.GeneralLinearGroup.scalar (Fin 2) u) i j = A i j * (u : LocalField F v) := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

 lemma mul_entry (A B : GL2 F v) (i j : Fin 2) :
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]

 lemma diag_ne_zero {A : GL2 F v} (hu : A 1 0 = 0) : A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 := by
  have hdet : (A : Matrix (Fin 2) (Fin 2) (LocalField F v)).det ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_two] at hdet
  rw [show (A : Matrix (Fin 2) (Fin 2) (LocalField F v)) 1 0 = 0 from hu,
    mul_zero, sub_zero] at hdet
  exact mul_ne_zero_iff.mp hdet

 lemma inv_entry_zero {A : GL2 F v} (hu : A 1 0 = 0) : (A⁻¹) 1 0 = 0 := by
  have h11 : A 1 1 ≠ 0 := (diag_ne_zero F v hu).2
  have hmul : ((A : Matrix (Fin 2) (Fin 2) (LocalField F v)) *
      ((A⁻¹ : GL2 F v) : Matrix (Fin 2) (Fin 2) (LocalField F v))) 1 0 = 0 := by
    have h := congr_arg
      (fun g : GL2 F v => (g : Matrix (Fin 2) (Fin 2) (LocalField F v)) 1 0)
      (mul_inv_cancel A)
    simpa using h
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hmul
  simp only [hu, zero_mul, zero_add, Matrix.one_apply, Fin.isValue, Fin.reduceEq,
    reduceIte] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left h11

 lemma inv_entry_zero' {A : GL2 F v} (hu : A 1 0 = 0) (hv : A 0 1 = 0) :
    (A⁻¹) 0 1 = 0 := by
  have h00 : A 0 0 ≠ 0 := (diag_ne_zero F v hu).1
  have hmul : ((A : Matrix (Fin 2) (Fin 2) (LocalField F v)) *
      ((A⁻¹ : GL2 F v) : Matrix (Fin 2) (Fin 2) (LocalField F v))) 0 1 = 0 := by
    have h := congr_arg
      (fun g : GL2 F v => (g : Matrix (Fin 2) (Fin 2) (LocalField F v)) 0 1)
      (mul_inv_cancel A)
    simpa using h
  rw [Matrix.mul_apply, Fin.sum_univ_two] at hmul
  simp only [hv, zero_mul, add_zero, Matrix.one_apply, Fin.isValue, Fin.reduceEq,
    reduceIte] at hmul
  exact (mul_eq_zero.mp hmul).resolve_left h00

def upperBorel : Subgroup (PGL2 F v) where
  carrier := {g | ∃ A : GL2 F v, Matrix.ProjGenLinGroup.mk A = g ∧ A 1 0 = 0}
  one_mem' := by
    refine ⟨1, ?_, ?_⟩ <;> simp
  mul_mem' := by
    rintro a b ⟨A, hA, huA⟩ ⟨B, hB, huB⟩
    refine ⟨A * B, ?_, ?_⟩
    · rw [map_mul, hA, hB]
    · rw [mul_entry, huA, huB, mul_zero, zero_mul, add_zero]
  inv_mem' := by
    rintro a ⟨A, hA, huA⟩
    exact ⟨A⁻¹, by rw [map_inv, hA], inv_entry_zero F v huA⟩

def diagonalTorus : Subgroup (PGL2 F v) where
  carrier := {g | ∃ A : GL2 F v,
    Matrix.ProjGenLinGroup.mk A = g ∧ A 1 0 = 0 ∧ A 0 1 = 0}
  one_mem' := by
    refine ⟨1, ?_, ?_, ?_⟩ <;> simp
  mul_mem' := by
    rintro a b ⟨A, hA, huA, hvA⟩ ⟨B, hB, huB, hvB⟩
    refine ⟨A * B, ?_, ?_, ?_⟩
    · rw [map_mul, hA, hB]
    · rw [mul_entry, huA, huB, mul_zero, zero_mul, add_zero]
    · rw [mul_entry, hvA, hvB, mul_zero, zero_mul, add_zero]
  inv_mem' := by
    rintro a ⟨A, hA, huA, hvA⟩
    exact ⟨A⁻¹, by rw [map_inv, hA], inv_entry_zero F v huA, inv_entry_zero' F v huA hvA⟩

 lemma scalar_entries_eq_one {A : GL2 F v}
    (hA : Matrix.ProjGenLinGroup.mk A = 1) : A 0 0 = A 1 1 := by
  have hmem : A ∈ Subgroup.center (GL2 F v) := Matrix.ProjGenLinGroup.mk_eq_one.mp hA
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hmem
  obtain ⟨u, rfl⟩ := hmem
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply]

 lemma choose_ratio_eq (b : upperBorel F v) (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A = b.val) (hu : A 1 0 = 0) :
    (Classical.choose b.property) 0 0 / (Classical.choose b.property) 1 1 = A 0 0 / A 1 1 := by
  obtain ⟨u, hu_eq⟩ := (Matrix.ProjGenLinGroup.mk_eq_mk_iff (g₁ := A)
    (g₂ := Classical.choose b.property)).mp
      (by rw [hA, (Classical.choose_spec b.property).1])
  have h00 : (Classical.choose b.property) 0 0 = A 0 0 * (u : LocalField F v) := by
    rw [← hu_eq, mul_scalar_apply]
  have h11 : (Classical.choose b.property) 1 1 = A 1 1 * (u : LocalField F v) := by
    rw [← hu_eq, mul_scalar_apply]
  rw [h00, h11]
  exact mul_div_mul_right _ _ u.ne_zero

def borelRatio : upperBorel F v →* (LocalField F v)ˣ where
  toFun b :=
    let A := Classical.choose b.property
    Units.mk0 (A 0 0 / A 1 1) (by
      have hu : A 1 0 = 0 := (Classical.choose_spec b.property).2
      exact div_ne_zero (diag_ne_zero F v hu).1 (diag_ne_zero F v hu).2)
  map_one' := by
    apply Units.ext
    have hspec := Classical.choose_spec (1 : upperBorel F v).property
    have hA : Matrix.ProjGenLinGroup.mk (Classical.choose (1 : upperBorel F v).property) = 1 := by
      rw [hspec.1]; rfl
    have heq := scalar_entries_eq_one F v hA
    have hne : (Classical.choose (1 : upperBorel F v).property) 0 0 ≠ 0 :=
      (diag_ne_zero F v hspec.2).1
    show (Classical.choose (1 : upperBorel F v).property) 0 0 /
      (Classical.choose (1 : upperBorel F v).property) 1 1 = 1
    rw [← heq]
    exact div_self hne
  map_mul' := by
    intro b c
    apply Units.ext
    have hbc : Matrix.ProjGenLinGroup.mk
        (Classical.choose b.property * Classical.choose c.property) = (b * c).val := by
      rw [map_mul, (Classical.choose_spec b.property).1, (Classical.choose_spec c.property).1]
      rfl
    have hu : (Classical.choose b.property * Classical.choose c.property) 1 0 = 0 := by
      rw [mul_entry, (Classical.choose_spec b.property).2, (Classical.choose_spec c.property).2,
        mul_zero, zero_mul, add_zero]
    have hmain := choose_ratio_eq F v (b * c) _ hbc hu
    have hb := choose_ratio_eq F v b (Classical.choose b.property)
      (Classical.choose_spec b.property).1 (Classical.choose_spec b.property).2
    have hc := choose_ratio_eq F v c (Classical.choose c.property)
      (Classical.choose_spec c.property).1 (Classical.choose_spec c.property).2
    show (Classical.choose (b * c).property) 0 0 / (Classical.choose (b * c).property) 1 1 =
      (Classical.choose b.property) 0 0 / (Classical.choose b.property) 1 1 *
      ((Classical.choose c.property) 0 0 / (Classical.choose c.property) 1 1)
    rw [hmain, hb, hc]
    have huAb := (Classical.choose_spec b.property).2
    have huAc := (Classical.choose_spec c.property).2
    rw [mul_entry, mul_entry, huAc, huAb]
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [div_mul_div_comm]

theorem borelRatio_eq (b : upperBorel F v) (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A = b.val) (hupper : A 1 0 = 0) :
    (borelRatio F v b : LocalField F v) = A 0 0 / A 1 1 := by
  have := choose_ratio_eq F v b A hA hupper
  simpa [borelRatio] using this

end DedekindZetaZeroFree.KPRankOneInductionRaw

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneInductionRaw

open scoped Topology NNReal Matrix OnePoint Classical
open IsDedekindDomain NumberField MeasureTheory
variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (RingOfIntegers F))

def localAbs : (LocalField F v)ˣ →* (ℝ≥0)ˣ where
  toFun y := Units.mk0 ‖(y : LocalField F v)‖₊ (by
    simp only [ne_eq, ← NNReal.coe_eq_zero, coe_nnnorm, norm_ne_zero_iff]
    exact Units.ne_zero y)
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp

def ordinaryDelta : upperBorel F v →* (ℝ≥0)ˣ :=
  (localAbs F v).comp (borelRatio F v)

theorem ordinaryDelta_eq (b : upperBorel F v) (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A = b.val) (hupper : A 1 0 = 0) :
    ((ordinaryDelta F v b : ℝ≥0) : ℝ) = ‖A 0 0 / A 1 1‖ := by
  have h1 : (ordinaryDelta F v b : ℝ≥0) = ‖(borelRatio F v b : LocalField F v)‖₊ := by
    simp [ordinaryDelta, localAbs]
  rw [h1, borelRatio_eq F v b A hA hupper, coe_nnnorm]

private theorem representative_upper (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A ∈ upperBorel F v) : A 1 0 = 0 := by
  obtain ⟨B, hB, hu⟩ := hA
  obtain ⟨t, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
  simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.mul_diagonal, hu] using hu

private theorem norm_lc {X : Type*} [TopologicalSpace X]
    (f : X → LocalField F v) (hf : Continuous f) (hn : ∀ x, f x ≠ 0) :
    IsLocallyConstant (fun x => ‖f x‖₊) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have he : ∀ᶠ z in 𝓝 x, ‖f z - f x‖ < ‖f x‖ :=
    ((isOpen_lt (hf.sub continuous_const).norm continuous_const).mem_nhds
      (by
        change ‖f x - f x‖ < ‖f x‖
        rw [sub_self, norm_zero]
        exact norm_pos_iff.mpr (hn x)))
  filter_upwards [he] with z hz
  apply NNReal.coe_injective
  change ‖f z‖ = ‖f x‖
  have h := IsUltrametricDist.norm_eq_of_add_norm_lt_max
    (x := f z) (y := -f x) (by
      simpa [sub_eq_add_neg] using hz.trans_le (le_max_right ‖f z‖ ‖f x‖))
  simpa using h

private theorem delta_lc : IsLocallyConstant (ordinaryDelta F v) := by
  let p : GL2 F v → PGL2 F v := Matrix.ProjGenLinGroup.mk
  let S : Set (PGL2 F v) := upperBorel F v
  have hp : IsOpenQuotientMap p := QuotientGroup.isOpenQuotientMap_mk
  have hq := (hp.restrictPreimage S).isQuotientMap
  let r : (p ⁻¹' S) → LocalField F v := fun A => A.val 0 0 / A.val 1 1
  have hr (A : p ⁻¹' S) :
      (borelRatio F v (S.restrictPreimage p A) : LocalField F v) = r A := by
    exact borelRatio_eq F v _ A.val rfl (representative_upper F v A.val A.property)
  have hn (A : p ⁻¹' S) : r A ≠ 0 := by
    rw [← hr A]
    exact Units.ne_zero _
  have hd (A : p ⁻¹' S) : A.val 1 1 ≠ 0 := by
    exact (div_ne_zero_iff.mp (hn A)).2
  have hval : Continuous (fun A : p ⁻¹' S =>
      (A.val : Matrix (Fin 2) (Fin 2) (LocalField F v))) :=
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (LocalField F v))).comp
      continuous_subtype_val
  have hc : Continuous r := by
    apply Continuous.div
    · exact (continuous_apply 0).comp ((continuous_apply 0).comp hval)
    · exact (continuous_apply 1).comp ((continuous_apply 1).comp hval)
    · exact hd
  have hl := norm_lc F v r hc hn
  have hcDelta : IsLocallyConstant ((ordinaryDelta F v) ∘ S.restrictPreimage p) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro A
    filter_upwards [hl.eventually_eq A] with B hB
    apply Units.ext
    change ‖(borelRatio F v (S.restrictPreimage p B) : LocalField F v)‖₊ =
      ‖(borelRatio F v (S.restrictPreimage p A) : LocalField F v)‖₊
    simpa only [hr] using hB
  intro U
  apply hq.isCoinducing.isOpen_preimage.mp
  exact hcDelta U

theorem ordinaryDelta_locallyConstant : IsLocallyConstant (ordinaryDelta F v) := by
  exact delta_lc F v

def halfModulus {B : Type*} [Group B] (δ : B →* (ℝ≥0)ˣ) : B →* (ℝ≥0)ˣ where
  toFun b := Units.mk0 (NNReal.sqrt (δ b : ℝ≥0)) (by
    rw [Ne, NNReal.sqrt_eq_zero]
    exact Units.ne_zero (δ b))
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp [MonoidHom.map_mul, NNReal.sqrt_mul]

theorem halfModulus_eq {B : Type*} [Group B] (δ : B →* (ℝ≥0)ˣ) (b : B) :
    ((halfModulus δ b : ℝ≥0) : ℝ) = Real.sqrt ((δ b : ℝ≥0) : ℝ) := by
  simp [halfModulus, Real.coe_sqrt]

theorem halfModulus_locallyConstant {B : Type*} [Group B] [TopologicalSpace B]
    (δ : B →* (ℝ≥0)ˣ) (hδ : IsLocallyConstant δ) :
    IsLocallyConstant (halfModulus δ) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro b
  filter_upwards [hδ.eventually_eq b] with y hy
  apply Units.ext
  simp only [halfModulus, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mk0, hy]

end DedekindZetaZeroFree.KPRankOneInductionRaw

end

end

section

noncomputable section
namespace DedekindZetaZeroFree.KPRankOneInductionRaw

open scoped Topology NNReal Matrix OnePoint Classical
open IsDedekindDomain NumberField MeasureTheory Topology Filter
variable (F : Type*) [Field F] [NumberField F]
  (v : HeightOneSpectrum (RingOfIntegers F))

theorem upperBorel_closed : IsClosed (upperBorel F v : Set (PGL2 F v)) := by
  have hp : Topology.IsQuotientMap (Matrix.ProjGenLinGroup.mk : GL2 F v → PGL2 F v) :=
    QuotientGroup.isOpenQuotientMap_mk.isQuotientMap
  apply hp.isClosed_preimage.mp
  have he : (Matrix.ProjGenLinGroup.mk : GL2 F v → PGL2 F v) ⁻¹'
      (upperBorel F v : Set (PGL2 F v)) = {A | A 1 0 = 0} := by
    ext A
    constructor
    · rintro ⟨B, hB, hu⟩
      obtain ⟨t, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
      simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.scalar, Matrix.mul_diagonal, hu] using hu
    · intro h
      exact ⟨A, rfl, h⟩
  rw [he]
  apply isClosed_eq _ continuous_const
  exact (continuous_apply 0).comp ((continuous_apply 1).comp
    (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) (LocalField F v))))

 def q (A : GL2 F v) : SectionCosetSpace (upperBorel F v) :=
  Quotient.mk _ (Matrix.ProjGenLinGroup.mk A)
private theorem rep_upper (A : GL2 F v)
    (hA : Matrix.ProjGenLinGroup.mk A ∈ upperBorel F v) : A 1 0 = 0 := by
  obtain ⟨B, hB, hu⟩ := hA
  obtain ⟨t, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hB
  simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
    Matrix.scalar, Matrix.mul_diagonal, hu] using hu
private theorem q_eq (A B : GL2 F v) : q F v A = q F v B ↔ (B * A⁻¹) 1 0 = 0 := by
  rw [q, q, Quotient.eq, QuotientGroup.rightRel_apply, ← map_inv, ← map_mul]
  exact ⟨rep_upper F v _, fun h => ⟨_, rfl, h⟩⟩
 def chart (x : LocalField F v) : GL2 F v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1,0;x,1] (by simp [Matrix.det_fin_two])
 def alt (x : LocalField F v) : GL2 F v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0,1;1,x] (by simp [Matrix.det_fin_two])
 def altInv (x : LocalField F v) : GL2 F v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![-x,1;1,0] (by simp [Matrix.det_fin_two])
private theorem chart_inv (x : LocalField F v) : (chart F v x)⁻¹ = chart F v (-x) := by
  apply inv_eq_of_mul_eq_one_right
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [chart, Matrix.mul_apply, Fin.sum_univ_two]
private theorem alt_inv (x : LocalField F v) : (alt F v x)⁻¹ = altInv F v x := by
  apply inv_eq_of_mul_eq_one_right
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [alt, altInv, Matrix.mul_apply, Fin.sum_univ_two]
 def flagRep : OnePoint (LocalField F v) → SectionCosetSpace (upperBorel F v) :=
  fun p => p.elim (q F v (alt F v 0)) (fun x => q F v (chart F v x))
 theorem flagRep_inj : Function.Injective (flagRep F v) := by
  intro x y h
  cases x <;> cases y
  · rfl
  · change q F v (alt F v 0) = q F v (chart F v _) at h
    rw [q_eq, alt_inv] at h
    simpa [chart, altInv, Matrix.mul_apply, Fin.sum_univ_two] using h
  · change q F v (chart F v _) = q F v (alt F v 0) at h
    rw [q_eq, chart_inv] at h
    simpa [chart, alt, Matrix.mul_apply, Fin.sum_univ_two] using h
  · change q F v (chart F v _) = q F v (chart F v _) at h
    rw [q_eq, chart_inv] at h
    simp [chart, Matrix.mul_apply, Fin.sum_univ_two] at h
    congr 1
    linear_combination -h
 theorem flagRep_surj : Function.Surjective (flagRep F v) := by
  intro x
  induction x using Quotient.inductionOn with | h g =>
  induction g using Quotient.inductionOn with | h A =>
  by_cases hd : A 1 1 = 0
  · refine ⟨∞, ?_⟩
    change q F v (alt F v 0) = q F v A
    rw [q_eq, alt_inv]
    simp [altInv, Matrix.mul_apply, Fin.sum_univ_two, hd]
  · refine ⟨↑(A 1 0 / A 1 1), ?_⟩
    change q F v (chart F v _) = q F v A
    rw [q_eq, chart_inv]
    simp [chart, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
private theorem chart_cont : Continuous (chart F v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun x : LocalField F v => (!![1,0;x,1] : Matrix _ _ _))
    fun_prop
  · simp only [chart_inv]
    change Continuous (fun x : LocalField F v => (!![1,0;-x,1] : Matrix _ _ _))
    fun_prop
private theorem alt_cont : Continuous (alt F v) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous (fun x : LocalField F v => (!![0,1;1,x] : Matrix _ _ _))
    fun_prop
  · simp only [alt_inv]
    change Continuous (fun x : LocalField F v => (!![-x,1;1,0] : Matrix _ _ _))
    fun_prop
private theorem q_cont : Continuous (q F v) :=
  continuous_quot_mk.comp QuotientGroup.continuous_mk
private theorem flagRep_alt (x : LocalField F v) (hx : x ≠ 0) :
    flagRep F v (↑x) = q F v (alt F v x⁻¹) := by
  change q F v (chart F v x) = q F v (alt F v x⁻¹)
  rw [q_eq, chart_inv]
  simp [chart, alt, Matrix.mul_apply, Fin.sum_univ_two, hx]
 theorem flagRep_cont : Continuous (flagRep F v) := by
  rw [OnePoint.continuous_iff]
  constructor
  · have h := ((q_cont F v).comp (alt_cont F v)).tendsto 0
    have hi : Tendsto (fun x : LocalField F v => x⁻¹)
        (coclosedCompact (LocalField F v)) (𝓝 0) := by
      rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
      exact tendsto_inv₀_cobounded
    apply (h.comp hi).congr'
    have hn : ∀ᶠ x : LocalField F v in coclosedCompact (LocalField F v), x ≠ 0 := by
      rw [coclosedCompact_eq_cocompact]
      exact (isCompact_singleton : IsCompact ({0} : Set (LocalField F v))).compl_mem_cocompact
    filter_upwards [hn] with x hx
    exact (flagRep_alt F v x hx).symm
  · exact (q_cont F v).comp (chart_cont F v)

def ordinaryFlagHomeomorph : SectionCosetSpace (upperBorel F v) ≃ₜ
    OnePoint (LocalField F v) := by
  letI : IsClosed (upperBorel F v : Set (PGL2 F v)) := upperBorel_closed F v
  letI : T2Space (SectionCosetSpace (upperBorel F v)) := by
    change T2Space (Quotient (MulAction.orbitRel (upperBorel F v) (PGL2 F v)))
    infer_instance
  exact (Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective (flagRep F v) ⟨flagRep_inj F v, flagRep_surj F v⟩)
    (flagRep_cont F v)).symm

theorem diagonalMatrix_det_ne_zero (y : (LocalField F v)ˣ) :
    Matrix.det (!![(y : LocalField F v), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (LocalField F v)) ≠ 0 := by
  simp [Matrix.det_fin_two]

def diagonalMatrix (y : (LocalField F v)ˣ) : GL2 F v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(y : LocalField F v), 0; 0, 1] (by exact diagonalMatrix_det_ne_zero F v y)

theorem upperRootMatrix_det_ne_zero (x : LocalField F v) :
    Matrix.det (!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) (LocalField F v)) ≠ 0 := by
  simp [Matrix.det_fin_two]

def upperRootMatrix (x : LocalField F v) : GL2 F v :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by exact upperRootMatrix_det_ne_zero F v x)

def diagonalElement (y : (LocalField F v)ˣ) : PGL2 F v :=
  Matrix.ProjGenLinGroup.mk (diagonalMatrix F v y)

def upperRootElement (x : LocalField F v) : PGL2 F v :=
  Matrix.ProjGenLinGroup.mk (upperRootMatrix F v x)

theorem diagonalElement_mem (y : (LocalField F v)ˣ) :
    diagonalElement F v y ∈ upperBorel F v := by
  exact ⟨diagonalMatrix F v y, rfl, by simp [diagonalMatrix]⟩

theorem upperRootElement_mem (x : LocalField F v) :
    upperRootElement F v x ∈ upperBorel F v := by
  exact ⟨upperRootMatrix F v x, rfl, by simp [upperRootMatrix]⟩

theorem ordinaryDelta_upperRoot (x : LocalField F v) :
    ordinaryDelta F v ⟨upperRootElement F v x, upperRootElement_mem F v x⟩ = 1 := by
  change localAbs F v (borelRatio F v _) = 1
  have h : borelRatio F v ⟨upperRootElement F v x, upperRootElement_mem F v x⟩ = 1 := by
    apply Units.ext
    simpa [upperRootMatrix] using borelRatio_eq F v
      ⟨upperRootElement F v x, upperRootElement_mem F v x⟩ (upperRootMatrix F v x) rfl
      (by simp [upperRootMatrix])
  rw [h, map_one]

def ordinaryUpperRootHom : Multiplicative (LocalField F v) →* PGL2 F v where
  toFun x := upperRootElement F v (Multiplicative.toAdd x)
  map_one' := by
    have h : upperRootMatrix F v 0 = 1 := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;> simp [upperRootMatrix]
    change Matrix.ProjGenLinGroup.mk (upperRootMatrix F v 0) = 1
    rw [h, map_one]
  map_mul' := by
    intro x z
    have h : upperRootMatrix F v (Multiplicative.toAdd x + Multiplicative.toAdd z) =
        upperRootMatrix F v (Multiplicative.toAdd x) * upperRootMatrix F v (Multiplicative.toAdd z) := by
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [upperRootMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]
    change Matrix.ProjGenLinGroup.mk (upperRootMatrix F v (Multiplicative.toAdd x + Multiplicative.toAdd z)) = _
    rw [h, map_mul]
    rfl

end DedekindZetaZeroFree.KPRankOneInductionRaw

end

end
