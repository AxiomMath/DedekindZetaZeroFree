module

public import DedekindZetaZeroFree.Adeles.Quotients.PGL2CuspParabolicStabilizers
public import DedekindZetaZeroFree.Adeles.Lattices.PGL.SteinitzClassObstruction

@[expose] public section

noncomputable section
open scoped Matrix Pointwise
namespace DedekindZetaZeroFree.FiniteAdelicParabolicExtension.TranslationRaw
noncomputable section
variable (F : Type*) [Field F] [NumberField F]
local notation "R" => NumberField.RingOfIntegers F
local notation "FI" => FractionalIdeal (nonZeroDivisors R) F
theorem preserves_iff (I : FI) (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    A ∈ MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F)
      (KPFiniteAdelicLatticeStabilizers.idealVectors F I) ↔
    ∀ V : Matrix (Fin 2) (Fin 1) F, V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I ↔
      A • V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff]
  simp only [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro h V
    simpa using (h (A • V))
  · intro h V
    simpa using (h (A⁻¹ • V))
theorem entries_of_preserves (I : FI) (hI : I ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : ∀ V : Matrix (Fin 2) (Fin 1) F, V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I →
      A • V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I) :
    A 0 0 ∈ (1 : FI) ∧ A 0 1 ∈ I⁻¹ ∧ A 1 0 ∈ I ∧ A 1 1 ∈ (1 : FI) := by
  have h1 := hA !![1; 0] (by simp [KPFiniteAdelicLatticeStabilizers.idealVectors, FractionalIdeal.zero_mem])
  change (∃ r : R, algebraMap R F r = (A • !![1; 0]) 0 0) ∧
    (A • !![1; 0]) 1 0 ∈ I at h1
  simp [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply, Fin.sum_univ_two] at h1
  refine ⟨(FractionalIdeal.mem_one_iff _).mpr h1.1, ?_, h1.2, ?_⟩
  · rw [FractionalIdeal.mem_inv_iff hI]
    intro y hy
    have h := hA !![0; y] (by simp [KPFiniteAdelicLatticeStabilizers.idealVectors, hy])
    change (∃ r : R, algebraMap R F r = (A • !![0; y]) 0 0) ∧ _ at h
    apply (FractionalIdeal.mem_one_iff _).mpr
    simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply, Fin.sum_univ_two] using h.1
  · have hd : A 1 1 ∈ I / I := by
      rw [FractionalIdeal.mem_div_iff_of_ne_zero hI]
      intro y hy
      have h := hA !![0; y] (by simp [KPFiniteAdelicLatticeStabilizers.idealVectors, hy])
      change _ ∧ (A • !![0; y]) 1 0 ∈ I at h
      simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply, Fin.sum_univ_two] using h.2
    simpa [div_self hI] using hd
private theorem det_mem_one_of_preserves (I : FI) (hI : I ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hA : ∀ V : Matrix (Fin 2) (Fin 1) F, V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I →
      A • V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I) :
    ((A : Matrix (Fin 2) (Fin 2) F).det) ∈ (1 : FI) := by
  obtain ⟨ha, hb, hc, hd⟩ := entries_of_preserves F I hI A hA
  rw [Matrix.det_fin_two]
  exact (1 : FI).val.sub_mem (by simpa using FractionalIdeal.mul_mem_mul ha hd)
    ((FractionalIdeal.mem_inv_iff hI).mp hb _ hc)
theorem scalar_unit_of_square_integral (u : Fˣ)
    (hu : (u : F)^2 ∈ (1 : FI)) (hui : ((u⁻¹ : Fˣ) : F)^2 ∈ (1 : FI)) :
    ∃ v : Rˣ, Units.map (algebraMap R F).toMonoidHom v = u := by
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hu
  obtain ⟨s, hs⟩ := (FractionalIdeal.mem_one_iff _).mp hui
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (by norm_num : 0 < 2) (hr ▸ isIntegral_algebraMap)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (by norm_num : 0 < 2) (hs ▸ isIntegral_algebraMap)
  have hxy : x * y = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [map_mul, map_one, hx, hy, Units.mul_inv]
  refine ⟨⟨x, y, hxy, by simpa [mul_comm] using hxy⟩, ?_⟩
  apply Units.ext
  exact hx
private theorem scalar_preserves (I : FI) (v : Rˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin 2)
      (Units.map (algebraMap R F).toMonoidHom v) ∈
      MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F)
        (KPFiniteAdelicLatticeStabilizers.idealVectors F I) := by
  let scalar (w : Rˣ) := Matrix.GeneralLinearGroup.scalar (Fin 2)
    (Units.map (algebraMap R F).toMonoidHom w)
  have hf : ∀ (w : Rˣ) (V : Matrix (Fin 2) (Fin 1) F),
      V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I →
      scalar w • V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I := by
    intro w V hV
    obtain ⟨⟨r, hr⟩, hV⟩ := hV
    change (∃ r : R, algebraMap R F r = (scalar w • V) 0 0) ∧
      (scalar w • V) 1 0 ∈ I
    have he : ∀ i, (scalar w • V) i 0 = algebraMap R F (w : R) * V i 0 := by
      intro i
      simp [scalar, Matrix.GeneralLinearGroup.smul_def, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
    rw [he 0, he 1]
    refine ⟨⟨(w : R) * r, by rw [map_mul, hr]⟩, ?_⟩
    exact I.val.smul_mem (w : R) hV
  apply (preserves_iff F I _).mpr
  intro V
  constructor
  · exact hf v V
  · intro h
    have hh := hf v⁻¹ (scalar v • V) h
    have he : scalar v⁻¹ = (scalar v)⁻¹ := by simp [scalar]
    simpa [he] using hh

theorem determinant_one_projective_iff (I : FI) (hI : I ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hd : (A : Matrix (Fin 2) (Fin 2) F).det = 1) :
    Matrix.ProjGenLinGroup.mk A ∈ KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I ↔
      A ∈ MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F)
        (KPFiniteAdelicLatticeStabilizers.idealVectors F I) := by
  constructor
  · intro h
    obtain ⟨C, hC, he⟩ := Subgroup.mem_map.mp h
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he.symm
    have hdet := det_mem_one_of_preserves F I hI C
      (fun V hV => ((preserves_iff F I C).mp hC V).mp hV)
    have hdeti := det_mem_one_of_preserves F I hI C⁻¹
      (fun V hV => ((preserves_iff F I C⁻¹).mp
        ((MulAction.stabilizer _ _).inv_mem hC) V).mp hV)
    have hdC : (C : Matrix (Fin 2) (Fin 2) F).det = (u : F)^2 := by
      rw [← hu]
      simp [Matrix.det_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.det_fin_two, hd]
    have hdCi : (↑(C⁻¹) : Matrix (Fin 2) (Fin 2) F).det = ((u⁻¹ : Fˣ) : F)^2 := by
      have hh := congrArg (fun X : Matrix.GeneralLinearGroup (Fin 2) F =>
        ((Matrix.GeneralLinearGroup.det X) : F)) (congrArg Inv.inv hu)
      simpa [map_mul, map_inv, Matrix.GeneralLinearGroup.det_scalar,
        Matrix.GeneralLinearGroup.val_det_apply, hd, Fintype.card_fin] using hh.symm
    obtain ⟨v, hv⟩ := scalar_unit_of_square_integral F u
      (hdC ▸ hdet) (hdCi ▸ (show (↑(C⁻¹) : Matrix (Fin 2) (Fin 2) F).det ∈ (1 : FI) from hdeti))
    have hs := scalar_preserves F I v
    rw [hv] at hs
    have ha := (MulAction.stabilizer _ _).mul_mem hC
      ((MulAction.stabilizer _ _).inv_mem hs)
    simpa [← hu] using ha
  · intro h
    exact Subgroup.mem_map.mpr ⟨A, h, rfl⟩
theorem preserves_of_entries (I : FI) (hI : I ≠ 0)
    (A : Matrix (Fin 2) (Fin 2) F)
    (ha : A 0 0 ∈ (1 : FI)) (hb : A 0 1 ∈ I⁻¹)
    (hc : A 1 0 ∈ I) (hd : A 1 1 ∈ (1 : FI)) :
    ∀ V : Matrix (Fin 2) (Fin 1) F, V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I →
      A * V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I := by
  intro V hV
  obtain ⟨⟨r, hr⟩, hV⟩ := hV
  change (∃ s : R, algebraMap R F s = (A * V) 0 0) ∧ (A * V) 1 0 ∈ I
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  constructor
  · apply (FractionalIdeal.mem_one_iff _).mp
    apply (1 : FI).val.add_mem
    · rw [← hr, mul_comm, ← Algebra.smul_def]
      exact (1 : FI).val.smul_mem r ha
    · exact (FractionalIdeal.mem_inv_iff hI).mp hb _ hV
  · apply I.val.add_mem
    · rw [← hr, mul_comm, ← Algebra.smul_def]
      exact I.val.smul_mem r hc
    · obtain ⟨d, hdm⟩ := (FractionalIdeal.mem_one_iff _).mp hd
      rw [← hdm, ← Algebra.smul_def]
      exact I.val.smul_mem d hV
theorem determinant_one_stabilizer_iff_entries (I : FI) (hI : I ≠ 0)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1) :
    A ∈ MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F)
      (KPFiniteAdelicLatticeStabilizers.idealVectors F I) ↔
    A 0 0 ∈ (1 : FI) ∧ A 0 1 ∈ I⁻¹ ∧ A 1 0 ∈ I ∧ A 1 1 ∈ (1 : FI) := by
  constructor
  · intro h
    exact entries_of_preserves F I hI A
      (fun V hV => ((preserves_iff F I A).mp h V).mp hV)
  · rintro ⟨ha, hb, hc, hd⟩
    have hf := preserves_of_entries F I hI (A : Matrix (Fin 2) (Fin 2) F) ha hb hc hd
    have hinv : (↑(A⁻¹) : Matrix (Fin 2) (Fin 2) F) =
        !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
      rw [Matrix.GeneralLinearGroup.coe_inv]
      rw [Matrix.inv_def, hdet]
      simp [Matrix.adjugate_fin_two]
    have hi : ∀ V : Matrix (Fin 2) (Fin 1) F,
        V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I →
          A⁻¹ • V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I := by
      change ∀ V, V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I →
        (↑(A⁻¹) : Matrix (Fin 2) (Fin 2) F) * V ∈ KPFiniteAdelicLatticeStabilizers.idealVectors F I
      apply preserves_of_entries F I hI
      · simpa [hinv] using hd
      · rw [hinv]; exact I⁻¹.val.neg_mem hb
      · rw [hinv]; exact I.val.neg_mem hc
      · simpa [hinv] using ha
    apply (preserves_iff F I A).mpr
    intro V
    constructor
    · exact hf V
    · intro h
      simpa only [inv_smul_smul] using hi (A • V) h
 def constraints (K : Fin 4 → FI) (c : Fin 4 → F) : Submodule R F where
  carrier := {x | ∀ i, x * c i ∈ K i}
  zero_mem' := by intro i; simpa using (K i).zero_mem
  add_mem' := by intro x y hx hy i; simpa [add_mul] using (K i).val.add_mem (hx i) (hy i)
  smul_mem' := by intro r x hx i; simpa [Algebra.smul_def, mul_assoc] using (K i).val.smul_mem r (hx i)
 def coeffModule (K : FI) (c : F) : Submodule R F where
  carrier := {x : F | x*c ∈ K}
  zero_mem' := by simpa using K.zero_mem
  add_mem' := by intro x y hx hy; simpa [add_mul] using K.val.add_mem hx hy
  smul_mem' := by intro r x hx; simpa [Algebra.smul_def, mul_assoc] using K.val.smul_mem r hx
private theorem coeff_fractional (K : FI) (c : F) (hc : c ≠ 0) :
    IsFractional (nonZeroDivisors R) (coeffModule F K c) := by
  apply FractionalIdeal.isFractional_of_le (J := FractionalIdeal.spanSingleton (nonZeroDivisors R) c⁻¹ * K)
  intro x hx
  apply FractionalIdeal.mem_singleton_mul.mpr
  refine ⟨x*c, hx, ?_⟩
  field_simp
private theorem coeff_integer (K : FI) (hK : K ≠ 0) (c : F) :
    ∃ r : R, r ≠ 0 ∧ algebraMap R F r * c ∈ K := by
  obtain ⟨y, hy, hyK⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger hK
  obtain ⟨d, r, hr⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors R) (c / algebraMap R F y)
  refine ⟨d, mem_nonZeroDivisors_iff_ne_zero.mp d.2, ?_⟩
  have hyF : algebraMap R F y ≠ 0 := NumberField.RingOfIntegers.coe_injective.ne (by simpa using hy)
  have he : algebraMap R F (d : R) * c = algebraMap R F r * algebraMap R F y := by
    rw [hr, Algebra.smul_def]
    field_simp
  rw [he, ← Algebra.smul_def]
  exact K.val.smul_mem r hyK
private theorem constraints_fractional (K : Fin 4 → FI) (c : Fin 4 → F)
    (hc : ∃ i, c i ≠ 0) : IsFractional (nonZeroDivisors R) (constraints F K c) := by
  obtain ⟨i, hi⟩ := hc
  apply FractionalIdeal.isFractional_of_le (J := ⟨coeffModule F (K i) (c i), coeff_fractional F (K i) (c i) hi⟩)
  intro x hx
  exact hx i
private theorem constraints_nonzero (K : Fin 4 → FI) (hK : ∀ i, K i ≠ 0) (c : Fin 4 → F) :
    constraints F K c ≠ ⊥ := by
  classical
  choose r hr hm using fun i => coeff_integer F (K i) (hK i) (c i)
  let p : R := ∏ i : Fin 4, r i
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hr i)
  have hpm : algebraMap R F p ∈ constraints F K c := by
    intro i
    have he : p = (∏ j ∈ Finset.univ.erase i, r j) * r i := by
      exact (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    rw [he, map_mul, mul_assoc, ← Algebra.smul_def]
    exact (K i).val.smul_mem _ (hm i)
  intro hb
  rw [hb] at hpm
  have hz : algebraMap R F p = 0 := hpm
  exact hp (NumberField.RingOfIntegers.coe_injective (by simpa using hz))
 def unipotent (x : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])
private theorem unipotent_fixes (x : F) :
    Matrix.ProjGenLinGroup.mk (unipotent F x) • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F := by
  unfold KPCuspArithmetic.infinity
  rw [Projectivization.PGL.mk_smul_mk]
  congr 1
  simp [unipotent, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
private theorem conjugated_membership (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) (x : F) :
    Matrix.ProjGenLinGroup.mk (unipotent F x) ∈ KPCuspArithmetic.conjugatedStabilizer F Γ q σ ↔
    σ * Matrix.ProjGenLinGroup.mk (unipotent F x) * σ⁻¹ ∈ Γ := by
  rw [KPCuspArithmetic.conjugatedStabilizer, Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv, MulAut.conj_apply, Subgroup.mem_inf]
  have hf : σ * Matrix.ProjGenLinGroup.mk (unipotent F x) * σ⁻¹ ∈
      MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q := by
    rw [MulAction.mem_stabilizer_iff]
    rw [mul_smul, mul_smul, ← hσ, inv_smul_smul, unipotent_fixes]
  exact and_iff_left hf
 def rootMatrix : Matrix (Fin 2) (Fin 2) F := !![0, 1; 0, 0]
 def coefficient (B : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F :=
  (B : Matrix (Fin 2) (Fin 2) F) * rootMatrix F * (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) F)
private theorem coefficient_ne (B : Matrix.GeneralLinearGroup (Fin 2) F) : coefficient F B ≠ 0 := by
  intro h
  have he := congrArg (fun M : Matrix (Fin 2) (Fin 2) F =>
    (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) F) * M * (↑B : Matrix (Fin 2) (Fin 2) F)) h
  have hb : (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) F) * (↑B : Matrix (Fin 2) (Fin 2) F) = 1 := by
    exact B.inv_val
  have hbi : (↑B : Matrix (Fin 2) (Fin 2) F) * (↑(B⁻¹) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    exact B.val_inv
  simp only [coefficient, ← Matrix.mul_assoc, hb, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul] at he
  rw [Matrix.mul_assoc, hb, Matrix.mul_one] at he
  have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) he
  simpa [rootMatrix] using this
private theorem conjugate_formula (B : Matrix.GeneralLinearGroup (Fin 2) F) (x : F) :
    (↑(B * unipotent F x * B⁻¹) : Matrix (Fin 2) (Fin 2) F) =
      1 + x • coefficient F B := by
  have hn : (↑(unipotent F x) : Matrix (Fin 2) (Fin 2) F) = 1 + x • rootMatrix F := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unipotent, rootMatrix]
  rw [Units.val_mul, Units.val_mul, hn, Matrix.mul_add, Matrix.add_mul]
  simp [coefficient, Matrix.mul_smul, Matrix.smul_mul]
private theorem one_add_mem (z : F) : 1 + z ∈ (1 : FI) ↔ z ∈ (1 : FI) := by
  constructor
  · intro h
    simpa using (1 : FI).val.sub_mem h (FractionalIdeal.one_mem_one (S := nonZeroDivisors R) (P := F))
  · intro h
    exact (1 : FI).val.add_mem (FractionalIdeal.one_mem_one (S := nonZeroDivisors R) (P := F)) h
private theorem conjugate_membership (I : FI) (hI : I ≠ 0)
    (B : Matrix.GeneralLinearGroup (Fin 2) F) (x : F) :
    Matrix.ProjGenLinGroup.mk (B * unipotent F x * B⁻¹) ∈ KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I ↔
    x ∈ constraints F ![1, I⁻¹, I, 1]
      ![coefficient F B 0 0, coefficient F B 0 1, coefficient F B 1 0, coefficient F B 1 1] := by
  have hd : (↑(B * unipotent F x * B⁻¹) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    simp [Matrix.det_mul, unipotent, Matrix.det_fin_two, ← Matrix.GeneralLinearGroup.val_det_apply]
  rw [determinant_one_projective_iff F I hI _ hd, determinant_one_stabilizer_iff_entries F I hI _ hd]
  rw [conjugate_formula]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul,
    Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_add]
  rw [one_add_mem, one_add_mem]
  change _ ↔ ∀ i : Fin 4, _
  simp [Fin.forall_fin_succ]
private theorem exists_translation_ideal (I : FI) (hI : I ≠ 0)
    (B : Matrix.GeneralLinearGroup (Fin 2) F) :
    ∃ J : FI, J ≠ 0 ∧ ∀ x : F,
      Matrix.ProjGenLinGroup.mk (B * unipotent F x * B⁻¹) ∈ KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I ↔ x ∈ J := by
  let K : Fin 4 → FI := ![1, I⁻¹, I, 1]
  let c : Fin 4 → F := ![coefficient F B 0 0, coefficient F B 0 1, coefficient F B 1 0, coefficient F B 1 1]
  have hc : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    apply coefficient_ne F B
    ext i j
    fin_cases i <;> fin_cases j
    · exact h 0
    · exact h 1
    · exact h 2
    · exact h 3
  have hK : ∀ i, K i ≠ 0 := by
    intro i
    fin_cases i <;> simp [K, hI]
  refine ⟨⟨constraints F K c, constraints_fractional F K c hc⟩, ?_, ?_⟩
  · intro hz
    apply constraints_nonzero F K hK c
    simpa using congrArg Subtype.val hz
  · intro x
    exact conjugate_membership F I hI B x
end
end DedekindZetaZeroFree.FiniteAdelicParabolicExtension.TranslationRaw

namespace DedekindZetaZeroFree.FiniteAdelicParabolicExtension

open TranslationRaw

open KPCuspArithmetic in

theorem mem_conjugatedStabilizer_iff
    (F : Type*) [Field F] [NumberField F]
    (Γ : Subgroup (PGL2 F)) (q : Cusp F) (σ : PGL2 F)
    (hσ : σ • infinity F = q) (g : PGL2 F) (hg : g • infinity F = infinity F) :
    g ∈ conjugatedStabilizer F Γ q σ ↔ σ * g * σ⁻¹ ∈ Γ := by
  have hstab : σ * g * σ⁻¹ ∈ MulAction.stabilizer (PGL2 F) q := by
    rw [MulAction.mem_stabilizer_iff]
    calc (σ * g * σ⁻¹) • q = (σ * g * σ⁻¹) • (σ • infinity F) := by rw [hσ]
      _ = σ • (g • (σ⁻¹ • (σ • infinity F))) := by simp only [mul_smul]
      _ = σ • (g • infinity F) := by rw [inv_smul_smul]
      _ = σ • infinity F := by rw [hg]
      _ = q := hσ
  constructor
  · intro h
    rw [conjugatedStabilizer, Subgroup.mem_map] at h
    obtain ⟨k, hk, hk'⟩ := h
    have : σ * g * σ⁻¹ = k := by
      rw [← hk']
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
      group
    rw [this]
    exact hk.1
  · intro h
    rw [conjugatedStabilizer, Subgroup.mem_map]
    refine ⟨σ * g * σ⁻¹, ⟨h, hstab⟩, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    group

theorem ideal_cusp_translation_fractionalIdeal
    (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (hI : I ≠ 0) (a : KPFiniteAdelicLatticeStabilizers.RationalPG F)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ J : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F,
      J ≠ 0 ∧ ∀ x : F,
        Matrix.ProjGenLinGroup.mk
          (Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1]
            (by simp [Matrix.det_fin_two])) ∈
          KPCuspArithmetic.conjugatedStabilizer F
            ((KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map
              (MulAut.conj a).toMonoidHom) q σ ↔ x ∈ J := by
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective (a⁻¹ * σ)
  obtain ⟨J, hJ, hm⟩ := exists_translation_ideal F I hI B
  refine ⟨J, hJ, fun x => ?_⟩
  change Matrix.ProjGenLinGroup.mk (unipotent F x) ∈
    KPCuspArithmetic.conjugatedStabilizer F
      ((KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map
        (MulAut.conj a).toMonoidHom) q σ ↔ x ∈ J
  rw [conjugated_membership F _ q σ hσ x, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  have he : a⁻¹ * (σ * Matrix.ProjGenLinGroup.mk (unipotent F x) * σ⁻¹) * a =
      Matrix.ProjGenLinGroup.mk (B * unipotent F x * B⁻¹) := by
    simp [map_mul, map_inv, hB, mul_assoc]
  rw [he]
  exact hm x

end DedekindZetaZeroFree.FiniteAdelicParabolicExtension

end
