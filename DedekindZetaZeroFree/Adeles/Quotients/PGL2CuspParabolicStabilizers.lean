module

public import Mathlib.Topology.Algebra.IsUniformGroup.DiscreteSubgroup
public import DedekindZetaZeroFree.Arithmetic.PGL.Cusps.StabilizerUnitRatios

@[expose] public section

section

noncomputable section

open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization nonZeroDivisors

namespace DedekindZetaZeroFree

namespace KPCuspArithmetic

variable (F : Type*) [Field F] [NumberField F]

abbrev PGL2 := Matrix.ProjGenLinGroup (Fin 2) F

end KPCuspArithmetic

end DedekindZetaZeroFree

end

end

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.Translations
variable {F : Type*} [Field F]
def unipotent (x : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])
@[simp] theorem unipotent_coe (x : F) :
    (↑(unipotent x) : Matrix (Fin 2) (Fin 2) F) = !![1, x; 0, 1] := rfl
@[simp] theorem unipotent_zero : unipotent (0 : F) = 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp
@[simp] theorem unipotent_add (x y : F) : unipotent (x + y) = unipotent x * unipotent y := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]
def translationHom : Multiplicative F →* ProjectiveGroup F where
  toFun x := Matrix.ProjGenLinGroup.mk (unipotent (Multiplicative.toAdd x))
  map_one' := by simp
  map_mul' x y := by
    change Matrix.ProjGenLinGroup.mk (unipotent (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [unipotent_add, map_mul]
theorem parameter_iff (S : Subgroup (ProjectiveGroup F)) (x : F) :
    TranslationParameter S x ↔ translationHom (Multiplicative.ofAdd x) ∈ S := by
  constructor
  · rintro ⟨A, hA, h10, he, h01⟩
    have hn : A 0 0 ≠ 0 := by
      intro hz
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, h10, hz])
    have hmatrix : A = unipotent x * Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (A 0 0) hn) := by
      apply Units.ext
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_two, h10, he, h01]
    have hp : Matrix.ProjGenLinGroup.mk (unipotent x) = Matrix.ProjGenLinGroup.mk A :=
      Matrix.ProjGenLinGroup.mk_eq_mk_iff.mpr ⟨_, hmatrix.symm⟩
    change Matrix.ProjGenLinGroup.mk (unipotent x) ∈ S
    rwa [hp]
  · intro hx
    exact ⟨unipotent x, hx, by simp, by simp, by simp⟩
theorem unipotent_fixes [NumberField F] (x : F) :
    translationHom (Multiplicative.ofAdd x) • StandardCusp F = StandardCusp F := by
  unfold StandardCusp
  change Matrix.ProjGenLinGroup.mk (unipotent x) • _ = _
  rw [Projectivization.PGL.mk_smul_mk]
  congr 1
  change (↑(unipotent x) : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0] = ![1, 0]
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
variable [NumberField F]
theorem cusp_translation_iff (Γ : Subgroup (ProjectiveGroup F))
    (q : Projectivization F (Plane F)) (σ : ProjectiveGroup F)
    (hσ : σ • StandardCusp F = q) (x : F) :
    TranslationParameter (CuspSubgroup F Γ q σ) x ↔
      (MulAut.conj σ).toMonoidHom (translationHom (Multiplicative.ofAdd x)) ∈ Γ := by
  rw [parameter_iff, CuspSubgroup, Subgroup.mem_map_equiv]
  simp only [MulAut.conj_symm_apply, inv_inv, Subgroup.mem_inf]
  have hf : σ * translationHom (Multiplicative.ofAdd x) * σ⁻¹ ∈
      MulAction.stabilizer (ProjectiveGroup F) q := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, ← hσ, inv_smul_smul,
      unipotent_fixes]
  exact and_iff_left hf

theorem translation_finite_index_of_full_ideal
    (M : Submodule (IntegralOrder F) (Plane F))
    (Γ : Subgroup (ProjectiveGroup F))
    (hΓ : Γ ≤ LatticeAutomorphisms F M)
    (hcomm : Γ.Commensurable (LatticeAutomorphisms F M))
    (q : Projectivization F (Plane F)) (σ : ProjectiveGroup F)
    (hσ : σ • StandardCusp F = q)
    (L : AddSubgroup F)
    (hL : ∀ x : F, x ∈ L ↔ TranslationParameter (CuspSubgroup F Γ q σ) x)
    (J : FractionalIdeal (IntegralOrder F)⁰ F)
    (hJ : ∀ x : F, x ∈ J ↔
      TranslationParameter (CuspSubgroup F (LatticeAutomorphisms F M) q σ) x) :
    L ≤ (J : Submodule (IntegralOrder F) F).toAddSubgroup ∧
      L.IsFiniteRelIndex (J : Submodule (IntegralOrder F) F).toAddSubgroup := by
  let f : Multiplicative F →* ProjectiveGroup F :=
    (MulAut.conj σ).toMonoidHom.comp translationHom
  have heL : L.toSubgroup = Γ.comap f := by
    ext x
    exact (hL (Multiplicative.toAdd x)).trans
      (cusp_translation_iff Γ q σ hσ (Multiplicative.toAdd x))
  have heJ : (J : Submodule (IntegralOrder F) F).toAddSubgroup.toSubgroup =
      (LatticeAutomorphisms F M).comap f := by
    ext x
    exact (hJ (Multiplicative.toAdd x)).trans
      (cusp_translation_iff (LatticeAutomorphisms F M) q σ hσ (Multiplicative.toAdd x))
  constructor
  · intro x hx
    apply (hJ x).mpr
    rw [cusp_translation_iff _ q σ hσ]
    apply hΓ
    exact (cusp_translation_iff Γ q σ hσ x).mp ((hL x).mp hx)
  · rw [AddSubgroup.isFiniteRelIndex_iff_relIndex_ne_zero,
      ← AddSubgroup.relIndex_toSubgroup, heL, heJ]
    exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp (hcomm.1.comap f)
end DedekindZetaZeroFree.KPCuspParabolicLattices.Translations

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.Multipliers
variable {F : Type*} [Field F] [NumberField F]
local notation "R" => IntegralOrder F
def multiplier (M : Submodule R (Plane F)) (f : Module.End F (Plane F)) : Submodule R F where
  carrier := {x | ∀ m ∈ M, x • f m ∈ M}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy m hm; simpa [add_smul] using M.add_mem (hx m hm) (hy m hm)
  smul_mem' := by intro r x hx m hm; simpa [smul_assoc] using M.smul_mem r (hx m hm)
theorem multiplier_nonzero (M : Submodule R (Plane F)) (hM : FullLattice F M)
    (f : Module.End F (Plane F)) : multiplier M f ≠ ⊥ := by
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.mp hM.1
  have hm : ∀ m : ↥s, ∃ r : R, r ≠ 0 ∧ r • f (m : Plane F) ∈ M := by
    intro m
    obtain ⟨r, hr⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors R) F (M : Set (Plane F)) (f m)
      (by rw [hM.2]; trivial)
    rw [Submodule.span_eq] at hr
    exact ⟨r, nonZeroDivisors.ne_zero r.property, hr⟩
  choose r hr hrf using hm
  let p : R := ∏ m : ↥s, r m
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun m _ => hr m)
  have hpM : algebraMap R F p ∈ multiplier M f := by
    intro m hm
    have ht : ∀ m ∈ s, p • f m ∈ M := by
      intro m hm
      let i : ↥s := ⟨m, hm⟩
      have he : p = (∏ j ∈ Finset.univ.erase i, r j) * r i :=
        (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
      rw [he, mul_smul]
      exact M.smul_mem _ (hrf i)
    rw [← hs] at hm
    induction hm using Submodule.span_induction with
    | mem m hm => simpa only [algebraMap_smul] using ht m hm
    | zero => simp
    | add x y _ _ hx hy => simpa [map_add, smul_add] using M.add_mem hx hy
    | smul a x _ hx =>
      rw [f.map_smul_of_tower a x, smul_comm]
      exact M.smul_mem a hx
  intro hz
  rw [hz] at hpM
  have h0 : algebraMap R F p = 0 := hpM
  exact hp ((IsFractionRing.injective R F) (by simpa using h0))
theorem multiplier_fractional (M : Submodule R (Plane F)) (hM : FullLattice F M)
    (f : Module.End F (Plane F)) (hf : f ≠ 0) :
    IsFractional (nonZeroDivisors R) (multiplier M f) := by
  have hm : ∃ m ∈ M, f m ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hf
    apply LinearMap.ext
    intro v
    change f v = 0
    have hv : v ∈ Submodule.span F (M : Set (Plane F)) := by rw [hM.2]; trivial
    induction hv using Submodule.span_induction with
    | mem m hm => exact hn m hm
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul a x _ hx => simp [map_smul, hx]
  obtain ⟨m, hm, hfm⟩ := hm
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, f m i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hfm (funext hn)
  let ev : Plane F →ₗ[R] F := (LinearMap.proj i : Plane F →ₗ[F] F).restrictScalars R
  let I : FractionalIdeal (nonZeroDivisors R) F :=
    ⟨M.map ev, FractionalIdeal.isFractional_of_fg ((Module.Finite.iff_fg.mp hM.1).map ev)⟩
  apply FractionalIdeal.isFractional_of_le
    (J := FractionalIdeal.spanSingleton (nonZeroDivisors R) (f m i)⁻¹ * I)
  intro x hx
  apply FractionalIdeal.mem_singleton_mul.mpr
  refine ⟨x * f m i, ?_, ?_⟩
  · exact ⟨x • f m, hx m hm, rfl⟩
  · field_simp
theorem shear_preserves_iff (M : Submodule R (Plane F))
    (f : Module.End F (Plane F)) (hff : ∀ v, f (f v) = 0) (x : F) :
    (∀ v, v ∈ M ↔ v + x • f v ∈ M) ↔ x ∈ multiplier M f := by
  constructor
  · intro h v hv
    simpa using M.sub_mem ((h v).mp hv) hv
  · intro hx v
    constructor
    · intro hv
      exact M.add_mem hv (hx v hv)
    · intro hv
      have hm := hx (v + x • f v) hv
      have he : f (v + x • f v) = f v := by simp [map_add, map_smul, hff]
      rw [he] at hm
      simpa using M.sub_mem hv hm
end DedekindZetaZeroFree.KPCuspParabolicLattices.Multipliers

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.LatticeConjugation
variable {F : Type*} [Field F] [NumberField F]
local notation "R" => IntegralOrder F
def matrixAut (M : Submodule R (Plane F)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F) where
  carrier := {A | ∀ v, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hB v).trans (hA _)
  inv_mem' := by
    intro A hA v
    have h := hA ((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm
theorem latticeAut_eq (M : Submodule R (Plane F)) :
    LatticeAutomorphisms F M = (matrixAut M).map Matrix.ProjGenLinGroup.mk := by
  have he : {g : ProjectiveGroup F | ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
      Matrix.ProjGenLinGroup.mk A = g ∧ ∀ v, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M} =
      ((matrixAut M).map Matrix.ProjGenLinGroup.mk : Set (ProjectiveGroup F)) := by
    ext g
    simp only [Set.mem_setOf_eq, Subgroup.mem_map]
    constructor
    · rintro ⟨A, rfl, hA⟩; exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩; exact ⟨A, rfl, hA⟩
  unfold LatticeAutomorphisms
  rw [he, Subgroup.closure_eq]
theorem scalar_preserves (M : Submodule R (Plane F)) (u : Fˣ)
    (hu : u ∈ IntegralUnits F) (v : Plane F) : v ∈ M ↔ (u : F) • v ∈ M := by
  obtain ⟨r, hr⟩ := hu
  have he : (u : F) = algebraMap R F (r : R) := congrArg Units.val hr.symm
  have hei : (↑u⁻¹ : F) = algebraMap R F (↑r⁻¹ : R) := by
    have h := congrArg (fun z : Fˣ => (↑z⁻¹ : F)) hr.symm
    exact h
  constructor
  · intro hv
    rw [he, algebraMap_smul]
    exact M.smul_mem r hv
  · intro hv
    have hm := M.smul_mem (↑r⁻¹ : R) hv
    rw [← algebraMap_smul F, ← hei, smul_smul] at hm
    simpa using hm
theorem projective_preserves_of_eigen_one
    (M : Submodule R (Plane F)) (hM : FullLattice F M)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (hv : ∃ v : Plane F, v ≠ 0 ∧ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v) :
    Matrix.ProjGenLinGroup.mk A ∈ LatticeAutomorphisms F M ↔ A ∈ matrixAut M := by
  constructor
  · intro hA
    rw [latticeAut_eq, Subgroup.mem_map] at hA
    obtain ⟨C, hC, hp⟩ := hA
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp.symm
    have hCv (v : Plane F) : (C : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
        (u : F) • ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
      rw [← hu, Units.val_mul, ← Matrix.mulVec_mulVec]
      have hs : (↑(Matrix.GeneralLinearGroup.scalar (Fin 2) u) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = (u : F) • v := by
        ext i
        simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal]
      rw [hs, Matrix.mulVec_smul]
    have hui : u ∈ IntegralUnits F := by
      apply eigen_unit_integral_of_fullLattice M hM (Matrix.GeneralLinearGroup.toLin C).toLinearEquiv
      · exact hC
      · obtain ⟨v, hv0, hAv⟩ := hv
        apply Module.End.hasEigenvalue_of_hasEigenvector
        refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv0⟩
        change (C : Matrix (Fin 2) (Fin 2) F) *ᵥ v = (u : F) • v
        rw [hCv, hAv]
    intro v
    have hc := hC v
    rw [hCv, ← scalar_preserves M u hui] at hc
    exact hc
  · intro hA
    rw [latticeAut_eq, Subgroup.mem_map]
    exact ⟨A, hA, rfl⟩
end DedekindZetaZeroFree.KPCuspParabolicLattices.LatticeConjugation

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.LatticeConjugation
variable {F : Type*} [Field F] [NumberField F]
local notation "R" => IntegralOrder F
open Translations Multipliers
def rootEnd : Module.End F (Plane F) := Matrix.mulVecLin !![0, 1; 0, 0]
def conjEnd (B : Matrix.GeneralLinearGroup (Fin 2) F) : Module.End F (Plane F) :=
  (Matrix.GeneralLinearGroup.toLin B : Module.End F (Plane F)).comp
    (rootEnd.comp (Matrix.GeneralLinearGroup.toLin B⁻¹ : Module.End F (Plane F)))
theorem rootEnd_formula (v : Plane F) : rootEnd v = ![v 1, 0] := by
  ext i
  fin_cases i <;> simp [rootEnd, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
theorem rootEnd_square (v : Plane F) : rootEnd (rootEnd v) = 0 := by
  simp [rootEnd_formula]
theorem inv_mulVec (B : Matrix.GeneralLinearGroup (Fin 2) F) (v : Plane F) :
    (↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
theorem mul_invVec (B : Matrix.GeneralLinearGroup (Fin 2) F) (v : Plane F) :
    (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
theorem conjEnd_formula (B : Matrix.GeneralLinearGroup (Fin 2) F) (v : Plane F) :
    conjEnd B v = (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ rootEnd ((↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := rfl
theorem conjEnd_square (B : Matrix.GeneralLinearGroup (Fin 2) F) (v : Plane F) :
    conjEnd B (conjEnd B v) = 0 := by
  simp only [conjEnd_formula, inv_mulVec, rootEnd_square, Matrix.mulVec_zero]
theorem conjEnd_ne (B : Matrix.GeneralLinearGroup (Fin 2) F) : conjEnd B ≠ 0 := by
  intro hz
  have he := congrArg (fun f : Module.End F (Plane F) => f ((↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ ![0, 1])) hz
  simp only [conjEnd_formula, inv_mulVec, rootEnd_formula, Matrix.cons_val_one,
    Matrix.cons_val_zero, LinearMap.zero_apply] at he
  have he' := congrArg (fun v => (↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) he
  simp only [inv_mulVec, Matrix.mulVec_zero] at he'
  have h := congrFun he' 0
  simpa using h
theorem unipotent_vec (x : F) (v : Plane F) :
    (↑(unipotent x) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v + x • rootEnd v := by
  ext i
  fin_cases i <;> simp [rootEnd_formula, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
theorem conj_unipotent_vec (B : Matrix.GeneralLinearGroup (Fin 2) F) (x : F) (v : Plane F) :
    (↑(B * unipotent x * B⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v + x • conjEnd B v := by
  rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    unipotent_vec, Matrix.mulVec_add, Matrix.mulVec_smul, mul_invVec, conjEnd_formula]
theorem conj_unipotent_eigen (B : Matrix.GeneralLinearGroup (Fin 2) F) (x : F) :
    ∃ v : Plane F, v ≠ 0 ∧ (↑(B * unipotent x * B⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = v := by
  refine ⟨(↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0], ?_, ?_⟩
  · intro hz
    have he := congrArg (fun v => (↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) hz
    simp only [inv_mulVec, Matrix.mulVec_zero] at he
    have h := congrFun he 0
    simpa using h
  · rw [conj_unipotent_vec]
    have he : conjEnd B ((↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) = 0 := by
      rw [conjEnd_formula, inv_mulVec, rootEnd_formula]
      change (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ (0 : Plane F) = 0
      exact Matrix.mulVec_zero _
    rw [he, smul_zero, add_zero]
theorem full_translation_ideal (M : Submodule R (Plane F)) (hM : FullLattice F M)
    (q : Projectivization F (Plane F)) (σ : ProjectiveGroup F)
    (hσ : σ • StandardCusp F = q) :
    ∃ J : FractionalIdeal R⁰ F, J ≠ 0 ∧ ∀ x : F,
      x ∈ J ↔ TranslationParameter (CuspSubgroup F (LatticeAutomorphisms F M) q σ) x := by
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  let J : FractionalIdeal R⁰ F := ⟨multiplier M (conjEnd B), multiplier_fractional M hM _ (conjEnd_ne B)⟩
  refine ⟨J, ?_, ?_⟩
  · intro hz
    apply multiplier_nonzero M hM (conjEnd B)
    have he := congrArg (fun I : FractionalIdeal R⁰ F => (I : Submodule R F)) hz
    rw [FractionalIdeal.coe_zero] at he
    exact he
  · intro x
    rw [cusp_translation_iff _ _ _ hσ]
    change x ∈ multiplier M (conjEnd B) ↔ σ * Matrix.ProjGenLinGroup.mk (unipotent x) * σ⁻¹ ∈ LatticeAutomorphisms F M
    rw [← hB, ← map_inv, ← map_mul, ← map_mul]
    rw [projective_preserves_of_eigen_one M hM _ (conj_unipotent_eigen B x)]
    change x ∈ multiplier M (conjEnd B) ↔ ∀ v, v ∈ M ↔ _
    simp only [conj_unipotent_vec]
    exact (shear_preserves_iff M (conjEnd B) (conjEnd_square B) x).symm
end DedekindZetaZeroFree.KPCuspParabolicLattices.LatticeConjugation

namespace DedekindZetaZeroFree.KPCuspParabolicLattices

theorem translation_fractional_ideal
    (F : Type*) [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (Γ : Subgroup (ProjectiveGroup F))
    (hΓ : Γ ≤ LatticeAutomorphisms F M)
    (hcomm : Γ.Commensurable (LatticeAutomorphisms F M))
    (q : Projectivization F (Plane F))
    (σ : ProjectiveGroup F) (hσ : σ • StandardCusp F = q)
    (L : AddSubgroup F)
    (hL : ∀ x : F, x ∈ L ↔ TranslationParameter (CuspSubgroup F Γ q σ) x) :
    ∃ J : FractionalIdeal (IntegralOrder F)⁰ F,
      J ≠ 0 ∧ L ≤ (J : Submodule (IntegralOrder F) F).toAddSubgroup ∧
      L.IsFiniteRelIndex (J : Submodule (IntegralOrder F) F).toAddSubgroup := by
  obtain ⟨J, hJ, hm⟩ := LatticeConjugation.full_translation_ideal M hM q σ hσ
  obtain ⟨hle, hfinite⟩ := Translations.translation_finite_index_of_full_ideal M Γ hΓ hcomm q σ hσ L hL J hm
  exact ⟨J, hJ, hle, hfinite⟩

end DedekindZetaZeroFree.KPCuspParabolicLattices

end
end

section

noncomputable section
open scoped Classical nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspParabolicLattices

private theorem isZLattice_of_commensurable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L J : AddSubgroup V) (h : L.Commensurable J)
    [DiscreteTopology J.toIntSubmodule] [IsZLattice ℝ J.toIntSubmodule] :
    ∃ hd : DiscreteTopology L.toIntSubmodule, letI := hd; IsZLattice ℝ L.toIntSubmodule := by
  haveI : DiscreteTopology J := by
    change DiscreteTopology {x : V // x ∈ (J : Set V)}
    rw [← AddSubgroup.coe_toIntSubmodule]
    exact (inferInstance : DiscreteTopology J.toIntSubmodule)
  haveI : DiscreteTopology L := h.discreteTopology_iff.mpr inferInstance
  have hd : DiscreteTopology L.toIntSubmodule := by
    change DiscreteTopology {x : V // x ∈ (L.toIntSubmodule : Set V)}
    rw [AddSubgroup.coe_toIntSubmodule]
    exact (inferInstance : DiscreteTopology L)
  letI := hd
  refine ⟨hd, ?_⟩
  constructor
  apply top_unique
  rw [← IsZLattice.span_top (K := ℝ) (L := J.toIntSubmodule)]
  apply Submodule.span_le.mpr
  intro x hx
  change x ∈ J at hx
  obtain ⟨n, hn, _, hm⟩ := AddSubgroup.exists_nsmul_mem_of_relIndex_ne_zero
    h.1.relIndex_ne_zero hx
  have hs : (n : ℝ) • x ∈ Submodule.span ℝ (L.toIntSubmodule : Set V) := by
    rw [Nat.cast_smul_eq_nsmul]
    exact Submodule.subset_span hm.1
  have hh := (Submodule.span ℝ (L.toIntSubmodule : Set V)).smul_mem (n : ℝ)⁻¹ hs
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  rw [smul_smul, inv_mul_cancel₀ hn', one_smul] at hh
  exact hh

theorem finite_index_ideal_isZLattice
    (F : Type*) [Field F] [NumberField F]
    (J : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) (hJ : J ≠ 0)
    (L : AddSubgroup F)
    (hL : L ≤ (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup)
    (hindex : L.IsFiniteRelIndex
      (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup) :
    ∃ hdisc : DiscreteTopology
        ((L.map (NumberField.mixedEmbedding F).toAddMonoidHom).toIntSubmodule),
      letI := hdisc
      IsZLattice ℝ ((L.map (NumberField.mixedEmbedding F).toAddMonoidHom).toIntSubmodule) := by
  let f := (NumberField.mixedEmbedding F).toAddMonoidHom
  let I : (FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)ˣ := Units.mk0 J hJ
  have hI : (↑I : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) = J := rfl
  let J' : AddSubgroup (NumberField.mixedEmbedding.mixedSpace F) :=
    (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup.map f

  have hcomm : (L.map f).Commensurable J' := by
    have hc : L.Commensurable (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup :=
      ⟨hindex, AddSubgroup.isFiniteRelIndex_of_le_right
        (H := (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup) (K := L)
        (L := (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup) hL⟩
    exact ⟨AddSubgroup.IsFiniteRelIndex.map f hc.1, AddSubgroup.IsFiniteRelIndex.map f hc.2⟩

  have hJ' : J'.toIntSubmodule = NumberField.mixedEmbedding.idealLattice F I := by
    ext x
    rw [NumberField.mixedEmbedding.mem_idealLattice, hI]
    constructor
    · intro hx
      change x ∈ J' at hx
      change x ∈ (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup.map f at hx
      rw [AddSubgroup.mem_map] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      exact ⟨y, by simpa using hy, hyx⟩
    · rintro ⟨y, hy, rfl⟩
      change (NumberField.mixedEmbedding F) y ∈ J'
      change (NumberField.mixedEmbedding F) y ∈
        (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup.map f
      rw [AddSubgroup.mem_map]
      exact ⟨y, by simpa using hy, rfl⟩
  haveI hd : DiscreteTopology J'.toIntSubmodule := by
    rw [hJ']; infer_instance
  haveI hz : IsZLattice ℝ J'.toIntSubmodule :=
    { span_top := by
        have hset : (J'.toIntSubmodule : Set (NumberField.mixedEmbedding.mixedSpace F)) =
            (NumberField.mixedEmbedding.idealLattice F I :
              Set (NumberField.mixedEmbedding.mixedSpace F)) := by rw [hJ']
        rw [hset]
        exact (inferInstance : IsZLattice ℝ
          (NumberField.mixedEmbedding.idealLattice F I)).span_top }
  exact isZLattice_of_commensurable (L.map f) J' hcomm

end DedekindZetaZeroFree.KPCuspParabolicLattices

end
end

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization nonZeroDivisors

namespace DedekindZetaZeroFree
namespace KPCuspArithmetic

variable (F : Type*) [Field F] [NumberField F]

abbrev Vec := Fin 2 → F

abbrev Cusp := Projectivization F (Vec F)
abbrev Order := NumberField.RingOfIntegers F

def IsRankTwoLattice (M : Submodule (Order F) (Vec F)) : Prop :=
  Module.Finite (Order F) M ∧ Submodule.span F (M : Set (Vec F)) = ⊤

def projectiveAutomorphisms (M : Submodule (Order F) (Vec F)) : Subgroup (PGL2 F) :=
  Subgroup.closure {g | ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
    Matrix.ProjGenLinGroup.mk A = g ∧
      ∀ v : Vec F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M}

def PreservesUpToHomothety (M : Submodule (Order F) (Vec F)) (g : PGL2 F) : Prop :=
  ∃ (A : Matrix.GeneralLinearGroup (Fin 2) F) (a : Fˣ),
    Matrix.ProjGenLinGroup.mk A = g ∧
    Set.image (fun v : Vec F => (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) (M : Set (Vec F)) =
      Set.image (fun v : Vec F => (a : F) • v) (M : Set (Vec F))

def infinity : Cusp F :=
  Projectivization.mk F ![1, 0] (by simp [Matrix.cons_val_zero])

def conjugatedStabilizer (Γ : Subgroup (PGL2 F)) (q : Cusp F) (σ : PGL2 F) :
    Subgroup (PGL2 F) :=
  (Γ ⊓ MulAction.stabilizer (PGL2 F) q).map (MulAut.conj σ⁻¹).toMonoidHom

def IsUpperTriangular (g : PGL2 F) : Prop :=
  ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
    Matrix.ProjGenLinGroup.mk A = g ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0

def rationalUnits : Subgroup Fˣ :=
  (Units.map (algebraMap (Order F) F).toMonoidHom).range

private def integralMatrixAutomorphisms (M : Submodule (Order F) (Vec F)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) F) where
  carrier := {A | ∀ v : Vec F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB v
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hB v).trans (hA _)
  inv_mem' := by
    intro A hA v
    have h := hA ((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at h
    exact h.symm

theorem mem_projectiveAutomorphisms_iff (M : Submodule (Order F) (Vec F)) (g : PGL2 F) :
    g ∈ projectiveAutomorphisms F M ↔
      ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
        Matrix.ProjGenLinGroup.mk A = g ∧
          ∀ v : Vec F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M := by
  have hset : {g : PGL2 F | ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
      Matrix.ProjGenLinGroup.mk A = g ∧
        ∀ v : Vec F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M} =
      ((integralMatrixAutomorphisms F M).map Matrix.ProjGenLinGroup.mk : Set (PGL2 F)) := by
    ext g
    simp only [Set.mem_setOf_eq, Subgroup.mem_map]
    constructor
    · rintro ⟨A, rfl, hA⟩; exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩; exact ⟨A, rfl, hA⟩
  unfold projectiveAutomorphisms
  rw [hset, Subgroup.closure_eq]
  change g ∈ (((integralMatrixAutomorphisms F M).map Matrix.ProjGenLinGroup.mk) : Set (PGL2 F)) ↔ _
  rw [← hset]
  rfl

private theorem inv_mulVec_mulVec (A : Matrix.GeneralLinearGroup (Fin 2) F) (v : Vec F) :
    (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec]

private theorem scalar_mulVec (a : Fˣ) (v : Vec F) :
    (↑(Matrix.GeneralLinearGroup.scalar (Fin 2) a) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = (a : F) • v := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.scalar, Matrix.diagonal, Pi.smul_apply]

theorem preservesUpToHomothety_iff_mem_projectiveAutomorphisms
    (M : Submodule (Order F) (Vec F)) (g : PGL2 F) :
    PreservesUpToHomothety F M g ↔ g ∈ projectiveAutomorphisms F M := by
  rw [mem_projectiveAutomorphisms_iff]
  constructor
  · rintro ⟨A, a, hA, him⟩
    let B := Matrix.GeneralLinearGroup.scalar (Fin 2) a⁻¹ * A
    have hBv (v : Vec F) : (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
        ((a⁻¹ : Fˣ) : F) • ((↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, scalar_mulVec]
    refine ⟨B, ?_, ?_⟩
    · simp [B, map_mul, hA]
    · intro v
      constructor
      · intro hv
        have hm : (↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈
            Set.image (fun v : Vec F => (a : F) • v) (M : Set (Vec F)) := by
          rw [← him]; exact ⟨v, hv, rfl⟩
        obtain ⟨w, hw, he⟩ := hm
        rw [hBv, ← he, smul_smul, Units.inv_mul, one_smul]
        exact hw
      · intro hv
        have hm : (↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈
            Set.image (fun v : Vec F => (a : F) • v) (M : Set (Vec F)) := by
          refine ⟨(↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v, hv, ?_⟩
          change (a : F) • ((↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = _
          rw [hBv, smul_smul, Units.mul_inv, one_smul]
        rw [← him] at hm
        obtain ⟨w, hw, he⟩ := hm
        have he' := congrArg (fun z => (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ z) he
        rw [inv_mulVec_mulVec, inv_mulVec_mulVec] at he'
        exact he' ▸ hw
  · rintro ⟨A, hA, hp⟩
    refine ⟨A, 1, hA, ?_⟩
    simp only [Units.val_one, one_smul, Set.image_id']
    apply Set.Subset.antisymm
    · rintro _ ⟨v, hv, rfl⟩; exact (hp v).mp hv
    · intro v hv
      refine ⟨(↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v, ?_, ?_⟩
      · apply (hp _).mpr
        simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using hv
      · simp [Matrix.mulVec_mulVec, ← Units.val_mul]

theorem subgroup_le_projectiveAutomorphisms
    (M : Submodule (Order F) (Vec F)) (Γ : Subgroup (PGL2 F))
    (hΓ : ∀ g ∈ Γ, PreservesUpToHomothety F M g) :
    Γ ≤ projectiveAutomorphisms F M := by
  intro g hg
  exact (preservesUpToHomothety_iff_mem_projectiveAutomorphisms F M g).mp (hΓ g hg)

def rationalMatrixLinearEquiv (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    Vec F ≃ₗ[Order F] Vec F :=
  (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.restrictScalars (Order F)

private theorem gl_mulVec_mul (A B : Matrix.GeneralLinearGroup (Fin 2) F) (v : Vec F) :
    (↑(A * B) : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
      (↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
  rw [Units.val_mul, Matrix.mulVec_mulVec]

private theorem gl_inv_mulVec (A : Matrix.GeneralLinearGroup (Fin 2) F) (v : Vec F) :
    (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
  rw [← gl_mulVec_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem projectiveAutomorphisms_conjugate
    (M : Submodule (Order F) (Vec F)) (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    (projectiveAutomorphisms F M).map
        (MulAut.conj (Matrix.ProjGenLinGroup.mk A)).toMonoidHom =
      projectiveAutomorphisms F (M.map (rationalMatrixLinearEquiv F A).toLinearMap) := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨B, hB, hp⟩ := (mem_projectiveAutomorphisms_iff F M k).mp hk
    rw [mem_projectiveAutomorphisms_iff]
    refine ⟨A * B * A⁻¹, ?_, ?_⟩
    · simp [map_mul, map_inv, hB, MulAut.conj_apply]
    · intro v
      have hmem (v : Vec F) : v ∈ M.map (rationalMatrixLinearEquiv F A).toLinearMap ↔
          (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M := by
        constructor
        · rintro ⟨w, hw, rfl⟩
          change (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ w) ∈ M
          rw [gl_inv_mulVec]
          exact hw
        · intro hv
          refine ⟨(↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v, hv, ?_⟩
          change (↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v
          simpa using gl_inv_mulVec F A⁻¹ v
      rw [hmem, hmem, gl_mulVec_mul, gl_mulVec_mul, gl_inv_mulVec]
      exact hp _
  · intro hg
    obtain ⟨B, hB, hp⟩ := (mem_projectiveAutomorphisms_iff F _ g).mp hg
    apply Subgroup.mem_map.mpr
    refine ⟨Matrix.ProjGenLinGroup.mk (A⁻¹ * B * A), ?_, ?_⟩
    · rw [mem_projectiveAutomorphisms_iff]
      refine ⟨A⁻¹ * B * A, rfl, ?_⟩
      intro v
      have hmem (w : Vec F) : (↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ w ∈
          M.map (rationalMatrixLinearEquiv F A).toLinearMap ↔ w ∈ M := by
        constructor
        · rintro ⟨z, hz, he⟩
          have he' := congrArg (fun t => (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ t) he
          change (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ z) =
            (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ w) at he'
          rw [gl_inv_mulVec, gl_inv_mulVec] at he'
          exact he' ▸ hz
        · intro hw; exact ⟨w, hw, rfl⟩
      rw [← hmem v, ← hmem ((↑(A⁻¹ * B * A) : Matrix (Fin 2) (Fin 2) F) *ᵥ v)]
      rw [gl_mulVec_mul, gl_mulVec_mul]
      have hinv (w : Vec F) : (↑A : Matrix (Fin 2) (Fin 2) F) *ᵥ
          ((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ w) = w := by
        simpa using gl_inv_mulVec F A⁻¹ w
      rw [hinv]
      exact hp _
    · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
      simp only [map_mul, map_inv]
      simp [mul_assoc, hB]

theorem isRankTwoLattice_map (M : Submodule (Order F) (Vec F))
    (hM : IsRankTwoLattice F M) (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    IsRankTwoLattice F (M.map (rationalMatrixLinearEquiv F A).toLinearMap) := by
  constructor
  · letI := hM.1
    exact Module.Finite.of_surjective _
      ((rationalMatrixLinearEquiv F A).toLinearMap.submoduleMap_surjective M)
  · have hmap : Submodule.span F (M.map (rationalMatrixLinearEquiv F A).toLinearMap : Set (Vec F)) =
        (Submodule.span F (M : Set (Vec F))).map
          (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.toLinearMap := by
      rw [Submodule.map_span]
      rfl
    rw [hmap, hM.2]
    rw [Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Matrix.GeneralLinearGroup.toLin A).toLinearEquiv.surjective

 theorem fixes_infinity_upper (g : PGL2 F) (hg : g • infinity F = infinity F) :
    IsUpperTriangular F g := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  refine ⟨A, rfl, ?_⟩
  unfold infinity at hg
  rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff] at hg
  obtain ⟨a, ha⟩ := hg
  have h := congrFun ha 1
  have hzero : (a • ![1, 0]) 1 = (0 : F) := by simp
  rw [hzero] at h
  change 0 = ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) 1 at h
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm
private theorem conjugated_upper (Γ : Subgroup (PGL2 F)) (q : Cusp F) (σ : PGL2 F)
    (hσ : σ • infinity F = q) :
    ∀ g ∈ conjugatedStabilizer F Γ q σ, IsUpperTriangular F g := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
  apply fixes_infinity_upper
  have hkq : k • q = q := hk.2
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
  change (σ⁻¹ * k * σ) • infinity F = infinity F
  rw [mul_smul, mul_smul, hσ, hkq, ← hσ, inv_smul_smul]

end KPCuspArithmetic

theorem kp_cusp_arithmetic_parabolic_stabilizers
    (F : Type*) [Field F] [NumberField F]
    (M : Submodule (KPCuspArithmetic.Order F) (KPCuspArithmetic.Vec F))
    (hM : KPCuspArithmetic.IsRankTwoLattice F M)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hΓ : ∀ g ∈ Γ, KPCuspArithmetic.PreservesUpToHomothety F M g)
    (hcomm : Γ.Commensurable (KPCuspArithmetic.projectiveAutomorphisms F M))
    (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (hσ : σ • KPCuspArithmetic.infinity F = q) :
    let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
    (∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) ∧
    ∃ (J : FractionalIdeal (KPCuspArithmetic.Order F)⁰ F) (L : AddSubgroup F)
      (E : Subgroup Fˣ) (ι : Multiplicative L →* S) (ρ : S →* E),
      J ≠ 0 ∧
      L ≤ (J : Submodule (KPCuspArithmetic.Order F) F).toAddSubgroup ∧
      L.IsFiniteRelIndex (J : Submodule (KPCuspArithmetic.Order F) F).toAddSubgroup ∧
      (∃ hdisc : DiscreteTopology ((L.map (NumberField.mixedEmbedding F).toAddMonoidHom).toIntSubmodule),
        letI := hdisc
        IsZLattice ℝ ((L.map (NumberField.mixedEmbedding F).toAddMonoidHom).toIntSubmodule)) ∧
      E ≤ KPCuspArithmetic.rationalUnits F ∧
      (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex ∧
      Function.Injective ι ∧ Function.Surjective ρ ∧ ι.range = ρ.ker ∧
      (∀ x : L, ∀ A : Matrix.GeneralLinearGroup (Fin 2) F,
        Matrix.ProjGenLinGroup.mk A = (ι (Multiplicative.ofAdd x) : KPCuspArithmetic.PGL2 F) →
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 = (x : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 0) ∧
      (∀ g : S, ∀ A : Matrix.GeneralLinearGroup (Fin 2) F,
        Matrix.ProjGenLinGroup.mk A = (g : KPCuspArithmetic.PGL2 F) →
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 = ((ρ g : Fˣ) : F) *
          (A : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
  have hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g :=
    KPCuspArithmetic.conjugated_upper F Γ q σ hσ
  refine ⟨hS, ?_⟩
  obtain ⟨L, E, ι, ρ, hL, hE, hι, hρ, hexact, htranslation, hratio⟩ :=
    KPCuspParabolicLattices.parabolic_exact_sequence S hS
  have hΓle := KPCuspArithmetic.subgroup_le_projectiveAutomorphisms F M Γ hΓ
  obtain ⟨J, hJ, hLle, hLindex⟩ :=
    KPCuspParabolicLattices.translation_fractional_ideal F M hM Γ hΓle hcomm q σ hσ L hL
  have hunit :=
    KPCuspParabolicLattices.ratio_integral_units F M hM Γ hΓle hcomm q σ hσ E hE
  have hlattice :=
    KPCuspParabolicLattices.finite_index_ideal_isZLattice F J hJ L hLle hLindex
  exact ⟨J, L, E, ι, ρ, hJ, hLle, hLindex, hlattice, hunit.1, hunit.2,
    hι, hρ, hexact, htranslation, hratio⟩

end DedekindZetaZeroFree

end
end
