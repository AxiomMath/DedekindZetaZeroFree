module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.GroupTheory.Commensurable

@[expose] public section

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspParabolicLattices

abbrev Plane (F : Type*) := Fin 2 → F
abbrev ProjectiveGroup (F : Type*) [Field F] := Matrix.ProjGenLinGroup (Fin 2) F
abbrev IntegralOrder (F : Type*) [Field F] [NumberField F] := NumberField.RingOfIntegers F

def Upper {F : Type*} [Field F] (g : ProjectiveGroup F) : Prop :=
  ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
    Matrix.ProjGenLinGroup.mk A = g ∧ (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0

def TranslationParameter {F : Type*} [Field F] (S : Subgroup (ProjectiveGroup F))
    (x : F) : Prop :=
  ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
    Matrix.ProjGenLinGroup.mk A ∈ S ∧
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
    (A : Matrix (Fin 2) (Fin 2) F) 0 1 = x * (A : Matrix (Fin 2) (Fin 2) F) 0 0

def RatioParameter {F : Type*} [Field F] (S : Subgroup (ProjectiveGroup F))
    (u : Fˣ) : Prop :=
  ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
    Matrix.ProjGenLinGroup.mk A ∈ S ∧
    (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (u : F) * (A : Matrix (Fin 2) (Fin 2) F) 1 1

 theorem diagonal_ne_zero {F : Type*} [Field F]
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (h : A 1 0 = 0) :
    A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 := by
  constructor <;> intro hz <;> exact A.det_ne_zero (by simp [Matrix.det_fin_two, h, hz])
private theorem ratio_eq {F : Type*} [Field F]
    (A B : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B) :
    A 0 0 / A 1 1 = B 0 0 / B 1 1 := by
  obtain ⟨u, rfl⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
    Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
  simp
  rw [mul_div_mul_right _ _ (Units.ne_zero u)]
 def representative {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (g : S) :=
  Classical.choose (hS g g.property)
private theorem representative_mk {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (g : S) :
    Matrix.ProjGenLinGroup.mk (representative S hS g) = g :=
  (Classical.choose_spec (hS g g.property)).1
 theorem representative_upper {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (g : S) :
    representative S hS g 1 0 = 0 :=
  (Classical.choose_spec (hS g g.property)).2
 def ratioValue {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (g : S) : F :=
  representative S hS g 0 0 / representative S hS g 1 1
private theorem ratioValue_formula {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : Matrix.ProjGenLinGroup.mk A = g) :
    ratioValue S hS g = A 0 0 / A 1 1 :=
  ratio_eq _ _ ((representative_mk S hS g).trans hA.symm)
 theorem ratioValue_one {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) :
    ratioValue S hS 1 = 1 := by
  rw [ratioValue_formula S hS 1 1 (by simp)]
  simp
 theorem ratioValue_mul {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (g h : S) :
    ratioValue S hS (g*h) = ratioValue S hS g * ratioValue S hS h := by
  let A := representative S hS g
  let B := representative S hS h
  have hA : A 1 0 = 0 := representative_upper S hS g
  have hB : B 1 0 = 0 := representative_upper S hS h
  rw [ratioValue_formula S hS (g*h) (A*B) (by
    rw [map_mul, representative_mk, representative_mk]; rfl)]
  change (A*B) 0 0 / (A*B) 1 1 = (A 0 0 / A 1 1) * (B 0 0 / B 1 1)
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hA, hB,
    mul_zero, zero_mul, add_zero, zero_add]
  exact mul_div_mul_comm _ _ _ _

 def upperRatio {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) : S →* Fˣ where
  toFun g := Units.mk0 (ratioValue S hS g) (by
    exact div_ne_zero (diagonal_ne_zero _ (representative_upper S hS g)).1
      (diagonal_ne_zero _ (representative_upper S hS g)).2)
  map_one' := by apply Units.ext; exact ratioValue_one S hS
  map_mul' g h := by apply Units.ext; exact ratioValue_mul S hS g h

private theorem upperRatio_formula {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : Matrix.ProjGenLinGroup.mk A = g)
    (hu : A 1 0 = 0) : A 0 0 = (upperRatio S hS g : F) * A 1 1 := by
  change A 0 0 = ratioValue S hS g * A 1 1
  rw [ratioValue_formula S hS g A hA]
  exact (div_mul_cancel₀ _ (diagonal_ne_zero A hu).2).symm

 def cuspTranslationMatrix {F : Type*} [Field F] (x : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])
 theorem translationMatrix_mul {F : Type*} [Field F] (x y : F) :
    cuspTranslationMatrix (x+y) = cuspTranslationMatrix x * cuspTranslationMatrix y := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

 def cuspTranslation {F : Type*} [Field F] : Multiplicative F →* ProjectiveGroup F where
  toFun x := Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix x.toAdd)
  map_one' := by
    change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix 0) = 1
    have h : cuspTranslationMatrix (0 : F) = 1 := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [cuspTranslationMatrix]
    rw [h, map_one]
  map_mul' x y := by
    change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix (x.toAdd+y.toAdd)) = _
    rw [translationMatrix_mul, map_mul]

private theorem cuspTranslation_injective {F : Type*} [Field F] :
    Function.Injective (cuspTranslation (F := F)) := by
  intro x y h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h00 := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) F => A 0 0) hu
  have h01 := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) F => A 0 1) hu
  simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  change x.toAdd = y.toAdd
  simpa only [h00, Units.val_one, mul_one] using h01

 def cuspTranslationLattice {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F)) : AddSubgroup F :=
  (S.comap cuspTranslation).toAddSubgroup

 def cuspTranslationInclusion {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F)) :
    Multiplicative (cuspTranslationLattice S) →* S where
  toFun x := ⟨cuspTranslation (Multiplicative.ofAdd (x.toAdd : F)), x.toAdd.property⟩
  map_one' := by apply Subtype.ext; exact map_one cuspTranslation
  map_mul' x y := by apply Subtype.ext; exact map_mul cuspTranslation _ _
private theorem cuspTranslationInclusion_injective {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F)) :
    Function.Injective (cuspTranslationInclusion S) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact cuspTranslation_injective (congrArg Subtype.val h)

private theorem cuspTranslationInclusion_formula {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F)) (x : cuspTranslationLattice S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = cuspTranslationInclusion S (Multiplicative.ofAdd x)) :
    A 1 0 = 0 ∧ A 0 0 = A 1 1 ∧ A 0 1 = (x : F) * A 0 0 := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h.symm
  change cuspTranslationMatrix (x : F) * Matrix.GeneralLinearGroup.scalar (Fin 2) u = A at hu
  rw [← hu]
  simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
private theorem ratio_one_translation {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g)
    (g : S) (hg : upperRatio S hS g = 1) :
    ∃ x : F, cuspTranslation (Multiplicative.ofAdd x) = g := by
  obtain ⟨A, hA, hu⟩ := hS g g.property
  have hn : A 1 1 ≠ 0 := by
    intro hz; exact A.det_ne_zero (by simp [Matrix.det_fin_two, hu, hz])
  have hd : A 0 0 = A 1 1 := by
    simpa only [hg, Units.val_one, one_mul] using upperRatio_formula S hS g A hA hu
  refine ⟨A 0 1 / A 1 1, ?_⟩
  change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix (A 0 1 / A 1 1)) = g
  rw [← hA, Matrix.ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 (A 1 1) hn, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two, hd, hu, hn]

private theorem cuspTranslationInclusion_range {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) :
    (cuspTranslationInclusion S).range = (upperRatio S hS).ker := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Units.ext
    have hf := upperRatio_formula S hS (cuspTranslationInclusion S x)
      (cuspTranslationMatrix (x.toAdd : F)) rfl (by simp [cuspTranslationMatrix])
    simpa [cuspTranslationMatrix] using hf.symm
  · intro hg
    obtain ⟨x, hx⟩ := ratio_one_translation S hS g hg
    have hxm : x ∈ cuspTranslationLattice S := by
      change cuspTranslation (Multiplicative.ofAdd x) ∈ S
      rw [hx]; exact g.property
    refine ⟨Multiplicative.ofAdd ⟨x, hxm⟩, ?_⟩
    apply Subtype.ext
    exact hx

theorem parabolic_exact_sequence
    {F : Type*} [Field F] (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) :
    ∃ (L : AddSubgroup F) (E : Subgroup Fˣ)
      (ι : Multiplicative L →* S) (ρ : S →* E),
      (∀ x : F, x ∈ L ↔ TranslationParameter S x) ∧
      (∀ u : Fˣ, u ∈ E ↔ RatioParameter S u) ∧
      Function.Injective ι ∧ Function.Surjective ρ ∧ ι.range = ρ.ker ∧
      (∀ x : L, ∀ A : Matrix.GeneralLinearGroup (Fin 2) F,
        Matrix.ProjGenLinGroup.mk A = (ι (Multiplicative.ofAdd x) : ProjectiveGroup F) →
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 ∧
        (A : Matrix (Fin 2) (Fin 2) F) 0 1 = (x : F) * (A : Matrix (Fin 2) (Fin 2) F) 0 0) ∧
      (∀ g : S, ∀ A : Matrix.GeneralLinearGroup (Fin 2) F,
        Matrix.ProjGenLinGroup.mk A = (g : ProjectiveGroup F) →
        (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 →
        (A : Matrix (Fin 2) (Fin 2) F) 0 0 = ((ρ g : Fˣ) : F) *
          (A : Matrix (Fin 2) (Fin 2) F) 1 1) := by
  let r := upperRatio S hS
  refine ⟨cuspTranslationLattice S, r.range, cuspTranslationInclusion S,
    r.rangeRestrict, ?_, ?_, cuspTranslationInclusion_injective S,
    r.rangeRestrict_surjective, ?_, cuspTranslationInclusion_formula S,
    upperRatio_formula S hS⟩
  · intro x
    constructor
    · intro hx
      refine ⟨cuspTranslationMatrix x, hx, ?_⟩
      simp [cuspTranslationMatrix]
    · rintro ⟨A, hA, hu, hd, hx⟩
      change cuspTranslation (Multiplicative.ofAdd x) ∈ S
      have hn : A 0 0 ≠ 0 := (diagonal_ne_zero A hu).1
      have he : Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix x) =
          Matrix.ProjGenLinGroup.mk A := by
        rw [Matrix.ProjGenLinGroup.mk_eq_mk_iff]
        refine ⟨Units.mk0 (A 0 0) hn, ?_⟩
        apply Units.ext
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two, hu, hd, hx]
      change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix x) ∈ S
      rw [he]
      exact hA
  · intro u
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨A, hA, hu⟩ := hS g g.property
      refine ⟨A, hA.symm ▸ g.property, hu, ?_⟩
      rw [← hg]
      exact upperRatio_formula S hS g A hA hu
    · rintro ⟨A, hA, hu, hd⟩
      let g : S := ⟨Matrix.ProjGenLinGroup.mk A, hA⟩
      refine ⟨g, ?_⟩
      apply Units.ext
      apply mul_right_cancel₀ (diagonal_ne_zero A hu).2
      exact (upperRatio_formula S hS g A rfl hu).symm.trans hd
  · rw [cuspTranslationInclusion_range S hS]
    ext g
    simp [r]

end DedekindZetaZeroFree.KPCuspParabolicLattices

end

end

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspParabolicLattices

variable (F : Type*) [Field F] [NumberField F]

def FullLattice (M : Submodule (IntegralOrder F) (Plane F)) : Prop :=
  Module.Finite (IntegralOrder F) M ∧ Submodule.span F (M : Set (Plane F)) = ⊤

def LatticeAutomorphisms (M : Submodule (IntegralOrder F) (Plane F)) :
    Subgroup (ProjectiveGroup F) :=
  Subgroup.closure {g | ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
    Matrix.ProjGenLinGroup.mk A = g ∧
      ∀ v : Plane F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M}

def StandardCusp : Projectivization F (Plane F) :=
  Projectivization.mk F ![1, 0] (by simp [Matrix.cons_val_zero])

def CuspSubgroup (Γ : Subgroup (ProjectiveGroup F))
    (q : Projectivization F (Plane F)) (σ : ProjectiveGroup F) :
    Subgroup (ProjectiveGroup F) :=
  (Γ ⊓ MulAction.stabilizer (ProjectiveGroup F) q).map (MulAut.conj σ⁻¹).toMonoidHom

def IntegralUnits : Subgroup Fˣ :=
  (Units.map (algebraMap (IntegralOrder F) F).toMonoidHom).range

end DedekindZetaZeroFree.KPCuspParabolicLattices

end

end
