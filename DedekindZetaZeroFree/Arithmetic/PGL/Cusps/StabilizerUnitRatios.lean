module

public import DedekindZetaZeroFree.Arithmetic.PGL.Cusps.ParabolicStabilizers
public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.LineAdaptedIdealDecomposition
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Localization.Finiteness

@[expose] public section

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

 def preservingMatrices {F : Type*} [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 2) F) where
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

private theorem genuine_representative {F : Type*} [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (g : ProjectiveGroup F)
    (hg : g ∈ LatticeAutomorphisms F M) :
    ∃ C : Matrix.GeneralLinearGroup (Fin 2) F,
      Matrix.ProjGenLinGroup.mk C = g ∧
      ∀ v, v ∈ M ↔ (C : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M := by
  have he : {g : ProjectiveGroup F | ∃ A : Matrix.GeneralLinearGroup (Fin 2) F,
      Matrix.ProjGenLinGroup.mk A = g ∧ ∀ v, v ∈ M ↔
        (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M} =
      ((preservingMatrices M).map Matrix.ProjGenLinGroup.mk : Set (ProjectiveGroup F)) := by
    ext g
    simp only [Set.mem_setOf_eq, Subgroup.mem_map]
    constructor
    · rintro ⟨A, rfl, hA⟩; exact ⟨A, hA, rfl⟩
    · rintro ⟨A, hA, rfl⟩; exact ⟨A, rfl, hA⟩
  unfold LatticeAutomorphisms at hg
  rw [he, Subgroup.closure_eq, Subgroup.mem_map] at hg
  obtain ⟨C, hC, rfl⟩ := hg
  exact ⟨C, rfl, hC⟩

theorem conjugated_ratio_has_lattice_representative
    (F : Type*) [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (σ : ProjectiveGroup F) (u : Fˣ)
    (hu : RatioParameter
      ((LatticeAutomorphisms F M).map (MulAut.conj σ⁻¹).toMonoidHom) u) :
    ∃ (N : Submodule (IntegralOrder F) (Plane F))
      (A : Matrix.GeneralLinearGroup (Fin 2) F),
      FullLattice F N ∧ A 1 0 = 0 ∧
      (∀ v : Plane F, v ∈ N ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ N) ∧
      A 0 0 = (u : F) * A 1 1 := by
  obtain ⟨A, hA, h10, hd⟩ := hu
  obtain ⟨g, hg, he⟩ := Subgroup.mem_map.mp hA
  obtain ⟨C, hC, hCM⟩ := genuine_representative M g hg
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  let D := B⁻¹ * C * B
  let f : Plane F →ₗ[F] Plane F := Matrix.mulVecLin (↑B⁻¹ : Matrix (Fin 2) (Fin 2) F)
  let N := M.map (f.restrictScalars (IntegralOrder F))
  have hinv (v : Plane F) :
      (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hinv' (v : Plane F) :
      (↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  have hN (v : Plane F) : v ∈ N ↔ (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M := by
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((↑B⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ w) ∈ M
      rwa [hinv]
    · intro hv
      refine ⟨(↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v, hv, ?_⟩
      exact hinv' v
  have hNfull : FullLattice F N := by
    refine ⟨?_, ?_⟩
    · letI := hM.1
      exact Module.Finite.map M (f.restrictScalars (IntegralOrder F))
    · have hset : (N : Set (Plane F)) = f '' (M : Set (Plane F)) := rfl
      rw [hset, Submodule.span_image, hM.2, Submodule.map_top]
      apply LinearMap.range_eq_top.mpr
      intro v
      exact ⟨(↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v, hinv' v⟩
  have hp : Matrix.ProjGenLinGroup.mk D = Matrix.ProjGenLinGroup.mk A := by
    simp only [D, map_mul, map_inv]
    rw [hB, hC]
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using he
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have entries (i j : Fin 2) : A i j = D i j * (z : F) := by
    rw [← hz]
    simp [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.scalar, Matrix.diagonal_apply]
  refine ⟨N, D, hNfull, ?_, ?_, ?_⟩
  · apply (mul_eq_zero.mp (by simpa only [entries] using h10)).resolve_right (Units.ne_zero z)
  · intro v
    rw [hN, hN]
    have hv : (↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ
        ((↑D : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        (↑C : Matrix (Fin 2) (Fin 2) F) *ᵥ ((↑B : Matrix (Fin 2) (Fin 2) F) *ᵥ v) := by
      simp only [D, Units.val_mul, ← Matrix.mulVec_mulVec, hinv]
    rw [hv]
    exact hCM _
  · apply mul_right_cancel₀ (Units.ne_zero z)
    simpa only [entries, mul_assoc] using hd

end DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

end

end

section

noncomputable section
open scoped Classical Matrix MatrixGroups

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

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

private theorem upperRatio_agree {F : Type*} [Field F]
    (S T : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (hT : ∀ g ∈ T, Upper g)
    (s : S) (t : T) (hst : (s : ProjectiveGroup F) = t) :
    upperRatio S hS s = upperRatio T hT t := by
  obtain ⟨A, hA, hu⟩ := hS s s.property
  have hzero : A 1 1 ≠ 0 := (diagonal_ne_zero A hu).2
  apply Units.ext
  apply mul_right_cancel₀ hzero
  rw [← upperRatio_formula S hS s A hA hu,
    ← upperRatio_formula T hT t A (hA.trans hst) hu]

private theorem mem_range_iff {F : Type*} [Field F]
    (S : Subgroup (ProjectiveGroup F))
    (hS : ∀ g ∈ S, Upper g) (u : Fˣ) :
    u ∈ (upperRatio S hS).range ↔ RatioParameter S u := by
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨representative S hS g,
      by rw [representative_mk]; exact g.property,
      representative_upper S hS g,
      upperRatio_formula S hS g _ (representative_mk S hS g) (representative_upper S hS g)⟩
  · rintro ⟨A, hA, hupper, hratio⟩
    refine ⟨⟨Matrix.ProjGenLinGroup.mk A, hA⟩, ?_⟩
    apply Units.ext
    have hzero : A 1 1 ≠ 0 := (diagonal_ne_zero A hupper).2
    have hf := upperRatio_formula S hS ⟨Matrix.ProjGenLinGroup.mk A, hA⟩ A rfl hupper
    apply mul_right_cancel₀ hzero
    rw [← hf, hratio]

theorem ratio_image_finite_relIndex
    {F : Type*} [Field F]
    (S T : Subgroup (ProjectiveGroup F)) (hST : S ≤ T)
    (hindex : S.IsFiniteRelIndex T) (hT : ∀ g ∈ T, Upper g)
    (E U : Subgroup Fˣ)
    (hE : ∀ u : Fˣ, u ∈ E ↔ RatioParameter S u)
    (hU : ∀ u : Fˣ, u ∈ U → RatioParameter T u) :
    E.IsFiniteRelIndex U := by
  have hS : ∀ g ∈ S, Upper g := fun g hg => hT g (hST hg)
  have hEeq : E = (upperRatio S hS).range := by
    ext u
    rw [hE u, mem_range_iff]
  have hUle : U ≤ (upperRatio T hT).range :=
    fun u hu => (mem_range_iff T hT u).mpr (hU u hu)
  haveI : (S.subgroupOf T).FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hindex
  have hSTi : (S.subgroupOf T).IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_of_finiteIndex
  have hmap := Subgroup.IsFiniteRelIndex.map (upperRatio T hT) hSTi
  have hmaprange : (S.subgroupOf T).map (upperRatio T hT) = (upperRatio S hS).range := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨(t : ProjectiveGroup F), ht⟩, upperRatio_agree S T hS hT _ t rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨⟨(s : ProjectiveGroup F), hST s.property⟩, s.property,
        (upperRatio_agree S T hS hT s _ rfl).symm⟩
  have hmap' : (upperRatio S hS).range.IsFiniteRelIndex (upperRatio T hT).range := by
    rw [← hmaprange, MonoidHom.range_eq_map]
    exact hmap
  have hErange : E.relIndex (upperRatio T hT).range ≠ 0 := by
    rw [hEeq]
    exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mp hmap'
  have hne := Subgroup.relIndex_inter_ne_zero hErange U
  rw [inf_eq_right.mpr hUle, inf_comm, Subgroup.inf_relIndex_left] at hne
  exact Subgroup.isFiniteRelIndex_iff_relIndex_ne_zero.mpr hne

end DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

end

end

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

private theorem plane_splitting
    {F : Type*} [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (v : Plane F) (hv : v ≠ 0) :
    ∃ (I J : FractionalIdeal (nonZeroDivisors (IntegralOrder F)) F) (w : Plane F),
      v 0 * w 1 - v 1 * w 0 ≠ 0 ∧
      ∀ x : Plane F, x ∈ M ↔ ∃ s ∈ I, ∃ t ∈ J, x = s • v + t • w := by
  let e := LinearEquiv.finTwoArrow F F
  let N := M.map (e.toLinearMap.restrictScalars (IntegralOrder F))
  have hfg : N.FG := (Module.Finite.iff_fg.mp hM.1).map _
  have hspan : Submodule.span F (N : Set (F × F)) = ⊤ := by
    have hc : (N : Set (F × F)) = e '' (M : Set (Plane F)) := by
      ext x
      simp only [N, Submodule.mem_map, Set.mem_image]
      rfl
    rw [hc]
    change Submodule.span F (e.toLinearMap '' (M : Set (Plane F))) = ⊤
    rw [← Submodule.map_span, hM.2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr e.surjective
  let L : DedekindZetaZeroFree.FullLattice (IntegralOrder F) F := ⟨N, ⟨hfg, hspan⟩⟩
  obtain ⟨I, J, w, _, _, _, hd, hm, _⟩ :=
    kp_cusp_line_adapted_ideal_splitting (IntegralOrder F) F L (e v)
      (fun hz => hv (e.injective (hz.trans (e.map_zero).symm)))
  refine ⟨I, J, e.symm w, ?_, ?_⟩
  · simpa [det₂, e, LinearEquiv.finTwoArrow, finTwoArrowEquiv] using hd
  · intro x
    have hmem : e x ∈ N ↔ x ∈ M := by
      simp only [N, Submodule.mem_map]
      exact ⟨fun ⟨y, hy, he⟩ => e.injective he ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
    rw [← hmem, hm]
    constructor
    · rintro ⟨s, hs, t, ht, hx⟩
      refine ⟨s, hs, t, ht, ?_⟩
      apply e.injective
      simpa only [map_add, map_smul, e.apply_symm_apply] using hx
    · rintro ⟨s, hs, t, ht, rfl⟩
      exact ⟨s, hs, t, ht, by simp⟩

theorem integral_unit_is_full_cusp_ratio
    (F : Type*) [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (q : Projectivization F (Plane F))
    (σ : ProjectiveGroup F) (hσ : σ • StandardCusp F = q)
    (u : Fˣ) (hu : u ∈ IntegralUnits F) :
    RatioParameter (CuspSubgroup F (LatticeAutomorphisms F M) q σ) u := by
  obtain ⟨r, hr⟩ := hu
  have hur : algebraMap (IntegralOrder F) F (r : IntegralOrder F) = (u : F) :=
    congrArg Units.val hr
  obtain ⟨B, hB⟩ := Matrix.ProjGenLinGroup.mk_surjective σ
  let e₀ : Plane F := ![1, 0]
  let e₁ : Plane F := ![0, 1]
  have he₀ : e₀ ≠ 0 := by simp [e₀, Matrix.cons_val_zero]
  let v : Plane F := B • e₀
  obtain ⟨I, J, w, hd, hm⟩ := plane_splitting M hM v
    ((smul_ne_zero_iff_ne B).mpr he₀)
  let T : Matrix.GeneralLinearGroup (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![v 0, w 0; v 1, w 1]
      (by simpa [Matrix.det_fin_two, mul_comm] using hd)
  let D : Matrix.GeneralLinearGroup (Fin 2) F :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(u : F), 0; 0, 1]
      (by simpa [Matrix.det_fin_two] using Units.ne_zero u)
  let A := T * D * T⁻¹
  have ht₀ : T • e₀ = v := by
    change (↑T : Matrix (Fin 2) (Fin 2) F) *ᵥ e₀ = v
    ext i; fin_cases i <;> simp [T, e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have ht₁ : T • e₁ = w := by
    change (↑T : Matrix (Fin 2) (Fin 2) F) *ᵥ e₁ = w
    ext i; fin_cases i <;> simp [T, e₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd₀ : D • e₀ = (u : F) • e₀ := by
    change (↑D : Matrix (Fin 2) (Fin 2) F) *ᵥ e₀ = (u : F) • e₀
    ext i; fin_cases i <;> simp [D, e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hd₁ : D • e₁ = e₁ := by
    change (↑D : Matrix (Fin 2) (Fin 2) F) *ᵥ e₁ = e₁
    ext i; fin_cases i <;> simp [D, e₁, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hav : A • v = (u : F) • v := by
    rw [← ht₀]
    simp only [A, mul_smul, inv_smul_smul, hd₀, smul_comm T (u : F)]
  have haw : A • w = w := by
    rw [← ht₁]
    simp only [A, mul_smul, inv_smul_smul, hd₁]
  have haf (s t : F) : A • (s • v + t • w) = ((u : F) * s) • v + t • w := by
    rw [smul_add, smul_comm A s, smul_comm A t, hav, haw, smul_smul, mul_comm s]
  have hi (s : F) (hs : s ∈ I) : (u : F) * s ∈ I := by
    rw [← hur]
    exact I.val.smul_mem (r : IntegralOrder F) hs
  have hii (s : F) (hs : s ∈ I) : ((u⁻¹ : Fˣ) : F) * s ∈ I := by
    have hur' : algebraMap (IntegralOrder F) F (↑r⁻¹ : IntegralOrder F) = (↑u⁻¹ : F) :=
      congrArg Units.val (show (Units.map (algebraMap (IntegralOrder F) F).toMonoidHom) r⁻¹ = u⁻¹ from
        (map_inv _ r).trans (congrArg Inv.inv hr))
    rw [← hur']
    exact I.val.smul_mem (↑r⁻¹ : IntegralOrder F) hs
  have hpres : ∀ x : Plane F, x ∈ M ↔ A • x ∈ M := by
    intro x
    constructor
    · intro hx
      obtain ⟨s, hs, t, ht, rfl⟩ := (hm x).mp hx
      rw [haf]
      exact (hm _).mpr ⟨_, hi s hs, t, ht, rfl⟩
    · intro hx
      obtain ⟨s, hs, t, ht, he⟩ := (hm _).mp hx
      have hz : ((↑u⁻¹ : F) * s) • v + t • w ∈ M :=
        (hm _).mpr ⟨_, hii s hs, t, ht, rfl⟩
      have he' : A • (((↑u⁻¹ : F) * s) • v + t • w) = A • x := by
        rw [haf, he]
        simp [← mul_assoc]
      exact (MulAction.injective A he') ▸ hz
  have haq : Matrix.ProjGenLinGroup.mk A • q = q := by
    have hq : q = Projectivization.mk F v ((smul_ne_zero_iff_ne B).mpr he₀) := by
      rw [← hσ, ← hB]
      exact Projectivization.PGL.mk_smul_mk B he₀
    rw [hq, Projectivization.PGL.mk_smul_mk]
    apply (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr
    exact ⟨u, hav.symm⟩
  let C := B⁻¹ * A * B
  have hc : C • e₀ = (u : F) • e₀ := by
    simp only [C, mul_smul]
    change B⁻¹ • (A • v) = _
    rw [hav, smul_comm B⁻¹ (u : F)]
    simp [v]
  change (↑C : Matrix (Fin 2) (Fin 2) F) *ᵥ e₀ = (u : F) • e₀ at hc
  have hc10 : C 1 0 = 0 := by
    simpa [e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 1
  have hc00 : C 0 0 = (u : F) := by
    simpa [e₀, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hc 0
  have hdet : (↑C : Matrix (Fin 2) (Fin 2) F).det = (u : F) := by
    have hh : Matrix.GeneralLinearGroup.det C = Matrix.GeneralLinearGroup.det D := by
      simp only [C, A, map_mul, map_inv]
      exact by
        let b := Matrix.GeneralLinearGroup.det B
        let t := Matrix.GeneralLinearGroup.det T
        let d := Matrix.GeneralLinearGroup.det D
        change b⁻¹ * (t * d * t⁻¹) * b = d
        calc
          _ = d * (b⁻¹ * b) * (t * t⁻¹) := by ac_rfl
          _ = d := by rw [inv_mul_cancel, mul_inv_cancel, mul_one, mul_one]
    have hh' := congrArg Units.val hh
    simpa [Matrix.GeneralLinearGroup.det, D, Matrix.det_fin_two] using hh'
  have hc11 : C 1 1 = 1 := by
    have hh : (u : F) * C 1 1 = (u : F) * 1 := by
      simpa [Matrix.det_fin_two, hc10, hc00] using hdet
    exact mul_left_cancel₀ (Units.ne_zero u) hh
  refine ⟨C, ?_, hc10, ?_⟩
  · apply Subgroup.mem_map.mpr
    refine ⟨Matrix.ProjGenLinGroup.mk A, ⟨?_, haq⟩, ?_⟩
    · apply Subgroup.subset_closure
      exact ⟨A, rfl, hpres⟩
    · simp [C, ← hB, MulAut.conj_apply]
  · rw [hc00, hc11, mul_one]

end DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

end

end

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

private theorem upper_of_fixes_standardCusp
    (F : Type*) [Field F] [NumberField F] (g : ProjectiveGroup F)
    (hg : g • StandardCusp F = StandardCusp F) : Upper g := by
  obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  refine ⟨A, rfl, ?_⟩
  have hv : (![1,0] : Plane F) ≠ 0 := by simp [Matrix.cons_val_zero]
  have hg' : (Matrix.ProjGenLinGroup.mk A : ProjectiveGroup F) •
      Projectivization.mk F (![1,0] : Plane F) hv =
      Projectivization.mk F (![1,0] : Plane F) hv := by
    simpa [StandardCusp] using hg
  have h : Projectivization.mk F (A • (![1,0] : Plane F)) (smul_ne_zero_iff_ne A |>.2 hv) =
      Projectivization.mk F (![1,0] : Plane F) hv := by
    rw [← Projectivization.PGL.mk_smul_mk (g := A) hv]
    exact hg'
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ _ _).mp h
  have h1 : (A • (![1,0] : Plane F)) 1 = (A : Matrix (Fin 2) (Fin 2) F) 1 0 := by
    rw [show A • (![1,0] : Plane F) = (A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1,0] from rfl]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have h2 : (a • (![1,0] : Plane F)) 1 = 0 := by
    simp [Matrix.cons_val_one, Matrix.cons_val_zero]
  have := congrFun ha 1
  rw [h1, h2] at this
  exact this.symm

theorem cusp_subgroup_upper
    (F : Type*) [Field F] [NumberField F]
    (Γ : Subgroup (ProjectiveGroup F))
    (q : Projectivization F (Plane F))
    (σ : ProjectiveGroup F) (hσ : σ • StandardCusp F = q) :
    ∀ g ∈ CuspSubgroup F Γ q σ, Upper g := by
  intro g hg
  rw [CuspSubgroup, Subgroup.mem_map] at hg
  obtain ⟨h, hh, rfl⟩ := hg
  have hq : h • q = q := hh.2
  refine upper_of_fixes_standardCusp F _ ?_
  rw [show (MulAut.conj σ⁻¹).toMonoidHom h = σ⁻¹ * h * σ by simp [MulAut.conj_apply]]
  rw [mul_smul, mul_smul, hσ, hq, ← hσ, ← mul_smul, inv_mul_cancel, one_smul]

end DedekindZetaZeroFree.KPCuspParabolicLattices.RatioUnits

end

end

section

noncomputable section
open scoped Classical Matrix MatrixGroups LinearAlgebra.Projectivization nonZeroDivisors

namespace DedekindZetaZeroFree.KPCuspParabolicLattices

theorem scalar_integral_unit
    (F : Type*) [Field F] [NumberField F]
    (u : Fˣ) (N P : Submodule (IntegralOrder F) F)
    (hN : N ≠ ⊥) (hP : P ≠ ⊥) (hNfg : N.FG) (hPfg : P.FG)
    (hu : ∀ x ∈ N, (u : F) * x ∈ N)
    (hui : ∀ x ∈ P, ((u⁻¹ : Fˣ) : F) * x ∈ P) :
    u ∈ IntegralUnits F := by
  have hint : IsIntegral (IntegralOrder F) (u : F) :=
    isIntegral_of_smul_mem_submodule N hN hNfg (u : F) hu
  have hiint : IsIntegral (IntegralOrder F) ((u⁻¹ : Fˣ) : F) :=
    isIntegral_of_smul_mem_submodule P hP hPfg ((u⁻¹ : Fˣ) : F) hui
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hiint
  have hxy : x * y = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [map_mul, map_one, hx, hy, Units.mul_inv]
  have hyx : y * x = 1 := by simpa only [mul_comm] using hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  apply Units.ext
  exact hx

theorem upper_diagonal_integral
    (F : Type*) [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hupper : A 1 0 = 0)
    (hA : ∀ v : Plane F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M) :
    IsIntegral (IntegralOrder F) (A 0 0) ∧
      IsIntegral (IntegralOrder F) (A 1 1) := by
  have hfg : M.FG := Module.Finite.iff_fg.mp hM.1
  letI : Submodule.IsLattice F M := ⟨hfg, hM.2⟩
  let e : F →ₗ[IntegralOrder F] Plane F :=
    (LinearMap.toSpanSingleton F (Plane F) ![1, 0]).restrictScalars _
  have heinj : Function.Injective e := by
    intro x y h
    simpa [e] using congrFun h 0
  let N := M.comap e
  have hNfg : N.FG := by
    apply Submodule.fg_of_fg_map_injective e heinj
    exact Submodule.FG.of_le hfg (Submodule.map_comap_le e M)
  have hN : N ≠ ⊥ := by
    obtain ⟨r, hr, hm⟩ := kp_cusp_full_lattice_clear_denominators
      (IntegralOrder F) F (Plane F) M ![1, 0]
    intro hn
    have hx : algebraMap (IntegralOrder F) F r ∈ N := hm
    rw [hn, Submodule.mem_bot] at hx
    exact hr (NumberField.RingOfIntegers.coe_injective (by simpa using hx))
  let p : Plane F →ₗ[IntegralOrder F] F := LinearMap.proj 1
  let P := M.map p
  have hPfg : P.FG := hfg.map p
  have hP : P ≠ ⊥ := by
    obtain ⟨r, hr, hm⟩ := kp_cusp_full_lattice_clear_denominators
      (IntegralOrder F) F (Plane F) M ![0, 1]
    intro hp
    have hx : algebraMap (IntegralOrder F) F r ∈ P := by
      refine ⟨_, hm, ?_⟩
      change algebraMap (IntegralOrder F) F r * 1 = _
      exact mul_one _
    rw [hp, Submodule.mem_bot] at hx
    exact hr (NumberField.RingOfIntegers.coe_injective (by simpa using hx))
  constructor
  · apply isIntegral_of_smul_mem_submodule N hN hNfg
    intro x hx
    change e (A 0 0 * x) ∈ M
    have hh := (hA (e x)).mp hx
    convert hh using 1
    ext i
    fin_cases i <;>
      simp [e, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hupper]
  · apply isIntegral_of_smul_mem_submodule P hP hPfg
    rintro x ⟨v, hv, rfl⟩
    refine ⟨(A : Matrix (Fin 2) (Fin 2) F) *ᵥ v, (hA v).mp hv, ?_⟩
    simp [p, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hupper]

theorem upper_ratio_integral_unit
    (F : Type*) [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hupper : A 1 0 = 0)
    (hA : ∀ v : Plane F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M)
    (u : Fˣ) (hu : A 0 0 = (u : F) * A 1 1) :
    u ∈ IntegralUnits F := by
  have hn : A 0 0 ≠ 0 ∧ A 1 1 ≠ 0 := by
    constructor <;> intro hz <;>
      exact A.det_ne_zero (by simp [Matrix.det_fin_two, hupper, hz])
  have hmul := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B 1 0)
    (show (A : Matrix (Fin 2) (Fin 2) F) * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) = 1 by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
  have hiupper : (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have hh : A 1 1 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, hupper] using hmul
    exact (mul_eq_zero.mp hh).resolve_left hn.2
  have hiA : ∀ v : Plane F, v ∈ M ↔ (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M := by
    intro v
    have hh := hA ((↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ v)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec] at hh
    exact hh.symm
  obtain ⟨ha, hd⟩ := upper_diagonal_integral F M hM A hupper hA
  obtain ⟨hia, hid⟩ := upper_diagonal_integral F M hM A⁻¹ hiupper hiA
  have hdiag (i : Fin 2) :
      A i i * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) i i = 1 := by
    have hh := congrArg (fun B : Matrix (Fin 2) (Fin 2) F => B i i)
      (show (A : Matrix (Fin 2) (Fin 2) F) * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) = 1 by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one])
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at hh
    fin_cases i
    · change A 0 0 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 0 0 = 1
      change A 0 0 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 0 0 +
        A 0 1 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 0 = 1 at hh
      simpa only [hiupper, mul_zero, add_zero] using hh
    · change A 1 1 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 1 = 1
      change A 1 0 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 0 1 +
        A 1 1 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 at hh
      simpa only [hupper, zero_mul, zero_add] using hh
  have hv : (u : F) = A 0 0 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [hu, mul_assoc, hdiag 1, mul_one]
  have hiv : ((u⁻¹ : Fˣ) : F) = A 1 1 * (↑A⁻¹ : Matrix (Fin 2) (Fin 2) F) 0 0 := by
    apply mul_left_cancel₀ (Units.ne_zero u)
    rw [Units.mul_inv]
    rw [← mul_assoc, ← hu, hdiag 0]
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hv ▸ ha.mul hid)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hiv ▸ hd.mul hia)
  have hxy : x * y = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [map_mul, map_one, hx, hy, Units.mul_inv]
  refine ⟨⟨x, y, hxy, by simpa only [mul_comm] using hxy⟩, ?_⟩
  apply Units.ext
  exact hx

theorem cuspSubgroup_mono
    {F : Type*} [Field F] [NumberField F]
    {Γ Δ : Subgroup (ProjectiveGroup F)} (h : Γ ≤ Δ)
    (q : Projectivization F (Plane F)) (σ : ProjectiveGroup F) :
    CuspSubgroup F Γ q σ ≤ CuspSubgroup F Δ q σ := by
  exact Subgroup.map_mono (inf_le_inf_right _ h)

theorem cuspSubgroup_commensurable
    {F : Type*} [Field F] [NumberField F]
    {Γ Δ : Subgroup (ProjectiveGroup F)} (h : Γ.Commensurable Δ)
    (q : Projectivization F (Plane F)) (σ : ProjectiveGroup F) :
    (CuspSubgroup F Γ q σ).Commensurable (CuspSubgroup F Δ q σ) := by
  let P := MulAction.stabilizer (ProjectiveGroup F) q
  have h1 : (Γ ⊓ P).IsFiniteRelIndex (Δ ⊓ P) := by
    haveI := h.1
    haveI : Γ.IsFiniteRelIndex (Δ ⊓ P) := Subgroup.isFiniteRelIndex_of_le_right Γ inf_le_left
    exact Subgroup.IsFiniteRelIndex.inf inferInstance
      (Subgroup.isFiniteRelIndex_of_le_right (H := P) (K := Δ ⊓ P) (L := P) inf_le_right)
  have h2 : (Δ ⊓ P).IsFiniteRelIndex (Γ ⊓ P) := by
    haveI := h.2
    haveI : Δ.IsFiniteRelIndex (Γ ⊓ P) := Subgroup.isFiniteRelIndex_of_le_right Δ inf_le_left
    exact Subgroup.IsFiniteRelIndex.inf inferInstance
      (Subgroup.isFiniteRelIndex_of_le_right (H := P) (K := Γ ⊓ P) (L := P) inf_le_right)
  exact (show (Γ ⊓ P).Commensurable (Δ ⊓ P) from ⟨h1,h2⟩).map _

theorem mem_integralUnits_iff
    {F : Type*} [Field F] [NumberField F] (u : Fˣ) :
    u ∈ IntegralUnits F ↔ IsIntegral ℤ (u : F) ∧ IsIntegral ℤ (↑u⁻¹ : F) := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨(v : IntegralOrder F).property, (↑v⁻¹ : IntegralOrder F).property⟩
  · rintro ⟨hu, hi⟩
    let v : (IntegralOrder F)ˣ :=
      { val := ⟨(u : F), hu⟩
        inv := ⟨(↑u⁻¹ : F), hi⟩
        val_inv := by apply NumberField.RingOfIntegers.ext; change (u : F) * (↑u⁻¹ : F) = 1; simp
        inv_val := by apply NumberField.RingOfIntegers.ext; change (↑u⁻¹ : F) * (u : F) = 1; simp }
    exact ⟨v, by ext; rfl⟩

theorem eigenvalue_integral_of_fullLattice
    {F : Type*} [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (f : Module.End F (Plane F)) (hf : ∀ v ∈ M, f v ∈ M)
    (μ : F) (hμ : f.HasEigenvalue μ) : IsIntegral ℤ μ := by
  haveI : Module.Finite (IntegralOrder F) M := hM.1
  let N := M ⊓ (f.eigenspace μ).restrictScalars (IntegralOrder F)
  have hNfg : N.FG := Submodule.FG.of_le (Module.Finite.iff_fg.mp inferInstance) inf_le_left
  have hN : N ≠ ⊥ := by
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span
      (nonZeroDivisors (IntegralOrder F)) F (M : Set (Plane F)) v
      (by rw [hM.2]; trivial)
    rw [Submodule.span_eq] at ht
    intro hn
    have hvN : t • v ∈ N := by
      refine ⟨ht, ?_⟩
      exact (f.eigenspace μ).smul_mem (algebraMap (IntegralOrder F) F t) hv.1
    rw [hn] at hvN
    have hz : t • v = 0 := hvN
    have ht0 : (t : IntegralOrder F) ≠ 0 := nonZeroDivisors.ne_zero t.property
    have htF : algebraMap (IntegralOrder F) F t ≠ 0 := by
      intro htF
      exact ht0 ((IsFractionRing.injective (IntegralOrder F) F) (by simpa using htF))
    exact (smul_ne_zero htF hv.2) hz
  apply isIntegral_trans (A := IntegralOrder F)
  apply isIntegral_of_smul_mem_submodule N hN hNfg μ
  intro v hv
  have he : f v = μ • v := Module.End.mem_eigenspace_iff.mp hv.2
  exact ⟨he ▸ hf v hv.1, (f.eigenspace μ).smul_mem μ hv.2⟩

theorem eigen_unit_integral_of_fullLattice
    {F : Type*} [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (f : Plane F ≃ₗ[F] Plane F) (hf : ∀ v, v ∈ M ↔ f v ∈ M)
    (u : Fˣ) (hu : Module.End.HasEigenvalue f.toLinearMap (u : F)) :
    u ∈ IntegralUnits F := by
  apply (mem_integralUnits_iff u).mpr
  refine ⟨eigenvalue_integral_of_fullLattice M hM f.toLinearMap
    (fun v hv => (hf v).mp hv) u hu, ?_⟩
  apply eigenvalue_integral_of_fullLattice M hM f.symm.toLinearMap
    (fun v hv => (hf (f.symm v)).mpr (by simpa using hv)) (↑u⁻¹ : F)
  obtain ⟨v, hv⟩ := hu.exists_hasEigenvector
  apply Module.End.hasEigenvalue_of_hasEigenvector
  refine ⟨?_, hv.2⟩
  apply Module.End.mem_eigenspace_iff.mpr
  apply f.injective
  change f (f.symm v) = f ((↑u⁻¹ : F) • v)
  have he : f v = (u : F) • v := Module.End.mem_eigenspace_iff.mp hv.1
  rw [f.apply_symm_apply, map_smul, he, smul_smul]
  simp

end DedekindZetaZeroFree.KPCuspParabolicLattices

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.CuspRatios
variable {F : Type*} [Field F] [NumberField F]
 def matrixAut (M : Submodule (IntegralOrder F) (Plane F)) : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F) where
  carrier := {A | ∀ v : Plane F, v ∈ M ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ M}
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

end DedekindZetaZeroFree.KPCuspParabolicLattices.CuspRatios
namespace DedekindZetaZeroFree.KPCuspParabolicLattices.CuspRatios
variable {F : Type*} [Field F] [NumberField F]

end DedekindZetaZeroFree.KPCuspParabolicLattices.CuspRatios

namespace DedekindZetaZeroFree.KPCuspParabolicLattices.CuspRatios
variable {F : Type*} [Field F]

end DedekindZetaZeroFree.KPCuspParabolicLattices.CuspRatios

namespace DedekindZetaZeroFree.KPCuspParabolicLattices

theorem ratio_integral_units
    (F : Type*) [Field F] [NumberField F]
    (M : Submodule (IntegralOrder F) (Plane F)) (hM : FullLattice F M)
    (Γ : Subgroup (ProjectiveGroup F))
    (hΓ : Γ ≤ LatticeAutomorphisms F M)
    (hcomm : Γ.Commensurable (LatticeAutomorphisms F M))
    (q : Projectivization F (Plane F))
    (σ : ProjectiveGroup F) (hσ : σ • StandardCusp F = q)
    (E : Subgroup Fˣ)
    (hE : ∀ u : Fˣ, u ∈ E ↔ RatioParameter (CuspSubgroup F Γ q σ) u) :
    E ≤ IntegralUnits F ∧ (E.subgroupOf (IntegralUnits F)).FiniteIndex := by
  have hfull : CuspSubgroup F Γ q σ ≤
      (LatticeAutomorphisms F M).map (MulAut.conj σ⁻¹).toMonoidHom :=
    Subgroup.map_mono (le_trans inf_le_left hΓ)
  have hle : E ≤ IntegralUnits F := by
    intro u hu
    obtain ⟨A, hA, hupper, hratio⟩ := (hE u).mp hu
    obtain ⟨N, B, hN, hBupper, hB, hBratio⟩ :=
      RatioUnits.conjugated_ratio_has_lattice_representative F M hM σ u
        ⟨A, hfull hA, hupper, hratio⟩
    exact upper_ratio_integral_unit F N hN B hBupper hB u hBratio
  have hindex : E.IsFiniteRelIndex (IntegralUnits F) :=
    RatioUnits.ratio_image_finite_relIndex
      (CuspSubgroup F Γ q σ)
      (CuspSubgroup F (LatticeAutomorphisms F M) q σ)
      (cuspSubgroup_mono hΓ q σ)
      (cuspSubgroup_commensurable hcomm q σ).1
      (RatioUnits.cusp_subgroup_upper F (LatticeAutomorphisms F M) q σ hσ)
      E (IntegralUnits F) hE
      (RatioUnits.integral_unit_is_full_cusp_ratio F M hM q σ hσ)
  letI := hindex
  exact ⟨hle, inferInstance⟩

end DedekindZetaZeroFree.KPCuspParabolicLattices

end

end
