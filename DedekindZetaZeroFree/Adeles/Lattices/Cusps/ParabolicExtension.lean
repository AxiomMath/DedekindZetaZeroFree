module

public import DedekindZetaZeroFree.Arithmetic.Ideals.FractionalIdealComplexLattice
public import DedekindZetaZeroFree.Arithmetic.Units.IdealCuspRatios
public import DedekindZetaZeroFree.Arithmetic.Ideals.IdealCuspTranslations

@[expose] public section

noncomputable section
open scoped Matrix Pointwise
namespace DedekindZetaZeroFree.KPCuspFiniteArithmetic

theorem rationalUnits_of_pow_mem (F : Type*) [Field F] [NumberField F]
    (u : Fˣ) (n : ℕ) (hn : 0 < n)
    (hu : u ^ n ∈ KPCuspArithmetic.rationalUnits F) :
    u ∈ KPCuspArithmetic.rationalUnits F := by
  change ∃ v : (NumberField.RingOfIntegers F)ˣ,
    Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom v = u ^ n at hu
  obtain ⟨v, hv⟩ := hu
  have hvval : algebraMap (NumberField.RingOfIntegers F) F (v : NumberField.RingOfIntegers F) =
      (u : F) ^ n := by
    exact congrArg Units.val hv
  have hvival : algebraMap (NumberField.RingOfIntegers F) F
      ((v⁻¹ : (NumberField.RingOfIntegers F)ˣ) : NumberField.RingOfIntegers F) =
      ((u⁻¹ : Fˣ) : F) ^ n := by
    have h : Units.map (algebraMap (NumberField.RingOfIntegers F) F).toMonoidHom v⁻¹ =
        (u⁻¹ : Fˣ) ^ n := by rw [map_inv, hv, inv_pow]
    exact congrArg Units.val h
  obtain ⟨x, hx⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
    (hvval ▸ isIntegral_algebraMap)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow hn
    (hvival ▸ isIntegral_algebraMap)
  have hxy : x * y = 1 := by
    apply NumberField.RingOfIntegers.coe_injective
    simp only [map_mul, map_one, hx, hy, Units.mul_inv]
  have hyx : y * x = 1 := by simpa only [mul_comm] using hxy
  refine ⟨⟨x, y, hxy, hyx⟩, ?_⟩
  apply Units.ext
  exact hx

theorem integral_ratio_of_commensurable (F : Type*) [Field F] [NumberField F]
    (E : Subgroup Fˣ) (hE : E.Commensurable (KPCuspArithmetic.rationalUnits F)) :
    E ≤ KPCuspArithmetic.rationalUnits F ∧
      (E.subgroupOf (KPCuspArithmetic.rationalUnits F)).FiniteIndex := by
  constructor
  · intro u hu
    obtain ⟨n, hn, _, hpow⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero
      hE.2.relIndex_ne_zero hu
    exact rationalUnits_of_pow_mem F u n hn hpow.1
  · exact Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hE.1

theorem conjugatedStabilizer_commensurable (F : Type*) [Field F]
    (Γ Δ : Subgroup (KPCuspArithmetic.PGL2 F)) (h : Γ.Commensurable Δ)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F) :
    (KPCuspArithmetic.conjugatedStabilizer F Γ q σ).Commensurable
      (KPCuspArithmetic.conjugatedStabilizer F Δ q σ) := by
  have hq : (Γ ⊓ MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q).Commensurable
      (Δ ⊓ MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q) := by
    simpa only [Subgroup.comap_subtype, Subgroup.subgroupOf_map_subtype] using
      (h.comap (MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q).subtype).map
        (MulAction.stabilizer (KPCuspArithmetic.PGL2 F) q).subtype
  exact hq.map (MulAut.conj σ⁻¹).toMonoidHom

theorem conjugatedStabilizer_upper (F : Type*) [Field F] [NumberField F]
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F)) (q : KPCuspArithmetic.Cusp F)
    (σ : KPCuspArithmetic.PGL2 F) (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∀ g ∈ KPCuspArithmetic.conjugatedStabilizer F Γ q σ,
      KPCuspArithmetic.IsUpperTriangular F g := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hg
  have hfix : (σ⁻¹ * k * σ) • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F := by
    have hkq : k • q = q := hk.2
    rw [mul_smul, mul_smul, hσ, hkq, ← hσ, inv_smul_smul]
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective
    ((MulAut.conj σ⁻¹).toMonoidHom k)
  refine ⟨A, hA, ?_⟩
  have hf : Matrix.ProjGenLinGroup.mk A • KPCuspArithmetic.infinity F =
      KPCuspArithmetic.infinity F := by
    rw [hA]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply, inv_inv]
    change (σ⁻¹ * k * σ) • KPCuspArithmetic.infinity F = KPCuspArithmetic.infinity F
    exact hfix
  unfold KPCuspArithmetic.infinity at hf
  rw [Projectivization.PGL.mk_smul_mk, Projectivization.mk_eq_mk_iff] at hf
  obtain ⟨a, ha⟩ := hf
  have h := congrFun ha 1
  have hz : (a • ![1, 0]) 1 = (0 : F) := by simp
  rw [hz] at h
  change 0 = ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ ![1, 0]) 1 at h
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h.symm

theorem isZLattice_of_commensurable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
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
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :=
  Classical.choose (hS g g.property)
private theorem representative_mk {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :
    Matrix.ProjGenLinGroup.mk (representative S hS g) = g :=
  (Classical.choose_spec (hS g g.property)).1
 theorem representative_upper {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) :
    representative S hS g 1 0 = 0 :=
  (Classical.choose_spec (hS g g.property)).2
 def ratioValue {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S) : F :=
  representative S hS g 0 0 / representative S hS g 1 1
private theorem ratioValue_formula {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : Matrix.ProjGenLinGroup.mk A = g) :
    ratioValue S hS g = A 0 0 / A 1 1 :=
  ratio_eq _ _ ((representative_mk S hS g).trans hA.symm)
 theorem ratioValue_one {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) :
    ratioValue S hS 1 = 1 := by
  rw [ratioValue_formula S hS 1 1 (by simp)]
  simp
 theorem ratioValue_mul {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g h : S) :
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
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) : S →* Fˣ where
  toFun g := Units.mk0 (ratioValue S hS g) (by
    exact div_ne_zero (diagonal_ne_zero _ (representative_upper S hS g)).1
      (diagonal_ne_zero _ (representative_upper S hS g)).2)
  map_one' := by apply Units.ext; exact ratioValue_one S hS
  map_mul' g h := by apply Units.ext; exact ratioValue_mul S hS g h

theorem upperRatio_formula {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) (g : S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) (hA : Matrix.ProjGenLinGroup.mk A = g)
    (hu : A 1 0 = 0) : A 0 0 = (upperRatio S hS g : F) * A 1 1 := by
  change A 0 0 = ratioValue S hS g * A 1 1
  rw [ratioValue_formula S hS g A hA]
  exact (div_mul_cancel₀ _ (diagonal_ne_zero A hu).2).symm

theorem upperRatio_agree {F : Type*} [Field F]
    (S T : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hT : ∀ g ∈ T, KPCuspArithmetic.IsUpperTriangular F g)
    (s : S) (t : T) (hst : (s : KPCuspArithmetic.PGL2 F) = t) :
    upperRatio S hS s = upperRatio T hT t := by
  obtain ⟨A, hA, hu⟩ := hS s s.property
  have hzero : A 1 1 ≠ 0 := by
    intro hz
    exact A.det_ne_zero (by simp [Matrix.det_fin_two, hu, hz])
  apply Units.ext
  apply mul_right_cancel₀ hzero
  rw [← upperRatio_formula S hS s A hA hu,
    ← upperRatio_formula T hT t A (hA.trans hst) hu]

theorem ranges_commensurable_of_agree {G H : Type*} [Group G] [Group H]
    (S T : Subgroup G) (h : S.Commensurable T)
    (f : S →* H) (g : T →* H)
    (hfg : ∀ (s : S) (t : T), (s : G) = t → f s = g t) :
    f.range.Commensurable g.range := by
  have hs : (T.subgroupOf S).Commensurable (⊤ : Subgroup S) := by
    simpa only [Subgroup.comap_subtype, Subgroup.subgroupOf_self] using h.symm.comap S.subtype
  have ht : (S.subgroupOf T).Commensurable (⊤ : Subgroup T) := by
    simpa only [Subgroup.comap_subtype, Subgroup.subgroupOf_self] using h.comap T.subtype
  have heq : (T.subgroupOf S).map f = (S.subgroupOf T).map g := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      let t : T := ⟨s, hs⟩
      exact ⟨t, s.property, (hfg s t rfl).symm⟩
    · rintro ⟨t, ht, rfl⟩
      let s : S := ⟨t, ht⟩
      exact ⟨s, t.property, hfg s t rfl⟩
  have hs' : ((T.subgroupOf S).map f).Commensurable f.range := by
    simpa only [MonoidHom.range_eq_map] using hs.map f
  have ht' : ((S.subgroupOf T).map g).Commensurable g.range := by
    simpa only [MonoidHom.range_eq_map] using ht.map g
  exact hs'.symm.trans (heq ▸ ht')

theorem upperRatio_ranges_commensurable {F : Type*} [Field F]
    (S T : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hT : ∀ g ∈ T, KPCuspArithmetic.IsUpperTriangular F g)
    (h : S.Commensurable T) :
    (upperRatio S hS).range.Commensurable (upperRatio T hT).range :=
  ranges_commensurable_of_agree S T h _ _ (upperRatio_agree S T hS hT)

def cuspTranslationMatrix {F : Type*} [Field F] (x : F) : Matrix.GeneralLinearGroup (Fin 2) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [Matrix.det_fin_two])
 theorem translationMatrix_mul {F : Type*} [Field F] (x y : F) :
    cuspTranslationMatrix (x+y) = cuspTranslationMatrix x * cuspTranslationMatrix y := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

def cuspTranslation {F : Type*} [Field F] : Multiplicative F →* KPCuspArithmetic.PGL2 F where
  toFun x := Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix x.toAdd)
  map_one' := by
    change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix 0) = 1
    have h : cuspTranslationMatrix (0 : F) = 1 := by
      apply Units.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [cuspTranslationMatrix]
    rw [h, map_one]
  map_mul' x y := by
    change Matrix.ProjGenLinGroup.mk (cuspTranslationMatrix (x.toAdd+y.toAdd)) = _
    rw [translationMatrix_mul, map_mul]

theorem cuspTranslation_injective {F : Type*} [Field F] :
    Function.Injective (cuspTranslation (F := F)) := by
  intro x y h
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  have h00 := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) F => A 0 0) hu
  have h01 := congrArg (fun A : Matrix.GeneralLinearGroup (Fin 2) F => A 0 1) hu
  simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  change x.toAdd = y.toAdd
  simpa only [h00, Units.val_one, mul_one] using h01

def cuspTranslationLattice {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) : AddSubgroup F :=
  (S.comap cuspTranslation).toAddSubgroup

theorem cuspTranslationLattice_commensurable {F : Type*} [Field F]
    (S T : Subgroup (KPCuspArithmetic.PGL2 F)) (h : S.Commensurable T) :
    (cuspTranslationLattice S).Commensurable (cuspTranslationLattice T) := by
  have hc := h.comap cuspTranslation
  exact ⟨⟨hc.1.relIndex_ne_zero⟩, ⟨hc.2.relIndex_ne_zero⟩⟩

def cuspTranslationInclusion {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) :
    Multiplicative (cuspTranslationLattice S) →* S where
  toFun x := ⟨cuspTranslation (Multiplicative.ofAdd (x.toAdd : F)), x.toAdd.property⟩
  map_one' := by apply Subtype.ext; exact map_one cuspTranslation
  map_mul' x y := by apply Subtype.ext; exact map_mul cuspTranslation _ _
theorem cuspTranslationInclusion_injective {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) :
    Function.Injective (cuspTranslationInclusion S) := by
  intro x y h
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact cuspTranslation_injective (congrArg Subtype.val h)

theorem cuspTranslationInclusion_formula {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F)) (x : cuspTranslationLattice S)
    (A : Matrix.GeneralLinearGroup (Fin 2) F)
    (h : Matrix.ProjGenLinGroup.mk A = cuspTranslationInclusion S (Multiplicative.ofAdd x)) :
    A 1 0 = 0 ∧ A 0 0 = A 1 1 ∧ A 0 1 = (x : F) * A 0 0 := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h.symm
  change cuspTranslationMatrix (x : F) * Matrix.GeneralLinearGroup.scalar (Fin 2) u = A at hu
  rw [← hu]
  simp [cuspTranslationMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]
private theorem ratio_one_translation {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
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

theorem cuspTranslationInclusion_range {F : Type*} [Field F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g) :
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

def extensionDataOfRatio {F : Type*} [Field F] [NumberField F]
    (S : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hE : (upperRatio S hS).range.Commensurable (KPCuspArithmetic.rationalUnits F)) :
    KPCuspChart.ExtensionData F S where
  L := cuspTranslationLattice S
  E := (upperRatio S hS).range
  inclusion := cuspTranslationInclusion S
  ratio := (upperRatio S hS).rangeRestrict
  integralUnits := (integral_ratio_of_commensurable F _ hE).1
  unitIndex := (integral_ratio_of_commensurable F _ hE).2
  injective := cuspTranslationInclusion_injective S
  surjective := (upperRatio S hS).rangeRestrict_surjective
  exact := by
    rw [cuspTranslationInclusion_range S hS]
    ext g
    simp
  upper := hS
  unipotentFormula := cuspTranslationInclusion_formula S
  ratioFormula := upperRatio_formula S hS

theorem extension_lattice_of_parabolic_commensurable
    {F : Type*} [Field F] [NumberField F]
    (S T : Subgroup (KPCuspArithmetic.PGL2 F))
    (hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g)
    (hT : ∀ g ∈ T, KPCuspArithmetic.IsUpperTriangular F g)
    (h : S.Commensurable T)
    (hE : (upperRatio T hT).range.Commensurable (KPCuspArithmetic.rationalUnits F))
    (hdisc : DiscreteTopology (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule)
    (hz : letI := hdisc; IsZLattice ℝ
      (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule) :
    ∃ D : KPCuspChart.ExtensionData F S,
      ∃ hd : DiscreteTopology (KPCuspChart.translationLattice F D.L).toIntSubmodule,
        letI := hd; IsZLattice ℝ (KPCuspChart.translationLattice F D.L).toIntSubmodule := by
  have he := (upperRatio_ranges_commensurable S T hS hT h).trans hE
  refine ⟨extensionDataOfRatio S hS he, ?_⟩
  letI := hdisc
  letI := hz
  have hc := cuspTranslationLattice_commensurable S T h
  exact isZLattice_of_commensurable
    (KPCuspChart.translationLattice F (cuspTranslationLattice S))
    (KPCuspChart.translationLattice F (cuspTranslationLattice T))
    ⟨hc.1.map (KPCuspChart.embedding F), hc.2.map (KPCuspChart.embedding F)⟩

def idealArithmeticModule (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    Submodule (NumberField.RingOfIntegers F) (Fin 2 → F) :=
  ((1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) : Submodule _ F).comap (LinearMap.proj 0) ⊓
  (I : Submodule _ F).comap (LinearMap.proj 1)
private theorem idealArithmeticModule_mem (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) (v : Fin 2 → F) :
    v ∈ idealArithmeticModule F I ↔ (∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = v 0) ∧ v 1 ∈ I := by
  simp [idealArithmeticModule, FractionalIdeal.mem_one_iff]
 def pairVec (F : Type*) [Field F] [NumberField F] :
    (F × F) ≃ₗ[NumberField.RingOfIntegers F] (Fin 2 → F) where
  toFun x := ![x.1,x.2]
  invFun x := (x 0,x 1)
  left_inv x := rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl
theorem idealArithmeticModule_full (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) (hI : I ≠ 0) :
    KPCuspArithmetic.IsRankTwoLattice F (idealArithmeticModule F I) := by
  have hfg : (idealArithmeticModule F I).FG := by
    have hmap : idealArithmeticModule F I = (coordinateLattice (NumberField.RingOfIntegers F) F 1 I).map (pairVec F).toLinearMap := by
      ext v
      constructor
      · intro hv
        exact ⟨(v 0, v 1), hv, by ext i; fin_cases i <;> rfl⟩
      · rintro ⟨v, hv, rfl⟩; exact hv
    rw [hmap]
    exact ((FractionalIdeal.fg_of_isNoetherianRing le_rfl (1 : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)).prod
      (FractionalIdeal.fg_of_isNoetherianRing le_rfl I)).map _
  refine ⟨Module.Finite.of_fg hfg, ?_⟩
  obtain ⟨b, hb, hb0⟩ := (I : Submodule (NumberField.RingOfIntegers F) F).ne_bot_iff.mp
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  apply top_unique
  intro x _
  have h1 : ![1,0] ∈ idealArithmeticModule F I := by simp [idealArithmeticModule]
  have h2 : ![0,b] ∈ idealArithmeticModule F I := by simp [idealArithmeticModule, hb]
  have hh := (Submodule.span F (idealArithmeticModule F I : Set (Fin 2 → F))).add_mem
    (Submodule.smul_mem _ (x 0) (Submodule.subset_span h1))
    (Submodule.smul_mem _ (x 1 / b) (Submodule.subset_span h2))
  convert hh using 1
  ext i
  fin_cases i <;> simp [div_mul_cancel₀, hb0]
private theorem ideal_stabilizer_iff (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (A : Matrix.GeneralLinearGroup (Fin 2) F) :
    A ∈ MulAction.stabilizer (KPFiniteAdelicLatticeStabilizers.RationalGL F) (KPFiniteAdelicLatticeStabilizers.idealVectors F I) ↔
    ∀ v : Fin 2 → F, v ∈ idealArithmeticModule F I ↔ (A : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ idealArithmeticModule F I := by
  rw [MulAction.mem_stabilizer_iff, Set.ext_iff]
  simp only [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro h v
    let V : Matrix (Fin 2) (Fin 1) F := fun i _ => v i
    have hh := h (A • V)
    simp only [inv_smul_smul] at hh
    change (∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = v 0) ∧ v 1 ∈ I ↔ _ at hh
    rw [idealArithmeticModule_mem, idealArithmeticModule_mem]
    change ((∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = v 0) ∧ v 1 ∈ I ↔
      (∃ r : NumberField.RingOfIntegers F, algebraMap _ F r = ((A : Matrix (Fin 2) (Fin 2) F) * V) 0 0) ∧
        ((A : Matrix (Fin 2) (Fin 2) F) * V) 1 0 ∈ I) at hh
    have he : ∀ i : Fin 2, ((A : Matrix (Fin 2) (Fin 2) F) * V) i 0 =
        ((A : Matrix (Fin 2) (Fin 2) F) *ᵥ v) i := by
      intro i
      change (∑ j : Fin 2, A i j * V j 0) = ∑ j : Fin 2, A i j * v j
      rfl
    rw [he 0, he 1] at hh
    exact hh
  · intro h V
    have hh := (h (fun i => (A⁻¹ • V) i 0)).symm
    rw [idealArithmeticModule_mem, idealArithmeticModule_mem] at hh
    have he : (A : Matrix (Fin 2) (Fin 2) F) *ᵥ (fun i => (A⁻¹ • V) i 0) = fun i => V i 0 := by
      have hx := congrArg (fun M : Matrix (Fin 2) (Fin 1) F => fun i => M i 0) (smul_inv_smul A V)
      ext i
      simpa [Matrix.GeneralLinearGroup.smul_def, Matrix.mul_apply, Matrix.mulVec, dotProduct] using congrFun hx i
    rw [he] at hh
    exact hh.symm
theorem idealProjectiveAut_eq_arithmeticAutomorphisms (F : Type*) [Field F] [NumberField F]
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F) :
    KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I = KPCuspArithmetic.projectiveAutomorphisms F (idealArithmeticModule F I) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
    apply Subgroup.subset_closure
    exact ⟨A, rfl, (ideal_stabilizer_iff F I A).mp hA⟩
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨A, hA, hp⟩
    exact ⟨A, (ideal_stabilizer_iff F I A).mpr hp, hA⟩

theorem extension_lattice_of_ideal_commensurable
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers F)) F)
    (hI : I ≠ 0) (a : KPFiniteAdelicLatticeStabilizers.RationalPG F)
    (Γ : Subgroup (KPCuspArithmetic.PGL2 F))
    (hcomm : Γ.Commensurable
      ((KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map (MulAut.conj a).toMonoidHom))
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ D : KPCuspChart.ExtensionData F
      (KPCuspArithmetic.conjugatedStabilizer F Γ q σ),
      ∃ hdisc : DiscreteTopology (KPCuspChart.translationLattice F D.L).toIntSubmodule,
        letI := hdisc
        IsZLattice ℝ (KPCuspChart.translationLattice F D.L).toIntSubmodule := by
  let Δ := (KPFiniteAdelicLatticeStabilizers.idealProjectiveAut F I).map
    (MulAut.conj a).toMonoidHom
  let S := KPCuspArithmetic.conjugatedStabilizer F Γ q σ
  let T := KPCuspArithmetic.conjugatedStabilizer F Δ q σ
  have hS : ∀ g ∈ S, KPCuspArithmetic.IsUpperTriangular F g :=
    conjugatedStabilizer_upper F Γ q σ hσ
  have hT : ∀ g ∈ T, KPCuspArithmetic.IsUpperTriangular F g :=
    conjugatedStabilizer_upper F Δ q σ hσ
  have hST : S.Commensurable T :=
    conjugatedStabilizer_commensurable F Γ Δ hcomm q σ
  have hE : (upperRatio T hT).range.Commensurable (KPCuspArithmetic.rationalUnits F) :=
    FiniteAdelicParabolicExtension.ideal_cusp_ratio_commensurable
      F I hI a q σ hσ (upperRatio T hT) (upperRatio_formula T hT)
  obtain ⟨J, hJ, htranslation⟩ :=
    FiniteAdelicParabolicExtension.ideal_cusp_translation_fractionalIdeal
      F I hI a q σ hσ
  have hL : cuspTranslationLattice T =
      (J : Submodule (NumberField.RingOfIntegers F) F).toAddSubgroup := by
    ext x
    exact htranslation x
  obtain ⟨hd, hz⟩ :=
    FiniteAdelicParabolicExtension.fractionalIdeal_complexPlace_lattice F hF J hJ
  have hlattice : ∃ hd' : DiscreteTopology
      (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule,
      letI := hd'; IsZLattice ℝ
        (KPCuspChart.translationLattice F (cuspTranslationLattice T)).toIntSubmodule := by
    rw [hL]
    exact ⟨hd, hz⟩
  obtain ⟨hd', hz'⟩ := hlattice
  exact extension_lattice_of_parabolic_commensurable S T hS hT hST hE hd' hz'

theorem finite_adelic_parabolic_extension_lattice
    (F : Type*) [Field F] [NumberField F]
    (hF : NumberField.InfinitePlace.nrRealPlaces F = 0)
    (U : Subgroup (KPFiniteAdelicLatticeStabilizers.AdelicPG F))
    (hcompact : letI := KPFiniteAdelicLatticeStabilizers.projectiveTopology F;
      IsCompact (U : Set (KPFiniteAdelicLatticeStabilizers.AdelicPG F)))
    (hopen : letI := KPFiniteAdelicLatticeStabilizers.projectiveTopology F;
      IsOpen (U : Set (KPFiniteAdelicLatticeStabilizers.AdelicPG F)))
    (g : KPFiniteAdelicLatticeStabilizers.AdelicPG F)
    (q : KPCuspArithmetic.Cusp F) (σ : KPCuspArithmetic.PGL2 F)
    (hσ : σ • KPCuspArithmetic.infinity F = q) :
    ∃ D : KPCuspChart.ExtensionData F
      (KPCuspArithmetic.conjugatedStabilizer F
        (KPFiniteAdelicLatticeStabilizers.levelStabilizer F U g) q σ),
      ∃ hdisc : DiscreteTopology (KPCuspChart.translationLattice F D.L).toIntSubmodule,
        letI := hdisc
        IsZLattice ℝ (KPCuspChart.translationLattice F D.L).toIntSubmodule := by
  obtain ⟨I, a, hI, hstandard⟩ :=
    KPFiniteAdelicLatticeStabilizers.standard_stabilizer_class_obstruction F g
  obtain ⟨hlevel, _⟩ :=
    KPFiniteAdelicLatticeStabilizers.level_stabilizers_commensurable_standard F U hcompact hopen g
  exact extension_lattice_of_ideal_commensurable F hF I hI a
    (KPFiniteAdelicLatticeStabilizers.levelStabilizer F U g) (hlevel.trans hstandard) q σ hσ

end DedekindZetaZeroFree.KPCuspFiniteArithmetic

end
