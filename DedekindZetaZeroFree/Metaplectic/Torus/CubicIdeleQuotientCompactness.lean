module

public import Mathlib
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.IdentityComponent
public import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison

@[expose] public section

namespace DedekindZetaZeroFree.KPCubicIdele

noncomputable section
open scoped NumberField NNReal IsMulCommutative

abbrev Ideles (F : Type) [Field F] [NumberField F] :=
  NumberField.IdeleGroup (𝓞 F) F

def cubes (F : Type) [Field F] [NumberField F] : Subgroup (Ideles F) :=
  (powMonoidHom (α := Ideles F) 3).range

def rationalCubes (F : Type) [Field F] [NumberField F] : Subgroup (Ideles F) :=
  NumberField.IdeleGroup.principalSubgroup (𝓞 F) F ⊔ cubes F

abbrev CubicClasses (F : Type) [Field F] [NumberField F] :=
  Ideles F ⧸ rationalCubes F

theorem mem_rationalCubes_iff (F : Type) [Field F] [NumberField F]
    (x : Ideles F) :
    x ∈ rationalCubes F ↔ ∃ (r : Fˣ) (a : Ideles F),
      x = NumberField.IdeleGroup.unitEmbedding (𝓞 F) F r * a ^ 3 := by
  rw [rationalCubes, Subgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨r, rfl⟩ := hy
    obtain ⟨a, rfl⟩ := hz
    exact ⟨r, a, rfl⟩
  · rintro ⟨r, a, rfl⟩
    exact ⟨_, ⟨r, rfl⟩, a ^ 3, ⟨a, rfl⟩, rfl⟩

private theorem positive_cube (r : ℝ≥0ˣ) : ∃ s : ℝ≥0ˣ, s ^ 3 = r := by
  let s := Units.map (NNReal.rpowMonoidHom (3 : ℝ)⁻¹) r
  refine ⟨s, ?_⟩
  apply Units.ext
  exact NNReal.rpow_inv_natCast_pow (r : ℝ≥0) (by norm_num : (3 : ℕ) ≠ 0)

 def classToCubic (F : Type) [Field F] [NumberField F] :
    IdeleClassGroup F →* CubicClasses F :=
  (QuotientGroup.map (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)
    (rationalCubes F) (MonoidHom.id _) le_sup_left).comp
    (IdeleGroup.ideleClassGroupEquivMathlib F).toMonoidHom

private theorem classToCubic_continuous (F : Type) [Field F] [NumberField F] :
    Continuous (classToCubic F) := by
  apply Continuous.comp _ (IdeleGroup.continuous_ideleClassGroupEquivMathlib F)
  exact (QuotientGroup.isQuotientMap_mk
    (NumberField.IdeleGroup.principalSubgroup (𝓞 F) F)).continuous_iff.mpr
    QuotientGroup.continuous_mk

private theorem classToCubic_mk (F : Type) [Field F] [NumberField F]
    (a : IdeleGroup F) :
    classToCubic F (QuotientGroup.mk' (IdeleGroup.principalSubgroup F) a) =
      QuotientGroup.mk' (rationalCubes F) (IdeleGroup.equivAdeleRingUnits a) := rfl

private theorem classToCubic_section (F : Type) [Field F] [NumberField F]
    (r : ℝ≥0ˣ) : classToCubic F (ideleClassPositiveArchimedeanSection F r) = 1 := by
  obtain ⟨s, rfl⟩ := positive_cube r
  rw [map_pow, map_pow]
  change QuotientGroup.mk' (rationalCubes F)
    (IdeleGroup.equivAdeleRingUnits (IdeleGroup.positiveArchimedeanSection F s)) ^ 3 = 1
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact (le_sup_right : cubes F ≤ rationalCubes F) ⟨_, rfl⟩

private theorem cubic_compact (F : Type) [Field F] [NumberField F] :
    CompactSpace (CubicClasses F) := by
  let f : IdeleClassGroup.normOneSubgroup (K := F) → CubicClasses F :=
    fun c => classToCubic F c
  have hc : Continuous f := (classToCubic_continuous F).comp continuous_subtype_val
  have hs : Function.Surjective f := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (rationalCubes F) z
    let a := (IdeleGroup.equivAdeleRingUnits (K := F)).symm x
    refine ⟨ideleClassNormOneCorrection F a, ?_⟩
    have h := congrArg (classToCubic F)
      (ideleClass_mk_eq_normOneCorrection_mul_positiveSection_inv F a)
    rw [map_mul, map_inv, classToCubic_section, inv_one] at h
    change _ = (classToCubic F) (ideleClassNormOneCorrection F a) *
      (1 : CubicClasses F) at h
    rw [mul_one (M := CubicClasses F)] at h
    simpa only [classToCubic_mk, a,
      (IdeleGroup.equivAdeleRingUnits (K := F)).apply_symm_apply] using h.symm
  exact hs.compactSpace hc

private theorem continuous_classNorm (F : Type) [Field F] [NumberField F] :
    Continuous (IdeleClassGroup.absoluteNorm (K := F)) := by
  have hfinite : Continuous (FiniteIdeleGroup.absoluteNorm (K := F)) := by
    apply continuous_of_continuousAt_one
    apply (continuousAt_const (y := (1 : ℝ≥0ˣ))).congr_of_eventuallyEq
    have ho : IsOpen (FiniteIdeleGroup.integralSubgroup (K := F) :
        Set (FiniteIdeleGroup F)) := by
      simpa only [Finset.coe_empty, FiniteIdeleGroup.supportedAt_empty] using
        (FiniteIdeleGroup.isOpen_supportedAt (K := F) ∅)
    filter_upwards [ho.mem_nhds (Subgroup.one_mem _)] with a ha
    exact IdeleGroup.finite_absoluteNorm_eq_one_of_integral a ha
  have hidele : Continuous (IdeleGroup.absoluteNorm (K := F)) :=
    (hfinite.comp continuous_snd).mul
      ((InfiniteIdeleGroup.continuous_archimedeanNorm.comp continuous_fst).inv)
  exact (QuotientGroup.isQuotientMap_mk
    (IdeleGroup.principalSubgroup F)).continuous_iff.mpr hidele

 def normProjection (F : Type) [Field F] [NumberField F] :
    IdeleClassGroup F →* IdeleClassGroup F :=
  MonoidHom.mk'
    (fun c => c * ideleClassPositiveArchimedeanSection F (IdeleClassGroup.absoluteNorm c))
    (fun x y => by
      simp only [map_mul]
      exact mul_mul_mul_comm (G := IdeleClassGroup F) _ _ _ _)

private theorem normProjection_mem (F : Type) [Field F] [NumberField F]
    (c : IdeleClassGroup F) : normProjection F c ∈ IdeleClassGroup.normOneSubgroup := by
  change IdeleClassGroup.absoluteNorm
    (c * ideleClassPositiveArchimedeanSection F (IdeleClassGroup.absoluteNorm c)) = 1
  rw [map_mul, ideleClassPositiveArchimedeanSection_absoluteNorm, mul_inv_cancel]

private theorem normProjection_continuous (F : Type) [Field F] [NumberField F] :
    Continuous (normProjection F) :=
  continuous_id.mul ((ideleClassPositiveArchimedeanSectionContinuous F).continuous.comp
    (continuous_classNorm F))

private theorem class_cubes_closed (F : Type) [Field F] [NumberField F] :
    IsClosed (Set.range (fun c : IdeleClassGroup F => c ^ 3)) := by
  let H := IdeleClassGroup.normOneSubgroup (K := F)
  let K : Set (IdeleClassGroup F) := (fun c : IdeleClassGroup F => c ^ 3) '' H
  have hK : IsClosed K :=
    (IdeleClassGroup.normOneSubgroup_isCompact.image (continuous_id.pow 3)).isClosed
  have heq : Set.range (fun c : IdeleClassGroup F => c ^ 3) =
      normProjection F ⁻¹' K := by
    ext c
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨normProjection F a, normProjection_mem F a, (map_pow _ _ _).symm⟩
    · rintro ⟨a, ha, h⟩
      obtain ⟨s, hs⟩ := positive_cube (IdeleClassGroup.absoluteNorm c)
      refine ⟨a * (ideleClassPositiveArchimedeanSection F s)⁻¹, ?_⟩
      change a ^ 3 = c * ideleClassPositiveArchimedeanSection F
        (IdeleClassGroup.absoluteNorm c) at h
      change (a * (ideleClassPositiveArchimedeanSection F s)⁻¹) ^ 3 = c
      rw [mul_pow (M := IdeleClassGroup F), inv_pow, ← map_pow, hs, h]
      exact mul_inv_cancel_right _ _
  rw [heq]
  exact hK.preimage (normProjection_continuous F)

theorem rationalCubes_isClosed (F : Type) [Field F] [NumberField F] :
    IsClosed (rationalCubes F : Set (Ideles F)) := by
  let e := IdeleGroup.equivAdeleRingUnitsContinuousMulEquiv F
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup F)
  have hclosed : IsClosed ((q ∘ e.symm) ⁻¹'
      Set.range (fun c : IdeleClassGroup F => c ^ 3)) :=
    (class_cubes_closed F).preimage (QuotientGroup.continuous_mk.comp e.symm.continuous)
  have heq : (rationalCubes F : Set (Ideles F)) =
      (q ∘ e.symm) ⁻¹' Set.range (fun c : IdeleClassGroup F => c ^ 3) := by
    ext x
    change x ∈ rationalCubes F ↔ ∃ c : IdeleClassGroup F, c ^ 3 = q (e.symm x)
    rw [mem_rationalCubes_iff]
    constructor
    · rintro ⟨r, a, rfl⟩
      refine ⟨q (e.symm a), ?_⟩
      change q (e.symm a) ^ 3 = q (e.symm
        (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F r * a ^ 3))
      rw [map_mul, map_pow, map_mul, map_pow]
      have hr : q (e.symm (NumberField.IdeleGroup.unitEmbedding (𝓞 F) F r)) = 1 := by
        apply (QuotientGroup.eq_one_iff _).mpr
        exact ⟨r, rfl⟩
      rw [hr, one_mul (M := IdeleClassGroup F)]
    · rintro ⟨c, hc⟩
      obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup F) c
      have hd : e.symm x / a ^ 3 ∈ IdeleGroup.principalSubgroup F := by
        apply QuotientGroup.eq_iff_div_mem.mp
        change q (e.symm x) = q (a ^ 3)
        rw [map_pow]
        exact hc.symm
      obtain ⟨r, hr⟩ := hd
      refine ⟨r, e a, ?_⟩
      have hid : e.symm x = IdeleGroup.principalIdele F r * a ^ 3 := by
        rw [hr]
        exact (div_mul_cancel _ _).symm
      have hx := congrArg e hid
      rw [map_mul, map_pow, e.apply_symm_apply] at hx
      change x = IdeleGroup.equivAdeleRingUnits (IdeleGroup.principalIdele F r) *
        e a ^ 3 at hx
      rw [IdeleGroup.equivAdeleRingUnits_principalIdele] at hx
      exact hx
  rw [heq]
  exact hclosed

theorem cubicClasses_compact_hausdorff (F : Type) [Field F] [NumberField F] :
    CompactSpace (CubicClasses F) ∧ T2Space (CubicClasses F) ∧
      IsTopologicalGroup (CubicClasses F) := by

  haveI : IsClosed (rationalCubes F : Set (Ideles F)) := rationalCubes_isClosed F
  refine ⟨?_, inferInstance, inferInstance⟩
  exact cubic_compact F

theorem coveringTorus_quotient_compact (F : Type) [Field F] [NumberField F]
    (E : Type*) [Group E] [TopologicalSpace E] [IsTopologicalGroup E]
    (π : E →* Ideles F) (hπ : Continuous π) (hopen : IsOpenMap π)
    (hsurj : Function.Surjective π) (R : Subgroup E) [R.Normal]
    (hkernel : π.ker ≤ R)
    (hrational : NumberField.IdeleGroup.principalSubgroup (𝓞 F) F ≤ R.map π)
    (hcubes : cubes F ≤ R.map π) :
    CompactSpace (E ⧸ R) := by

  have hN : rationalCubes F ≤ R.map π := sup_le hrational hcubes
  let Mq : Subgroup (Ideles F) := R.map π

  haveI hcubic : CompactSpace (CubicClasses F) := (cubicClasses_compact_hausdorff F).1
  haveI hMcompact : CompactSpace (Ideles F ⧸ Mq) := by
    have hsurj_id : Function.Surjective
        (⇑(QuotientGroup.mk' Mq) ∘ ⇑(MonoidHom.id (Ideles F))) :=
      Function.Surjective.comp (QuotientGroup.mk'_surjective Mq) Function.surjective_id
    set g : Ideles F ⧸ rationalCubes F →* Ideles F ⧸ Mq :=
      QuotientGroup.map (rationalCubes F) Mq (MonoidHom.id (Ideles F)) hN with hg
    have hcont : Continuous g := by
      refine (QuotientGroup.isOpenQuotientMap_mk (G := Ideles F)
        (N := rationalCubes F)).continuous_comp_iff.mp ?_
      have h1 : (⇑g ∘ QuotientGroup.mk) =
          ⇑((QuotientGroup.mk' Mq).comp (MonoidHom.id (Ideles F))) := by
        funext x
        rw [hg]
        exact QuotientGroup.map_mk (N := rationalCubes F) Mq (MonoidHom.id (Ideles F)) hN x
      rw [h1]
      exact QuotientGroup.continuous_mk.comp continuous_id
    have hsurjg : Function.Surjective g :=
      QuotientGroup.map_surjective_of_surjective (N := rationalCubes F) Mq
        (MonoidHom.id (Ideles F)) hsurj_id hN
    rw [← isCompact_univ_iff]
    have h2 := isCompact_univ.image hcont
    rwa [Set.image_univ, Set.range_eq_univ.mpr hsurjg] at h2

  let fq : E →* Ideles F ⧸ Mq := (QuotientGroup.mk' Mq).comp π
  have hfker : R ≤ fq.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff (π x)).mpr (Subgroup.mem_map_of_mem π hx)
  let φ : E ⧸ R →* Ideles F ⧸ Mq := QuotientGroup.lift R fq hfker
  have hφsurj : Function.Surjective ⇑φ :=
    QuotientGroup.lift_surjective_of_surjective (N := R) fq (by
      have h : Function.Surjective (⇑(QuotientGroup.mk' Mq) ∘ ⇑π) :=
        Function.Surjective.comp (QuotientGroup.mk'_surjective Mq) hsurj
      exact h) hfker
  have hφinj : Function.Injective ⇑φ := by
    rw [QuotientGroup.injective_lift_iff (N := R) fq hfker]
    refine le_antisymm hfker ?_
    intro x hx
    have hxM : π x ∈ Mq := by
      have h1 : fq x = 1 := MonoidHom.mem_ker.mp hx
      simpa [fq, MonoidHom.comp_apply, QuotientGroup.coe_mk'] using
        (QuotientGroup.eq_one_iff (π x)).mp h1
    obtain ⟨r, hr, hπr⟩ := Subgroup.mem_map.mp hxM
    have hmem : x * r⁻¹ ∈ π.ker := by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hπr, mul_inv_cancel]
    have hxR : x * r⁻¹ ∈ R := hkernel hmem
    have hx' : x = (x * r⁻¹) * r := by group
    rw [hx']
    exact R.mul_mem hxR hr
  have hφcont : Continuous ⇑φ := by
    refine (QuotientGroup.isOpenQuotientMap_mk (G := E) (N := R)).continuous_comp_iff.mp ?_
    have h1 : (⇑φ ∘ QuotientGroup.mk) = ⇑fq := by
      funext x
      exact QuotientGroup.lift_mk (N := R) (φ := fq) hfker x
    rw [h1]
    exact QuotientGroup.continuous_mk.comp hπ
  have hopenmap : IsOpenMap ⇑φ := by
    refine (QuotientGroup.isOpenQuotientMap_mk (G := E) (N := R)).isOpenMap_iff.mpr ?_
    have h1 : (⇑φ ∘ QuotientGroup.mk) = ⇑fq := by
      funext x
      exact QuotientGroup.lift_mk (N := R) (φ := fq) hfker x
    rw [h1]
    exact (QuotientGroup.isOpenMap_coe (G := Ideles F) (N := Mq)).comp hopen
  let e : E ⧸ R ≃ Ideles F ⧸ Mq := Equiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have homeo : E ⧸ R ≃ₜ Ideles F ⧸ Mq :=
    e.toHomeomorphOfContinuousOpen hφcont hopenmap
  exact Homeomorph.compactSpace homeo.symm

end
end DedekindZetaZeroFree.KPCubicIdele
