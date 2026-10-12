module

public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.BezoutSteinitzEquivalence
public import DedekindZetaZeroFree.Arithmetic.Ideals.RankTwoLattices.DeterminantAndLineClasses
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section

open scoped nonZeroDivisors

namespace DedekindZetaZeroFree

theorem kp_cusp_class_eq_iff_scalar
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0) :
    ClassGroup.mk K (Units.mk0 I hI) = ClassGroup.mk K (Units.mk0 J hJ) ↔
      ∃ c : K, c ≠ 0 ∧ FractionalIdeal.spanSingleton R⁰ c * I = J := by
  refine (ClassGroup.equiv K).injective.eq_iff.symm.trans ?_
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self,
    Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv, RingEquiv.refl_apply,
    QuotientGroup.mk'_eq_mk', mem_principal_ideals_iff,
    Units.ext_iff, Units.val_mul, Units.val_mk0, exists_prop]
  constructor
  · rintro ⟨X, ⟨x, hX⟩, hx⟩
    refine ⟨x, ?_, ?_⟩
    · rintro rfl
      simp [X.ne_zero.symm] at hX
    simpa only [hX, mul_comm] using! hx
  · rintro ⟨x, hx, eq_J⟩
    refine ⟨Units.mk0 _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx), ⟨x, rfl⟩, ?_⟩
    simpa only [mul_comm] using! eq_J

private theorem scalar_mul_ideal
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (c : K) (I : FractionalIdeal R⁰ K) :
    (FractionalIdeal.spanSingleton R⁰ c * I : FractionalIdeal R⁰ K).val =
      Submodule.map (LinearMap.mulLeft R c) I.val := by
  change ((FractionalIdeal.spanSingleton R⁰ c * I : FractionalIdeal R⁰ K) : Submodule R K) = _
  rw [FractionalIdeal.coe_mul, FractionalIdeal.coe_spanSingleton]
  ext x
  simp only [Submodule.mem_span_singleton_mul, Submodule.mem_map,
    LinearMap.mulLeft_apply]
  rfl

 theorem coordinate_full
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0) :
    Submodule.IsLattice K (coordinateLattice R K I J) := by
  obtain ⟨a, ha, ha0⟩ := (I : Submodule R K).ne_bot_iff.mp
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hI)
  obtain ⟨b, hb, hb0⟩ := (J : Submodule R K).ne_bot_iff.mp
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr hJ)
  refine ⟨(FractionalIdeal.fg_of_isNoetherianRing le_rfl I).prod
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl J), ?_⟩
  apply top_unique
  intro x _
  have he1 : ((a, 0) : K × K) ∈ coordinateLattice R K I J :=
    ⟨ha, Submodule.zero_mem _⟩
  have he2 : ((0, b) : K × K) ∈ coordinateLattice R K I J :=
    ⟨Submodule.zero_mem _, hb⟩
  have hx := (Submodule.span K (coordinateLattice R K I J : Set (K × K))).add_mem
    (Submodule.smul_mem _ (x.1 / a) (Submodule.subset_span he1))
    (Submodule.smul_mem _ (x.2 / b) (Submodule.subset_span he2))
  convert hx using 1
  ext <;> simp [div_mul_cancel₀, ha0, hb0]

 def coordinate_full_lattice
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal R⁰ K) (hI : I ≠ 0) (hJ : J ≠ 0) : FullLattice R K :=
  ⟨coordinateLattice R K I J, coordinate_full R K I J hI hJ⟩

private theorem determinant_nonzero
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) : determinantIdeal R K M ≠ 0 := by
  intro h
  apply kp_cusp_determinantSubmodule_ne_bot R K M
  exact (congrArg Subtype.val h).trans FractionalIdeal.coe_zero

private theorem determinant_class_map
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M N : FullLattice R K) (g : (K × K) ≃ₗ[K] (K × K))
    (hg : Submodule.map (g.toLinearMap.restrictScalars R) M.val = N.val) :
    determinantClass R K M = determinantClass R K N := by
  apply (kp_cusp_class_eq_iff_scalar R K _ _
    (determinant_nonzero R K M) (determinant_nonzero R K N)).mpr
  refine ⟨LinearMap.det g.toLinearMap, g.isUnit_det'.ne_zero, ?_⟩
  apply FractionalIdeal.coeToSubmodule_injective
  change (FractionalIdeal.spanSingleton R⁰ (LinearMap.det g.toLinearMap) *
    determinantIdeal R K M).val = (determinantIdeal R K N).val
  rw [scalar_mul_ideal]
  exact (kp_cusp_determinantSubmodule_map R K M.val g).symm.trans (by rw [hg]; rfl)

private theorem determinant_coordinate
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (D : FractionalIdeal R⁰ K) (hD : D ≠ 0) :
    determinantClass R K (coordinate_full_lattice R K 1 D one_ne_zero hD) =
      ClassGroup.mk K (Units.mk0 D hD) := by
  unfold determinantClass
  congr 1
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change determinantSubmodule R K (coordinateLattice R K 1 D) = D.val
  simpa only [one_mul] using kp_cusp_determinantSubmodule_coordinateLattice R K 1 D

 noncomputable def coordinate_prod_equiv
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I J : FractionalIdeal R⁰ K) :
    (I × J) ≃ₗ[R] coordinateLattice R K I J :=
  LinearEquiv.ofBijective
    { toFun := fun p => ⟨(p.1.val, p.2.val), p.1.property, p.2.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨by
      intro x y h
      have hh := congrArg Subtype.val h
      exact Prod.ext (Subtype.ext (congrArg Prod.fst hh))
        (Subtype.ext (congrArg Prod.snd hh)), by
      intro x
      exact ⟨(⟨x.val.1, x.property.1⟩, ⟨x.val.2, x.property.2⟩), rfl⟩⟩

 noncomputable def ring_unit_ideal_equiv
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    R ≃ₗ[R] (1 : FractionalIdeal R⁰ K).val :=
  LinearEquiv.ofBijective
    ({ toFun := fun r => ⟨algebraMap R K r, FractionalIdeal.coe_mem_one R⁰ r⟩
       map_add' := fun _ _ => Subtype.ext (map_add _ _ _)
       map_smul' := fun r x => Subtype.ext (by
         change algebraMap R K (r * x) = r • algebraMap R K x
         simp [Algebra.smul_def]) } :
      R →ₗ[R] (1 : FractionalIdeal R⁰ K).val)
    ⟨by
      intro x y h
      exact IsFractionRing.injective R K (congrArg Subtype.val h), by
      intro x
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff R⁰).mp x.property
      exact ⟨r, Subtype.ext hr⟩⟩

theorem kp_cusp_rank_two_normal_form
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) :
    ∃ (D : FractionalIdeal R⁰ K) (hD : D ≠ 0)
      (g : (K × K) ≃ₗ[K] (K × K)),
      Submodule.map (g.toLinearMap.restrictScalars R) M.val =
        coordinateLattice R K 1 D ∧
      ClassGroup.mk K (Units.mk0 D hD) = determinantClass R K M := by
  obtain ⟨I, J, w, hI, hJ, hcoeff, hdet, hcoords, hproj, e, he⟩ :=
    kp_cusp_line_adapted_ideal_splitting R K M (1, 0) (by simp)
  let D : FractionalIdeal R⁰ K := I * J
  have hD : D ≠ 0 := mul_ne_zero hI hJ
  let N := coordinate_full_lattice R K 1 D one_ne_zero hD
  letI : Submodule.IsLattice K M.val := M.property
  letI : Submodule.IsLattice K N.val := N.property
  obtain ⟨s⟩ := kp_cusp_ideal_steinitz_nonempty R K I J hI hJ
  let f : M.val ≃ₗ[R] N.val :=
    e.symm.trans (s.trans
      ((LinearEquiv.prodCongr (ring_unit_ideal_equiv R K) (LinearEquiv.refl R D)).trans
        (coordinate_prod_equiv R K 1 D)))
  obtain ⟨g, hg, _⟩ := kp_cusp_full_lattice_equiv_extension R K
    (K × K) (K × K) M.val N.val f
  refine ⟨D, hD, g, hg.2, ?_⟩
  exact (determinant_coordinate R K D hD).symm.trans
    (determinant_class_map R K M N g hg.2).symm

theorem kp_cusp_latticeEquivalent_iff_determinantClass_eq
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M N : FullLattice R K) :
    latticeEquivalent R K M.val N.val ↔
      determinantClass R K M = determinantClass R K N := by
  constructor
  · rintro ⟨g, hg⟩
    exact determinant_class_map R K M N g hg
  · intro h
    obtain ⟨D, hD, g, hg, hcD⟩ := kp_cusp_rank_two_normal_form R K M
    obtain ⟨E, hE, k, hk, hcE⟩ := kp_cusp_rank_two_normal_form R K N
    have hDE := hcD.trans (h.trans hcE.symm)
    obtain ⟨e⟩ := (kp_cusp_fractional_ideal_equiv_iff R K D E hD hE).mpr
      ((kp_cusp_class_eq_iff_scalar R K D E hD hE).mp hDE)
    let P := coordinate_full_lattice R K 1 D one_ne_zero hD
    let Q := coordinate_full_lattice R K 1 E one_ne_zero hE
    letI : Submodule.IsLattice K P.val := P.property
    letI : Submodule.IsLattice K Q.val := Q.property
    let f : P.val ≃ₗ[R] Q.val := (coordinate_prod_equiv R K 1 D).symm.trans
      ((LinearEquiv.prodCongr (LinearEquiv.refl R (1 : FractionalIdeal R⁰ K)) e).trans
        (coordinate_prod_equiv R K 1 E))
    obtain ⟨l, hl, _⟩ := kp_cusp_full_lattice_equiv_extension R K
      (K × K) (K × K) P.val Q.val f
    have hMP : (latticeSetoid R K).r M P := ⟨g, hg⟩
    have hPQ : (latticeSetoid R K).r P Q := ⟨l, hl.2⟩
    have hNQ : (latticeSetoid R K).r N Q := ⟨k, hk⟩
    exact (latticeSetoid R K).iseqv.trans
      ((latticeSetoid R K).iseqv.trans hMP hPQ)
      ((latticeSetoid R K).iseqv.symm hNQ)

noncomputable def latticeDeterminantClass
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Quotient (latticeSetoid R K) → ClassGroup R :=
  Quotient.lift (determinantClass R K) (by
    intro M N h
    exact (kp_cusp_latticeEquivalent_iff_determinantClass_eq R K M N).mp h)

@[simp] theorem latticeDeterminantClass_mk
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (M : FullLattice R K) :
    latticeDeterminantClass R K (Quotient.mk (latticeSetoid R K) M) =
      determinantClass R K M := by
  rfl

theorem kp_cusp_latticeDeterminantClass_bijective
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] :
    Function.Bijective (latticeDeterminantClass R K) := by
  constructor
  · intro x y h
    induction x using Quotient.inductionOn with
    | h M =>
      induction y using Quotient.inductionOn with
      | h N =>
        apply Quotient.sound
        exact (kp_cusp_latticeEquivalent_iff_determinantClass_eq R K M N).mpr h
  · intro c
    refine ClassGroup.induction K (fun I => ?_) c
    refine ⟨Quotient.mk (latticeSetoid R K)
      (coordinate_full_lattice R K 1 (I : FractionalIdeal R⁰ K) one_ne_zero I.ne_zero), ?_⟩
    rw [latticeDeterminantClass_mk, determinant_coordinate]
    congr 1
    exact Units.ext rfl

theorem kp_cusp_numberField_lattice_quotient_finite
    (F : Type*) [Field F] [NumberField F] :
    Finite (Quotient (latticeSetoid (NumberField.RingOfIntegers F) F)) := by
  letI : Fintype (ClassGroup (NumberField.RingOfIntegers F)) :=
    NumberField.RingOfIntegers.instFintypeClassGroup F
  exact Finite.of_injective (latticeDeterminantClass (NumberField.RingOfIntegers F) F)
    (kp_cusp_latticeDeterminantClass_bijective _ _).1

end DedekindZetaZeroFree
