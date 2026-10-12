module

public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanTraceClassification
public import DedekindZetaZeroFree.Adeles.Characters.AdditiveQuotient.PointSeparation

@[expose] public section

section

open scoped NumberField nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
namespace DedekindZetaZeroFree.KPCompactFourierSeparation
noncomputable section
set_option allowUnsafeReducibility true in
attribute [local reducible] NumberField.AdeleRing
 def archIn (F : Type) [Field F] [NumberField F] :
    InfiniteAdeleRing F →+ AdeleRing (𝓞 F) F where
  toFun x := (x, 0)
  map_zero' := rfl
  map_add' _ _ := by simp

private theorem archIn_cont (F : Type) [Field F] [NumberField F] :
    Continuous (archIn F) := continuous_id.prodMk continuous_const

private theorem diagonal_decomp (F : Type) [Field F] [NumberField F] (a : F) :
    algebraMap F (AdeleRing (𝓞 F) F) a =
      archIn F (algebraMap F (InfiniteAdeleRing F) a) +
        ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) a) : AdeleRing (𝓞 F) F) := by
  apply Prod.ext <;> simp [archIn]

private theorem character_rational_arch
    (F : Type) [Field F] [NumberField F]
    (χ : AddChar (AdeleRing (𝓞 F) F) Circle) (hc : Continuous χ)
    (hF : ∀ t : F, χ (algebraMap F (AdeleRing (𝓞 F) F) t) = 1) :
    ∃ a : F, ∀ x : InfiniteAdeleRing F,
      χ (x, 0) = Circle.exp (2 * Real.pi * KPArchTrace.infiniteTracePairing F x
        (algebraMap F (InfiniteAdeleRing F) a)) := by
  let χa := χ.compAddMonoidHom (archIn F)
  have hca : Continuous χa := hc.comp (archIn_cont F)
  obtain ⟨y, hy, _⟩ := KPArchTrace.infinite_character_classification F χa hca
  obtain ⟨T, k, I, _, hker, hI, hIfiber, _, _⟩ := kp_adelic_character_open_kernel F χ hc
  have hdiag : ∀ a : F, a ∈ (I : FractionalIdeal (𝓞 F)⁰ F) →
      χa (algebraMap F (InfiniteAdeleRing F) a) = 1 := by
    intro a ha
    have haf : algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈
        KPAdelicCharacter.finiteIdealNeighborhood F T k := by
      have : a ∈ (I : Set F) := ha
      rwa [hIfiber] at this
    have h := hF a
    rw [diagonal_decomp F a, AddChar.map_add_eq_mul, hker _ haf, mul_one] at h
    exact h
  obtain ⟨a, _, ha⟩ := KPArchTrace.infinite_character_parameter_mem_inverseDifferent
    F (I : FractionalIdeal (𝓞 F)⁰ F) hI χa hca y hy hdiag
  refine ⟨a, ?_⟩
  intro x
  simpa only [ha, χa, AddChar.compAddMonoidHom_apply, archIn, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using hy x

private theorem characters_eq_of_arch_eq
    (F : Type) [Field F] [NumberField F]
    (χ η : AddChar (AdeleRing (𝓞 F) F) Circle)
    (hc : Continuous χ) (he : Continuous η)
    (hχF : ∀ t : F, χ (algebraMap F (AdeleRing (𝓞 F) F) t) = 1)
    (hηF : ∀ t : F, η (algebraMap F (AdeleRing (𝓞 F) F) t) = 1)
    (ha : ∀ x : InfiniteAdeleRing F, χ (x, 0) = η (x, 0)) : χ = η := by
  have hf : ∀ z : FiniteAdeleRing (𝓞 F) F, χ (0, z) = η (0, z) := by
    have hh : (fun z : FiniteAdeleRing (𝓞 F) F => χ (0, z)) = (fun z => η (0, z)) := by
      apply (finiteAdele_dense F).equalizer
        (hc.comp (continuous_const.prodMk continuous_id))
        (he.comp (continuous_const.prodMk continuous_id))
      funext t
      have h1 := hχF t
      have h2 := hηF t
      rw [diagonal_decomp F t, AddChar.map_add_eq_mul] at h1 h2
      change χ (_, 0) * _ = 1 at h1
      change η (_, 0) * _ = 1 at h2
      rw [ha] at h1
      exact mul_left_cancel (h1.trans h2.symm)
    exact congrFun hh
  apply AddChar.ext
  intro x
  have hx : x = ((x.1, 0) : AdeleRing (𝓞 F) F) + ((0, x.2) : AdeleRing (𝓞 F) F) := by
    apply Prod.ext <;> simp
  rw [hx, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, ha, hf]

private theorem pairing_scale
    (F : Type) [Field F] [NumberField F]
    (x : InfiniteAdeleRing F) (a t : F) :
    KPArchTrace.infiniteTracePairing F
      (algebraMap F (InfiniteAdeleRing F) t * x)
      (algebraMap F (InfiniteAdeleRing F) a) =
    KPArchTrace.infiniteTracePairing F x
      (algebraMap F (InfiniteAdeleRing F) (t * a)) := by
  simp only [KPArchTrace.infiniteTracePairing, KPArchTrace.infiniteToSpace,
    PoissonArch.tracePairing, ContinuousLinearEquiv.apply_symm_apply, map_mul]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    simp only [Prod.fst_mul, Pi.mul_apply]
    ring
  · congr 1
    apply Finset.sum_congr rfl
    intro v _
    simp only [Prod.snd_mul, Pi.mul_apply]
    congr 1
    ring

theorem adelic_annihilator_scalar
      (F : Type) [Field F] [NumberField F]
      (ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) Circle)
      (hψcont : Continuous ψ) (hψne : ψ ≠ 1)
      (hψF : ∀ t : F, ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t) = 1)
      (φ : AddChar (NumberField.AdeleRing (𝓞 F) F) Circle)
      (hφcont : Continuous φ)
      (hφF : ∀ t : F, φ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t) = 1) :
      ∃ t : F, ∀ x : NumberField.AdeleRing (𝓞 F) F,
        φ x = ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t * x) := by
  classical
  obtain ⟨a, ha⟩ := character_rational_arch F ψ hψcont hψF
  obtain ⟨b, hb⟩ := character_rational_arch F φ hφcont hφF
  have hane : a ≠ 0 := by
    intro hzero
    apply hψne
    apply characters_eq_of_arch_eq F ψ 1 hψcont continuous_const hψF
      (by intro t; rfl)
    intro x
    rw [ha, hzero, map_zero]
    have hz : KPArchTrace.infiniteTracePairing F x 0 = 0 := by
      unfold KPArchTrace.infiniteTracePairing KPArchTrace.infiniteToSpace
      rw [map_zero, map_zero]
      simp [PoissonArch.tracePairing]
    rw [hz, mul_zero, Circle.exp_zero]
    rfl
  let t := b / a
  let η := ψ.mulShift (algebraMap F (AdeleRing (𝓞 F) F) t)
  have hη : Continuous η := hψcont.comp (continuous_const.mul continuous_id)
  have hηF : ∀ r : F, η (algebraMap F (AdeleRing (𝓞 F) F) r) = 1 := by
    intro r
    simpa [η, AddChar.mulShift_apply, ← map_mul] using hψF (t * r)
  have heq : φ = η := characters_eq_of_arch_eq F φ η hφcont hη hφF hηF (by
    intro x
    change φ (x, 0) = ψ (algebraMap F (AdeleRing (𝓞 F) F) t *
      ((x, 0) : AdeleRing (𝓞 F) F))
    have hm : algebraMap F (AdeleRing (𝓞 F) F) t * ((x, 0) : AdeleRing (𝓞 F) F) =
        ((algebraMap F (InfiniteAdeleRing F) t * x, 0) : AdeleRing (𝓞 F) F) := by
      apply Prod.ext <;> simp [mul_comm]
    rw [hm, ha, hb, pairing_scale]
    dsimp [t]
    rw [div_mul_cancel₀ b hane])
  refine ⟨t, ?_⟩
  intro x
  rw [heq]
  simp [η, AddChar.mulShift_apply, mul_comm]
end
end DedekindZetaZeroFree.KPCompactFourierSeparation

end

section

namespace DedekindZetaZeroFree.KPCompactFourierSeparation

theorem scalar_character_injective
    {F : Type*} [Field F] {A : Type*} [CommRing A] [Algebra F A]
    {M : Type*} [Group M] (ψ : AddChar A M) (hψne : ψ ≠ 1) :
    Function.Injective (fun t : F => fun x : A => ψ (algebraMap F A t * x)) := by
  intro t s hts
  have hfun : (fun x : A => ψ (algebraMap F A t * x))
      = fun x : A => ψ (algebraMap F A s * x) := hts
  by_contra hne
  have hu : t - s ≠ 0 := sub_ne_zero.mpr hne
  have key : ∀ x : A, ψ (algebraMap F A (t - s) * x) = 1 := by
    intro x
    have hx := congrFun hfun x
    have hsub : algebraMap F A (t - s) * x = algebraMap F A t * x - algebraMap F A s * x := by
      rw [map_sub, sub_mul]
    rw [hsub, sub_eq_add_neg, AddChar.map_add_eq_mul, hx, AddChar.map_neg_eq_inv, mul_inv_cancel]
  obtain ⟨y, hy⟩ := AddChar.ne_one_iff.mp hψne
  refine hy ?_
  have h := key (algebraMap F A (t - s)⁻¹ * y)
  rwa [← mul_assoc, ← map_mul, mul_inv_cancel₀ hu, map_one, one_mul] at h

end DedekindZetaZeroFree.KPCompactFourierSeparation

end

section

namespace DedekindZetaZeroFree

open MeasureTheory
open scoped NumberField

namespace KPCompactFourier

open MeasureTheory Set
variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

 noncomputable def charMap (χ : {χ : AddChar X Circle // Continuous χ}) : C(X, ℂ) :=
  ⟨fun x => (χ.val x : ℂ), continuous_subtype_val.comp χ.property⟩

 noncomputable def charAlgebra : StarSubalgebra ℂ C(X, ℂ) where
  toSubalgebra := Algebra.adjoin ℂ (range (charMap (X := X)))
  star_mem' := by
    change Algebra.adjoin ℂ (range (charMap (X := X))) ≤
      star (Algebra.adjoin ℂ (range (charMap (X := X))))
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨χ, hc⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨⟨χ⁻¹, hc.comp continuous_neg⟩, ?_⟩
    ext x
    simpa only [charMap, ContinuousMap.star_apply, ContinuousMap.coe_mk,
      AddChar.inv_apply, AddChar.map_neg_eq_inv, Complex.star_def] using Circle.coe_inv_eq_conj (χ x)

private theorem charAlgebra_span : (charAlgebra (X := X)).toSubalgebra.toSubmodule =
    Submodule.span ℂ (range (charMap (X := X))) := by
  apply Algebra.adjoin_eq_span_of_subset
  refine Subset.trans ?_ Submodule.subset_span
  intro x hx
  refine Submonoid.closure_induction (fun _ => id) ?_ ?_ hx
  · refine ⟨⟨1, continuous_const⟩, ?_⟩
    ext x
    simp [charMap]
  · rintro _ _ _ _ ⟨⟨χ, hc⟩, rfl⟩ ⟨⟨ψ, hd⟩, rfl⟩
    refine ⟨⟨χ * ψ, hc.mul hd⟩, ?_⟩
    ext x
    simp [charMap]

private theorem char_span_dense
    (hsep : ∀ x y : X, x ≠ y → ∃ χ : AddChar X Circle, Continuous χ ∧ χ x ≠ χ y) :
    (Submodule.span ℂ (range (charMap (X := X)))).topologicalClosure = ⊤ := by
  rw [← charAlgebra_span]
  have hA : (charAlgebra (X := X)).SeparatesPoints := by
    intro x y hxy
    obtain ⟨χ, hc, hn⟩ := hsep x y hxy
    refine ⟨_, ⟨charMap ⟨χ, hc⟩, Algebra.subset_adjoin ⟨⟨χ, hc⟩, rfl⟩, rfl⟩, ?_⟩
    exact fun h => hn (Subtype.coe_injective h)
  exact congrArg (fun A : StarSubalgebra ℂ C(X, ℂ) => A.toSubalgebra.toSubmodule)
    (ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
      (charAlgebra (X := X)) hA)

variable (μ : Measure X) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]

 theorem int_cont (f : C(X, ℂ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

 noncomputable def integralFunctional (u : C(X, ℂ)) : C(X, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, u x * f x ∂μ
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply, mul_add]
        exact integral_add (int_cont μ (u * f)) (int_cont μ (u * g))
      map_smul' := by
        intro c f
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm (u _) c]
        exact integral_const_mul c _ }
    ‖u‖ (by
      intro f
      calc
        ‖∫ x, u x * f x ∂μ‖ ≤ ‖u‖ * ‖f‖ := by
          simpa using norm_integral_le_of_norm_le_const
            (μ := μ) (Filter.Eventually.of_forall (fun x => by
              rw [norm_mul]
              exact mul_le_mul (ContinuousMap.norm_coe_le_norm u x)
                (ContinuousMap.norm_coe_le_norm f x) (norm_nonneg _) (norm_nonneg _))))

theorem char_integral_zero (χ : AddChar X Circle) (hne : χ ≠ 1) :
    (∫ x, (χ x : ℂ) ∂μ) = 0 := by
  obtain ⟨z, hz⟩ : ∃ z, χ z ≠ 1 := by
    by_contra! h
    apply hne
    apply DFunLike.ext
    intro z
    exact h z
  have heq := integral_add_left_eq_self (μ := μ) (fun x => (χ x : ℂ)) z
  simp only [χ.map_add_eq_mul, Circle.coe_mul, integral_const_mul] at heq
  have hc : (χ z : ℂ) ≠ 1 := fun h => hz (Circle.coe_eq_one.mp h)
  by_contra hI
  exact hc ((mul_eq_right₀ hI).mp heq)

theorem uniqueness_of_characters_separate
    (hsep : ∀ x y : X, x ≠ y → ∃ χ : AddChar X Circle, Continuous χ ∧ χ x ≠ χ y)
    (h : X → ℂ) (hh : Continuous h)
    (hfourier : ∀ χ : AddChar X Circle, Continuous χ → χ ≠ 1 →
      (∫ x, h x * (χ x : ℂ) ∂μ) = 0) :
    ∀ x, h x = ∫ y, h y ∂μ := by
  let u : C(X, ℂ) := ⟨fun x => h x - ∫ y, h y ∂μ, hh.sub continuous_const⟩
  let L := integralFunctional μ u
  have hgen : ∀ f ∈ range (charMap (X := X)), f ∈ L.ker := by
    rintro _ ⟨⟨χ, hc⟩, rfl⟩
    change (∫ x, (h x - ∫ y, h y ∂μ) * (χ x : ℂ) ∂μ) = 0
    simp_rw [sub_mul]
    rw [integral_sub]
    · by_cases hn : χ = 1
      · subst χ
        simp
      · rw [hfourier χ hc hn, integral_const_mul, char_integral_zero μ χ hn]
        simp
    · exact int_cont μ (⟨h, hh⟩ * charMap ⟨χ, hc⟩)
    · exact (int_cont μ (charMap ⟨χ, hc⟩)).const_mul _
  have hspan : Submodule.span ℂ (range (charMap (X := X))) ≤ L.ker :=
    Submodule.span_le.mpr hgen
  have htop : (⊤ : Submodule ℂ C(X, ℂ)) ≤ L.ker := by
    rw [← char_span_dense hsep]
    exact Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  have hzero : ∫ x, u x * star (u x) ∂μ = 0 := by
    have hm := htop (Submodule.mem_top (x := star u))
    exact hm
  have hreal : ∫ x, ‖u x‖ ^ 2 ∂μ = 0 := by
    have h := hzero
    simp_rw [Complex.star_def, Complex.mul_conj'] at h
    simp_rw [← Complex.ofReal_pow] at h
    rw [integral_complex_ofReal] at h
    exact Complex.ofReal_injective h
  have hae : (fun x => ‖u x‖ ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
      ((u.continuous.norm.pow 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).mp hreal
  have hu : (u : X → ℂ) = 0 := by
    apply MeasureTheory.Measure.eq_of_ae_eq (μ := μ) _ u.continuous continuous_const
    filter_upwards [hae] with x hx
    change u x = 0
    exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hx)
  intro x
  have hx := congrFun hu x
  exact sub_eq_zero.mp hx

end KPCompactFourier

namespace KPCompactFourier

abbrev AdditiveQuotient (F : Type) [Field F] [NumberField F] :=
  NumberField.AdeleRing (𝓞 F) F ⧸ NumberField.AdeleRing.principalSubgroup (𝓞 F) F

noncomputable instance quotientMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace (AdditiveQuotient F) := borel (AdditiveQuotient F)

instance quotientBorelSpace (F : Type) [Field F] [NumberField F] :
    BorelSpace (AdditiveQuotient F) := ⟨rfl⟩

end KPCompactFourier

theorem kp_adelic_character_exhaustion
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) Circle)
    (hψcont : Continuous ψ) (hψne : ψ ≠ 1)
    (hψF : ∀ t : F, ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t) = 1)
    (χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle)
    (hχcont : Continuous χ) (hχne : χ ≠ 1) :
    ∃! t : F, t ≠ 0 ∧ ∀ x : NumberField.AdeleRing (𝓞 F) F,
      χ (QuotientAddGroup.mk x) =
        ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t * x) := by
  let A := NumberField.AdeleRing (𝓞 F) F
  let S := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let φ : AddChar A Circle := χ.compAddMonoidHom (QuotientAddGroup.mk' S)
  have hφ (x : A) : φ x = χ (QuotientAddGroup.mk x) := rfl
  have hφcont : Continuous φ := hχcont.comp QuotientAddGroup.continuous_mk
  have hφF (r : F) : φ (algebraMap F A r) = 1 := by
    rw [hφ]
    have hr : (QuotientAddGroup.mk (algebraMap F A r) : KPCompactFourier.AdditiveQuotient F) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).mpr ⟨r, rfl⟩
    rw [hr, χ.map_zero_eq_one]
  obtain ⟨t, ht⟩ := KPCompactFourierSeparation.adelic_annihilator_scalar
    F ψ hψcont hψne hψF φ hφcont hφF
  have hformula (x : A) : χ (QuotientAddGroup.mk x) = ψ (algebraMap F A t * x) := ht x
  have htne : t ≠ 0 := by
    intro hzero
    apply hχne
    apply DFunLike.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    simpa [hzero] using hformula x
  refine ⟨t, ⟨htne, hformula⟩, ?_⟩
  intro s hs
  apply KPCompactFourierSeparation.scalar_character_injective ψ hψne
  funext x
  exact (hs.2 x).symm.trans (hformula x)

end DedekindZetaZeroFree

end

section

namespace DedekindZetaZeroFree

open MeasureTheory
open scoped NumberField

namespace KPCompactFourier

open MeasureTheory Set
variable {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

variable (μ : Measure X) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]

end KPCompactFourier

namespace KPCompactFourier

noncomputable def representative (F : Type) [Field F] [NumberField F] :
    AdditiveQuotient F → NumberField.AdeleRing (𝓞 F) F := Quotient.out

noncomputable def unipotentFiber
    (F : Type) [Field F] [NumberField F] {G : Type*} [Group G]
    (n : AddChar (NumberField.AdeleRing (𝓞 F) F) G) (θ : G → ℂ) (g : G)
    (x : AdditiveQuotient F) : ℂ :=
  θ (n (representative F x) * g)

noncomputable def fourierPeriod
    (F : Type) [Field F] [NumberField F] {G : Type*} [Group G]
    (μ : Measure (AdditiveQuotient F))
    (ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) Circle)
    (n : AddChar (NumberField.AdeleRing (𝓞 F) F) G) (θ : G → ℂ) (g : G) : ℂ :=
  ∫ x, unipotentFiber F n θ g x * (ψ (representative F x) : ℂ) ∂μ

end KPCompactFourier

theorem kp_adelic_scaled_character
    (F : Type) [Field F] [NumberField F]
    (ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) Circle)
    (hψcont : Continuous ψ) (hψne : ψ ≠ 1)
    (hψF : ∀ t : F, ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t) = 1)
    (t : F) (ht : t ≠ 0) :
    ∃! χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle,
      Continuous χ ∧ χ ≠ 1 ∧ ∀ x : NumberField.AdeleRing (𝓞 F) F,
        χ (QuotientAddGroup.mk x) =
          ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t * x) := by
  let A := NumberField.AdeleRing (𝓞 F) F
  let S := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let m : A →+ A :=
    { toFun := fun x => algebraMap F A t * x
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  let φ := ψ.compAddMonoidHom m
  have hS : S ≤ φ.toAddMonoidHom.ker := by
    rintro x ⟨r, rfl⟩
    change Additive.ofMul (ψ (algebraMap F A t * algebraMap F A r)) = 0
    rw [← map_mul, hψF]
    rfl
  let χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle :=
    AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift S φ.toAddMonoidHom hS)
  have hχ : ∀ x : A, χ (QuotientAddGroup.mk x) = ψ (algebraMap F A t * x) := by
    intro x
    change Additive.toMul ((QuotientAddGroup.lift S φ.toAddMonoidHom hS)
      (QuotientAddGroup.mk x)) = _
    rw [QuotientAddGroup.lift_mk']
    rfl
  refine ⟨χ, ⟨?_, ?_, hχ⟩, ?_⟩
  · apply (QuotientAddGroup.isQuotientMap_mk S).continuous_iff.mpr
    change Continuous (fun x : A => χ (QuotientAddGroup.mk x))
    simp_rw [hχ]
    exact hψcont.comp (continuous_const.mul continuous_id)
  · intro heq
    apply hψne
    apply DFunLike.ext
    intro x
    have hx := hχ (algebraMap F A t⁻¹ * x)
    rw [heq] at hx
    have hinv : algebraMap F A t * algebraMap F A t⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ ht, map_one]
    simpa [← mul_assoc, hinv] using hx.symm
  · intro χ' hχ'
    apply DFunLike.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact (hχ'.2.2 x).trans (hχ x).symm

theorem kp_additive_adelic_fourier_uniqueness
    (F : Type) [Field F] [NumberField F]
    [CompactSpace (KPCompactFourier.AdditiveQuotient F)]
    [T2Space (KPCompactFourier.AdditiveQuotient F)]
    (μ : Measure (KPCompactFourier.AdditiveQuotient F))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (h : KPCompactFourier.AdditiveQuotient F → ℂ) (hh : Continuous h)
    (hfourier : ∀ χ : AddChar (KPCompactFourier.AdditiveQuotient F) Circle,
      Continuous χ → χ ≠ 1 → (∫ x, h x * (χ x : ℂ) ∂μ) = 0) :
    ∀ x, h x = ∫ y, h y ∂μ := by
  exact KPCompactFourier.uniqueness_of_characters_separate μ
    (AdelicSeparation.additiveAdeleQuotient_characters_separate F) h hh hfourier

theorem kp_right_translate_periods_force_constant
    (F : Type) [Field F] [NumberField F]
    [CompactSpace (KPCompactFourier.AdditiveQuotient F)]
    [T2Space (KPCompactFourier.AdditiveQuotient F)]
    (μ : Measure (KPCompactFourier.AdditiveQuotient F))
    [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (ψ : AddChar (NumberField.AdeleRing (𝓞 F) F) Circle)
    (hψcont : Continuous ψ) (hψne : ψ ≠ 1)
    (hψF : ∀ t : F, ψ (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t) = 1)
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : AddChar (NumberField.AdeleRing (𝓞 F) F) G) (hncont : Continuous n)
    (a : Fˣ → G)
    (hconj : ∀ (t : Fˣ) (x : NumberField.AdeleRing (𝓞 F) F),
      n x * a t = a t * n (algebraMap F (NumberField.AdeleRing (𝓞 F) F) (↑t⁻¹ : F) * x))
    (θ : G → ℂ) (hθcont : Continuous θ)
    (hθn : ∀ (t : F) (g : G),
      θ (n (algebraMap F (NumberField.AdeleRing (𝓞 F) F) t) * g) = θ g)
    (hθa : ∀ (t : Fˣ) (g : G), θ (a t * g) = θ g)
    (hperiod : ∀ g, KPCompactFourier.fourierPeriod F μ ψ n θ g = 0) :
    ∀ (g : G) (x : KPCompactFourier.AdditiveQuotient F),
      KPCompactFourier.unipotentFiber F n θ g x =
        ∫ y, KPCompactFourier.unipotentFiber F n θ g y ∂μ := by
  let A := NumberField.AdeleRing (𝓞 F) F
  let S := NumberField.AdeleRing.principalSubgroup (𝓞 F) F
  let Q := KPCompactFourier.AdditiveQuotient F
  have hfiber (g : G) (z : A) :
      KPCompactFourier.unipotentFiber F n θ g (QuotientAddGroup.mk z) = θ (n z * g) := by
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add S z
    obtain ⟨s, hs⟩ := r.property
    change θ (n (Quotient.out (QuotientAddGroup.mk z)) * g) = _
    rw [hr, ← hs, add_comm, n.map_add_eq_mul, mul_assoc, hθn]
  have hfcont (g : G) : Continuous (KPCompactFourier.unipotentFiber F n θ g) := by
    apply (QuotientAddGroup.isQuotientMap_mk S).continuous_iff.mpr
    change Continuous (fun z : A => KPCompactFourier.unipotentFiber F n θ g
      (QuotientAddGroup.mk z))
    simp_rw [hfiber]
    exact hθcont.comp (hncont.mul continuous_const)
  intro g
  apply kp_additive_adelic_fourier_uniqueness F μ _ (hfcont g)
  intro χ hχcont hχne
  obtain ⟨t, ⟨ht, hχ⟩, _⟩ :=
    kp_adelic_character_exhaustion F ψ hψcont hψne hψF χ hχcont hχne
  let u : Fˣ := Units.mk0 t ht
  let m : A →+ A :=
    { toFun := fun z => algebraMap F A t * z
      map_zero' := mul_zero _
      map_add' := mul_add _ }
  have hS : S ≤ ((QuotientAddGroup.mk' S).comp m).ker := by
    rintro z ⟨s, rfl⟩
    change QuotientAddGroup.mk (algebraMap F A t * algebraMap F A s) = 0
    rw [← map_mul]
    exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨t * s, rfl⟩
  let D : Q →+ Q := QuotientAddGroup.lift S ((QuotientAddGroup.mk' S).comp m) hS
  have hD (z : A) : D (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (algebraMap F A t * z) := QuotientAddGroup.lift_mk' S hS z
  have hDcont : Continuous D := by
    apply (QuotientAddGroup.isQuotientMap_mk S).continuous_iff.mpr
    change Continuous (fun z : A => D (QuotientAddGroup.mk z))
    simp_rw [hD]
    exact QuotientAddGroup.continuous_mk.comp (continuous_const.mul continuous_id)
  have hinv : algebraMap F A t * algebraMap F A t⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ ht, map_one]
  have hDsurj : Function.Surjective D := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨QuotientAddGroup.mk (algebraMap F A t⁻¹ * z), ?_⟩
    rw [hD, ← mul_assoc, hinv, one_mul]
  have hDmp : MeasurePreserving D μ μ := D.measurePreserving hDcont hDsurj rfl
  have htransform (q : Q) :
      KPCompactFourier.unipotentFiber F n θ (a u * g) (D q) *
        (ψ (KPCompactFourier.representative F (D q)) : ℂ) =
      KPCompactFourier.unipotentFiber F n θ g q * (χ q : ℂ) := by
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [hD, hfiber, hfiber]
    have hrep : ψ (KPCompactFourier.representative F
        (QuotientAddGroup.mk (algebraMap F A t * z))) = ψ (algebraMap F A t * z) := by
      obtain ⟨r, hr⟩ := QuotientAddGroup.mk_out_eq_add S (algebraMap F A t * z)
      obtain ⟨s, hs⟩ := r.property
      change ψ (Quotient.out _) = _
      rw [hr, ← hs, ψ.map_add_eq_mul, hψF, mul_one]
    rw [hrep, hχ]
    congr 1
    rw [← mul_assoc, hconj, mul_assoc, hθa]
    congr 2
    apply congrArg n
    change algebraMap F A t⁻¹ * (algebraMap F A t * z) = z
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ht, map_one, one_mul]
  obtain ⟨χψ, ⟨hχψcont, _, hχψ⟩, _⟩ :=
    kp_adelic_scaled_character F ψ hψcont hψne hψF 1 one_ne_zero
  have hχψrep (q : Q) : χψ q = ψ (KPCompactFourier.representative F q) := by
    have hr := hχψ (KPCompactFourier.representative F q)
    simpa [KPCompactFourier.representative, map_one, Quotient.out_eq'] using hr
  have hintcont : Continuous (fun q : Q =>
      KPCompactFourier.unipotentFiber F n θ (a u * g) q *
        (ψ (KPCompactFourier.representative F q) : ℂ)) := by
    simp_rw [← hχψrep]
    exact (hfcont _).mul (continuous_subtype_val.comp hχψcont)
  have hint := integral_map_of_stronglyMeasurable (μ := μ)
    hDcont.measurable hintcont.stronglyMeasurable
  rw [hDmp.map_eq] at hint
  simp_rw [htransform] at hint
  exact hint.symm.trans (hperiod (a u * g))

end DedekindZetaZeroFree

end
