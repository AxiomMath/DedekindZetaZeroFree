module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Conductors.PrimitiveCharactersByCRT
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Reciprocity.PrincipalLocalUnitRelation
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.IdealIdelesAndLocalFactors
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Characters.CongruenceCharacterDescent

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

set_option maxHeartbeats 2000000

noncomputable section
namespace DedekindZetaZeroFree.PrimitiveRay

variable {F : Type} [Field F] [NumberField F]

private theorem M_eq_narrow (hc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) : M F m hm = RayClassBridge.narrowIdealModulus F m hm := by
  letI : IsEmpty (ClassFieldTheory.RayClassRealPlace F) :=
    ⟨fun v => (NumberField.InfinitePlace.not_isReal_iff_isComplex.mpr (hc.isComplex v.val)) v.property⟩
  apply ClassFieldTheory.RayClassModulus.ext
  · rfl
  · simp [M_infinitePart, RayClassBridge.narrowIdealModulus_infinitePart]
private theorem CRT_iff (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (u : (v.adicCompletion F)ˣ) :
    CRTLocalHigherUnits F v k u ↔ u ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k := by
  rw [ClassFieldTheory.mem_rayLocalHigherUnitGroup_iff]
  rfl
private theorem principal_formula (hc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (χ : RayClassCharacter F m)
    (α : 𝓞 F) (hα : α ≠ 0) (hcop : Ideal.span {α} ⊔ m = ⊤) :
    χ (Ideal.span {α}) =
      (((∏ v ∈ (M F m hm).finitePart.support,
        RayClassBridge.ideleClassCharacter F hc m hm χ
          (IdeleGroup.finitePlaceIdeleClass v (CRTIntegralLocalUnit F v α hα))) : ℂˣ) : ℂ)⁻¹ := by
  have hI : Ideal.span {α} ≠ ⊥ := by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα
  let ρ : ClassFieldTheory.RayClassGroup (M F m hm) →* ℂˣ :=
    (M_eq_narrow hc m hm).symm ▸ RayClassBridge.rayCharacter F hc m hm χ
  have transEval (N N' : ClassFieldTheory.RayClassModulus F) (h : N = N')
      (r : ClassFieldTheory.RayClassGroup N' →* ℂˣ)
      (I : ClassFieldTheory.NumberFieldFractionalIdealGroup F)
      (hp : I ∈ ClassFieldTheory.rayClassPrimeToIdeals N)
      (hp' : I ∈ ClassFieldTheory.rayClassPrimeToIdeals N') :
      (h.symm ▸ r) (QuotientGroup.mk ⟨I, hp⟩) = r (QuotientGroup.mk ⟨I, hp'⟩) := by
    subst N'; rfl
  have transLocal (N N' : ClassFieldTheory.RayClassModulus F) (h : N = N')
      (r : ClassFieldTheory.RayClassGroup N' →* ℂˣ)
      (c : IdeleClassGroup F) :
      (h.symm ▸ r) ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F N).symm
        (QuotientGroup.mk' (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F N).congruenceSubgroup c)) =
      r ((ClassFieldTheory.GlobalClassFieldComparison.rayClassGroupEquivOriginalIdele F N').symm
        (QuotientGroup.mk' (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F N').congruenceSubgroup c)) := by
    subst N'; rfl
  have heval : (ρ (frozenPrincipalRayClass F m hm α hα hcop) : ℂ) = χ (Ideal.span {α}) := by
    change (↑(( (M_eq_narrow hc m hm).symm ▸ RayClassBridge.rayCharacter F hc m hm χ)
      (QuotientGroup.mk (frozenIntegralPrimeTo F m hm (Ideal.span {α}) _ hcop))) : ℂ) = _
    exact (congrArg (fun x : ℂˣ => (x : ℂ))
      (transEval _ _ (M_eq_narrow hc m hm) _ _
        (frozenIntegralPrimeTo F m hm (Ideal.span {α}) hI hcop).property
        ((RayClassBridge.integralUnit_mem_primeTo_iff F m hm _ hI).mpr hcop))).trans
      (RayClassBridge.rayCharacter_integral F hc m hm χ _ hI hcop)
  have hlocal : ∀ v u, ρ (frozenFinitePlaceRayClass F m hm v u) =
      RayClassBridge.ideleClassCharacter F hc m hm χ (IdeleGroup.finitePlaceIdeleClass v u) := by
    intro v u
    exact transLocal _ _ (M_eq_narrow hc m hm) _ _
  have hrel := congrArg ρ (rm_kummer_ray_principal_relation F hc m hm α hα hcop)
  rw [map_prod] at hrel
  simp only [map_inv, hlocal] at hrel
  have hev := congrArg (fun x : ℂˣ => (x : ℂ)) hrel
  rw [heval] at hev
  rw [Finset.prod_inv_distrib, Units.val_inv_eq_inv_val] at hev
  exact hev
private theorem support_eq (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) :
    (M F m hm).finitePart.support = CRTIdealSupport F m := by
  ext v
  simp only [Finsupp.mem_support_iff, M_finitePart, CRTIdealSupport, Finset.mem_preimage,
    idealPrimeSupport, Multiset.mem_toFinset, idealPrimeExponent]
  exact Multiset.count_ne_zero
private theorem local_continuous (hc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (χ : RayClassCharacter F m)
    (v : HeightOneSpectrum (𝓞 F)) :
    Continuous ((RayClassBridge.ideleClassCharacter F hc m hm χ).comp
      (IdeleGroup.finitePlaceIdeleClass v)) := by
  let lam := (RayClassBridge.ideleClassCharacter F hc m hm χ).comp
      (IdeleGroup.finitePlaceIdeleClass v)
  apply continuous_of_continuousAt_one lam
  have hev : lam =ᶠ[nhds 1] fun _ => (1 : ℂˣ) := by
    filter_upwards [(ClassFieldTheory.isOpen_rayLocalHigherUnitGroup v
      ((RayClassBridge.narrowIdealModulus F m hm).finitePart v)).mem_nhds
        (ClassFieldTheory.rayLocalHigherUnitGroup v _).one_mem] with u hu
    exact RayClassBridge.ideleClassCharacter_finitePlaceIdeleClass_higherUnit F hc m hm χ v u hu
  exact continuousAt_const.congr hev.symm

theorem primitive_iff_local_isLeast (hc : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥) (χ : RayClassCharacter F m) :
    χ.IsPrimitive ↔
      ∀ v : HeightOneSpectrum (𝓞 F),
        IsLeast {k : ℕ | ∀ t : (v.adicCompletion F)ˣ,
          t ∈ ClassFieldTheory.rayLocalHigherUnitGroup v k →
            RayClassBridge.ideleClassCharacter F hc m hm χ
              (IdeleGroup.finitePlaceIdeleClass v t) = 1}
          ((RayClassBridge.narrowIdealModulus F m hm).finitePart v) := by
  constructor
  · intro hprim
    let H := kernelConductor hc m hm χ
    let f := modulusIdeal H.narrowFiniteConductor
    have hf0 : f ≠ ⊥ := modulusIdeal_ne_bot _
    have hmf : m ≤ f := kernel_bound hc m hm χ
    have hdef := kernel_defining hc m hm χ
    change (ClassFieldTheory.GlobalClassFieldComparison.rayClassModulusToOriginal F
      (M F f hf0)).congruenceSubgroup ≤ _ at hdef
    rw [M_eq_narrow hc f hf0] at hdef
    obtain ⟨ρ, ρ₀, χf, _, _, _, hχf⟩ := rayDescent hc
      (RayClassBridge.ideleClassCharacter F hc m hm χ) f hf0 hdef
    have heq : f = m := by
      by_contra hne
      have hlt : m < f := lt_of_le_of_ne hmf (Ne.symm hne)
      obtain ⟨α, hα, hcong, hpos, hcop, hval⟩ := hprim f hlt
      have hI : Ideal.span {α} ≠ ⊥ := by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using hα
      have hcopf : Ideal.span {α} ⊔ f = ⊤ := top_unique (hcop ▸ sup_le_sup_left hmf _)
      have h1 := RayClassBridge.ideleClassCharacter_idealIdele F hc m hm χ _ hI hcop
      have h2 := RayClassBridge.ideleClassCharacter_idealIdele F hc f hf0 χf _ hI hcopf
      rw [hχf] at h2
      apply hval
      rw [← h1, h2]
      exact χf.map_span' α hα hcong hpos
    have hexp : H.narrowFiniteConductor = (RayClassBridge.narrowIdealModulus F m hm).finitePart := by
      rw [← modulusIdeal_M H.narrowFiniteConductor]
      change (M F f hf0).finitePart = _
      simp only [heq]
      rfl
    intro v
    constructor
    · intro u hu
      apply localTrivial hc m hm χ v u
      simpa only [← hexp] using hu
    · intro k hk
      have hle : RayClass.localHigherUnitClassSubgroup v k ≤ H.1 := by
        rintro _ ⟨u, hu, rfl⟩
        change RayClassBridge.ideleClassCharacter F hc m hm χ (IdeleGroup.finitePlaceIdeleClass v u) = 1
        apply hk u
        rwa [ClassFieldTheory.rayLocalHigherUnitGroup_eq_rayClass]
      have h := H.narrowFiniteLocalConductorExponent_le v hle
      rw [← H.narrowFiniteConductor_apply_eq_narrowFiniteLocalConductorExponent, hexp] at h
      exact h
  · intro hleast
    let lam : (v : ↥(CRTIdealSupport F m)) → (v.val.adicCompletion F)ˣ →* ℂˣ :=
      fun v => (RayClassBridge.ideleClassCharacter F hc m hm χ).comp
        (IdeleGroup.finitePlaceIdeleClass v.val)
    apply primitive_of_exact_local_exponents F hc m hm χ lam
    · intro v; exact local_continuous hc m hm χ v.val
    · intro v u hu
      apply (hleast v.val).1 u
      have he : idealPrimeExponent v.val.asIdeal m =
          (RayClassBridge.narrowIdealModulus F m hm).finitePart v.val := (M_finitePart F m hm v.val).symm
      exact (CRT_iff _ _ _).mp (he ▸ hu)
    · intro v k hk
      by_contra hn
      push Not at hn
      have h := (hleast v.val).2 (show k ∈ {k : ℕ | ∀ u,
        u ∈ ClassFieldTheory.rayLocalHigherUnitGroup v.val k →
          RayClassBridge.ideleClassCharacter F hc m hm χ
            (IdeleGroup.finitePlaceIdeleClass v.val u) = 1} from
        fun u hu => hn u ((CRT_iff _ _ _).mpr hu))
      have he : (RayClassBridge.narrowIdealModulus F m hm).finitePart v.val =
        idealPrimeExponent v.val.asIdeal m := M_finitePart F m hm v.val
      rw [he] at h
      omega
    · intro α hα hcop
      rw [principal_formula hc m hm χ α hα hcop, support_eq m hm]
      congr 2
      exact (Finset.prod_attach (CRTIdealSupport F m) _).symm

end DedekindZetaZeroFree.PrimitiveRay

end
