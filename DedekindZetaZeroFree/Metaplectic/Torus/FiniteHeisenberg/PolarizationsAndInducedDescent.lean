module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteHeisenberg.StagePairing
public import DedekindZetaZeroFree.Metaplectic.Torus.SmoothPeriodizationAndAveraging

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.TorusFinitePolarizations
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open KPGlobalTorusFiniteStages TorusFiniteCenterQuotient

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (C : CompatibleModelData F ζ hζ) (L : Level F ζ hζ C)

local instance : Fintype (symplecticQuotient F ζ hζ C L) :=
  @Fintype.ofFinite _ (quotient_finite F ζ hζ C L)

private theorem root_four (ε : rootsOfUnity 3 F) : ε ^ 4 = ε := by
  have hp : ε ^ 3 = 1 := by apply Subtype.ext; exact ε.property
  rw [pow_succ, hp, one_mul]
private theorem maximal_transfer
    (T : FinitePolarization.HeisenbergData (H F ζ hζ C L) (symplecticQuotient F ζ hζ C L))
    (hp : ∀ x y, T.pairing x y = ordinaryRoots F ζ hζ (stagePairing F ζ hζ C L x y ^ 4))
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hA : KPGlobalProductPolarizationCharacter.IsMaximalIsotropic F (stagePairing F ζ hζ C L) A) :
    FinitePolarization.IsMaximalIsotropic T.pairing A := by
  have he (x y) : T.pairing x y = 1 ↔ stagePairing F ζ hζ C L x y = 1 := by
    rw [hp, root_four]
    constructor
    · intro hh; apply ordinaryRoots_injective F ζ hζ; simpa using hh
    · intro hh; rw [hh, map_one]
  exact ⟨fun x hx y hy => (he x y).mpr (hA.1 x hx y hy),
    fun N hN hi => hA.2 N hN (fun x hx y hy => (he x y).mp (hi x hx y hy))⟩

private theorem projection_mk (x : stageDomain F ζ hζ C L) :
    projection F ζ hζ C L (QuotientGroup.mk x) = domainProjection F ζ hζ C L x := rfl

private theorem rational_factor (x : stageDomain F ζ hζ C L)
    (hx : domainProjection F ζ hζ C L x ∈ rationalPolarization F ζ hζ C L) :
    ∃ (r : (R F ζ hζ).comap (stageDomain F ζ hζ C L).subtype)
      (k : phaseGroup F ζ hζ C L), x = r.val * phaseElement F ζ hζ C L k := by
  obtain ⟨a, ha, he⟩ := Subgroup.mem_map.mp hx
  obtain ⟨t, ht⟩ := KPGlobalTorusFiniteStagesCofinality.finiteTorusClassProjection_surjective F ζ hζ a.val
  have ht' : pD F ζ hζ t.val = a.val := ht
  have hr : t.val ∈ R F ζ hζ := by
    change t.val ∈ KPGlobalCenterRationalCharacter.R F ζ hζ
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage]
    change pD F ζ hζ t.val ∈ A F
    rw [ht']; exact ha.1
  let r : (R F ζ hζ).comap (stageDomain F ζ hζ C L).subtype :=
    ⟨⟨t.val, by change pD F ζ hζ t.val ∈ annihilator F ζ hζ L.K; rw [ht']; exact a.property⟩, hr⟩
  have hk : pD F ζ hζ (r.val⁻¹ * x).val ∈ L.K := by
    have hh : QuotientGroup.mk a = QuotientGroup.mk (⟨pD F ζ hζ x.val, x.property⟩ : annihilator F ζ hζ L.K) := he
    have hh' := QuotientGroup.eq.mp hh
    change a.val⁻¹ * pD F ζ hζ x.val ∈ L.K at hh'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
    change (pD F ζ hζ t.val)⁻¹ * pD F ζ hζ x.val ∈ L.K
    rwa [ht']
  exact ⟨r, ⟨(r.val⁻¹ * x).val, hk⟩, by apply Subtype.ext; simp [phaseElement, r]⟩

private theorem product_mem (x : stageDomain F ζ hζ C L) :
    domainProjection F ζ hζ C L x ∈ productPolarization F ζ hζ C L ↔ x.val ∈ B F ζ hζ C := by
  constructor
  · intro hx
    obtain ⟨m, hm, he⟩ := Subgroup.mem_map.mp hx
    have hh : QuotientGroup.mk m = QuotientGroup.mk (⟨pD F ζ hζ x.val, x.property⟩ : annihilator F ζ hζ L.K) := he
    have hk' := QuotientGroup.eq.mp hh
    have hk : m.val⁻¹ * pD F ζ hζ x.val ∈ L.K := hk'
    change pD F ζ hζ x.val ∈ M F ζ hζ C
    have hh' := (M F ζ hζ C).mul_mem hm (L.inside hk)
    simpa only [Subgroup.subtype_apply, mul_inv_cancel_left] using hh'
  · intro hx
    exact Subgroup.mem_map.mpr ⟨⟨pD F ζ hζ x.val, x.property⟩, hx, rfl⟩

 abbrev QR (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :=
  Q.H.comap (stageDomain F ζ hζ C L).subtype
 abbrev qChar (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) : QR F ζ hζ C L Q →* ℂˣ :=
  Q.character.toMonoidHom.comp ((stageDomain F ζ hζ C L).subtype.restrict (fun _ hx => hx))

private theorem qchar_phase (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ C)
    (u : QR F ζ hζ C L Q) (k : phaseGroup F ζ hζ C L)
    (he : u.val = phaseElement F ζ hζ C L k) :
    qChar F ζ hζ C L Q u = phaseCharacter F ζ hζ C L k := by
  rcases hQ with rfl | rfl
  · exact (compatibleAdjustment_agrees F ζ hζ C
      ⟨k.val, phase_inside_product F ζ hζ C L k.property⟩
      ⟨u.val.val, u.property⟩ (congrArg Subtype.val he).symm).symm
  · apply congrArg (productUnitCharacter F ζ hζ C C.adjustment)
    apply Subtype.ext
    change u.val.val = k.val
    exact congrArg Subtype.val he

 theorem q_project (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L))
    (u : QR F ζ hζ C L Q) : domainProjection F ζ hζ C L u.val ∈ A := by
  rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨⟨pD F ζ hζ u.val.val, u.val.property⟩,
      ⟨by
        have hu := u.property
        change u.val.val ∈ KPGlobalCenterRationalCharacter.R F ζ hζ at hu
        rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage] at hu
        exact hu, u.val.property⟩, rfl⟩
  · exact (product_mem F ζ hζ C L u.val).mpr u.property

private theorem q_factor (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L))
    (x : stageDomain F ζ hζ C L) (hx : domainProjection F ζ hζ C L x ∈ A) :
    ∃ (u : QR F ζ hζ C L Q) (k : phaseGroup F ζ hζ C L),
      x = u.val * phaseElement F ζ hζ C L k := by
  rcases hQ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rational_factor F ζ hζ C L x hx
  · exact ⟨⟨x, (product_mem F ζ hζ C L x).mp hx⟩, 1, by simp [phaseElement]⟩

private theorem phase_kernel_char (x : stageDomain F ζ hζ C L)
    (hx : x ∈ phaseKernel F ζ hζ C L) :
    ∃ k : phaseGroup F ζ hζ C L, x = phaseElement F ζ hζ C L k ∧
      phaseCharacter F ζ hζ C L k = 1 := by
  obtain ⟨k, hk, he⟩ := hx
  exact ⟨k, he.symm, hk⟩

 def combined (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    QR F ζ hζ C L Q × phaseGroup F ζ hζ C L →* stageDomain F ζ hζ C L :=
  (QR F ζ hζ C L Q).subtype.noncommCoprod (phaseInclusion F ζ hζ C L)
    (fun u k => (phaseInclusion_central F ζ hζ C L k u.val).symm)

 def combinedChar (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ) :
    QR F ζ hζ C L Q × phaseGroup F ζ hζ C L →* ℂˣ :=
  (qChar F ζ hζ C L Q).noncommCoprod (phaseCharacter F ζ hζ C L) (fun _ _ => Commute.all _ _)

 theorem combined_kernel (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : Q = rationalModel F ζ hζ ∨ Q = productModel F ζ hζ C)
    (v : QR F ζ hζ C L Q × phaseGroup F ζ hζ C L)
    (hv : combined F ζ hζ C L Q v ∈ phaseKernel F ζ hζ C L) :
    combinedChar F ζ hζ C L Q v = 1 := by
  obtain ⟨k, hk, hχ⟩ := phase_kernel_char F ζ hζ C L _ hv
  have hu : v.1.val = phaseElement F ζ hζ C L (k * v.2⁻¹) := by
    change v.1.val * phaseElement F ζ hζ C L v.2 = phaseElement F ζ hζ C L k at hk
    apply Subtype.ext
    have hh := congrArg (fun x : stageDomain F ζ hζ C L => x * (phaseElement F ζ hζ C L v.2)⁻¹) hk
    have hh' := congrArg Subtype.val hh
    simpa [phaseElement, mul_assoc] using hh'
  change qChar F ζ hζ C L Q v.1 * phaseCharacter F ζ hζ C L v.2 = 1
  rw [qchar_phase F ζ hζ C L Q hQ _ _ hu, map_mul, map_inv, hχ, one_mul, inv_mul_cancel]

 def combinedQuotient (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L)) :
    QR F ζ hζ C L Q × phaseGroup F ζ hζ C L →* A.comap (projection F ζ hζ C L) :=
  (((QuotientGroup.mk' _).comp (combined F ζ hζ C L Q))).codRestrict _ (by
    intro v
    change domainProjection F ζ hζ C L (v.1.val * phaseElement F ζ hζ C L v.2) ∈ A
    rw [map_mul]
    have hk : domainProjection F ζ hζ C L (phaseElement F ζ hζ C L v.2) = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [domainProjection_kernel]
      exact v.2.property
    rw [hk, mul_one]
    exact q_project F ζ hζ C L Q A hQ v.1)

 theorem combinedQuotient_surj (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L)) :
    Function.Surjective (combinedQuotient F ζ hζ C L Q A hQ) := by
  intro a
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective a.val
  have hxa : domainProjection F ζ hζ C L x ∈ A := by
    rw [← projection_mk, hx]; exact a.property
  obtain ⟨u, k, he⟩ := q_factor F ζ hζ C L Q A hQ x hxa
  exact ⟨(u,k), Subtype.ext (by change QuotientGroup.mk (u.val * phaseElement F ζ hζ C L k) = a.val; rw [← he, hx])⟩

 def descendedChar (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L)) :
    A.comap (projection F ζ hζ C L) →* ℂˣ :=
  (combinedQuotient F ζ hζ C L Q A hQ).liftOfSurjective
    (combinedQuotient_surj F ζ hζ C L Q A hQ) ⟨combinedChar F ζ hζ C L Q, by
      intro v hv
      apply combined_kernel F ζ hζ C L Q (hQ.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1))
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hv)⟩

private theorem descendedChar_formula (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L))
    (v : QR F ζ hζ C L Q × phaseGroup F ζ hζ C L) :
    descendedChar F ζ hζ C L Q A hQ (combinedQuotient F ζ hζ C L Q A hQ v) =
      qChar F ζ hζ C L Q v.1 * phaseCharacter F ζ hζ C L v.2 :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

private theorem char_q (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L))
    (u : QR F ζ hζ C L Q) :
    descendedChar F ζ hζ C L Q A hQ
      ⟨QuotientGroup.mk u.val, q_project F ζ hζ C L Q A hQ u⟩ = qChar F ζ hζ C L Q u := by
  have hh := descendedChar_formula F ζ hζ C L Q A hQ (u,1)
  have he : combinedQuotient F ζ hζ C L Q A hQ (u,1) = ⟨QuotientGroup.mk u.val, q_project F ζ hζ C L Q A hQ u⟩ := by
    apply Subtype.ext
    change QuotientGroup.mk (u.val * phaseElement F ζ hζ C L 1) = QuotientGroup.mk u.val
    have hh : phaseElement F ζ hζ C L (1 : phaseGroup F ζ hζ C L) = 1 := Subtype.ext rfl
    rw [hh, mul_one]
  rw [he, map_one, mul_one] at hh
  exact hh

private theorem char_phase (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L))
    (k : phaseGroup F ζ hζ C L) (hk : projection F ζ hζ C L (QuotientGroup.mk (phaseElement F ζ hζ C L k)) ∈ A) :
    descendedChar F ζ hζ C L Q A hQ ⟨QuotientGroup.mk (phaseElement F ζ hζ C L k), hk⟩ = phaseCharacter F ζ hζ C L k := by
  have hh := descendedChar_formula F ζ hζ C L Q A hQ (1,k)
  have he : combinedQuotient F ζ hζ C L Q A hQ (1,k) = ⟨QuotientGroup.mk (phaseElement F ζ hζ C L k), hk⟩ := by
    apply Subtype.ext
    change QuotientGroup.mk (1 * phaseElement F ζ hζ C L k) = QuotientGroup.mk (phaseElement F ζ hζ C L k)
    rw [one_mul]
  rw [he, map_one, one_mul] at hh
  exact hh

 theorem sections_congr (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : RestrictedSections F ζ hζ C L Q) (x y : stageDomain F ζ hζ C L)
    (hxy : (QuotientGroup.mk x : H F ζ hζ C L) = QuotientGroup.mk y) : f.val x = f.val y := by
  have hk := QuotientGroup.eq.mp hxy
  obtain ⟨k, he, hχ⟩ := phase_kernel_char F ζ hζ C L _ hk
  have hy : y = x * phaseElement F ζ hζ C L k := by rw [← he]; simp
  rw [hy, f.property.2, hχ, Units.val_one, one_mul]

 def sectionLift (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : RestrictedSections F ζ hζ C L Q) : H F ζ hζ C L → ℂ :=
  Quotient.lift f.val (by
    intro x y hxy
    apply sections_congr F ζ hζ C L Q f x y
    exact Quotient.sound hxy)

private theorem sectionLift_mk (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (f : RestrictedSections F ζ hζ C L Q) (x : stageDomain F ζ hζ C L) :
    sectionLift F ζ hζ C L Q f (QuotientGroup.mk x) = f.val x := rfl

 theorem sectionLift_covariance (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L))
    (f : RestrictedSections F ζ hζ C L Q) :
    sectionLift F ζ hζ C L Q f ∈ FinitePolarization.inducedSpace
      (A.comap (projection F ζ hζ C L)) (descendedChar F ζ hζ C L Q A hQ) := by
    intro a g
    obtain ⟨v, rfl⟩ := combinedQuotient_surj F ζ hζ C L Q A hQ a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    change sectionLift F ζ hζ C L Q f (QuotientGroup.mk (v.1.val * phaseElement F ζ hζ C L v.2) * QuotientGroup.mk x) = _
    rw [← QuotientGroup.mk_mul, sectionLift_mk, descendedChar_formula, sectionLift_mk]
    have he : (v.1.val * phaseElement F ζ hζ C L v.2) * x =
        (v.1.val * x) * phaseElement F ζ hζ C L v.2 := by
      have hc : phaseElement F ζ hζ C L v.2 * x = x * phaseElement F ζ hζ C L v.2 := (phaseInclusion_central F ζ hζ C L v.2 x).eq
      rw [mul_assoc, hc, ← mul_assoc]
    rw [he, f.property.2, f.property.1, Units.val_mul]
    change (phaseCharacter F ζ hζ C L v.2 : ℂ) * ((qChar F ζ hζ C L Q v.1 : ℂ) * f.val x) = _
    ring

 def descentMap (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L)) :
    RestrictedSections F ζ hζ C L Q →ₗ[ℂ]
      FinitePolarization.inducedSpace (A.comap (projection F ζ hζ C L)) (descendedChar F ζ hζ C L Q A hQ) where
  toFun f := ⟨sectionLift F ζ hζ C L Q f, sectionLift_covariance F ζ hζ C L Q A hQ f⟩
  map_add' f g := by
    apply Subtype.ext
    funext x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective x
    rfl

 theorem descent_bijective (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L)) :
    Function.Bijective (descentMap F ζ hζ C L Q A hQ) := by
  constructor
  · intro f g he
    apply Subtype.ext
    funext x
    exact congrArg (fun f => f.val (QuotientGroup.mk x)) he
  · intro f
    let g : RestrictedSections F ζ hζ C L Q := ⟨fun x => f.val (QuotientGroup.mk x), by
      constructor
      · intro u x
        change f.val (QuotientGroup.mk (u.val * x)) = _
        rw [QuotientGroup.mk_mul]
        rw [f.property ⟨QuotientGroup.mk u.val, q_project F ζ hζ C L Q A hQ u⟩, char_q]
        rfl
      · intro k x
        have hk : projection F ζ hζ C L (QuotientGroup.mk (phaseElement F ζ hζ C L k)) ∈ A := by
          change domainProjection F ζ hζ C L (phaseElement F ζ hζ C L k) ∈ A
          have hh : domainProjection F ζ hζ C L (phaseElement F ζ hζ C L k) = 1 := by
            apply MonoidHom.mem_ker.mp
            rw [domainProjection_kernel]; exact k.property
          rw [hh]; exact A.one_mem
        have hc : x * phaseElement F ζ hζ C L k = phaseElement F ζ hζ C L k * x := (phaseInclusion_central F ζ hζ C L k x).symm.eq
        change f.val (QuotientGroup.mk (x * phaseElement F ζ hζ C L k)) = _
        rw [hc, QuotientGroup.mk_mul]
        rw [f.property ⟨QuotientGroup.mk (phaseElement F ζ hζ C L k), hk⟩, char_phase]⟩
    refine ⟨g, ?_⟩
    apply Subtype.ext
    funext x
    obtain ⟨x,rfl⟩ := QuotientGroup.mk_surjective x
    rfl

 def descentEquiv (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L)) :=
  LinearEquiv.ofBijective (descentMap F ζ hζ C L Q A hQ) (descent_bijective F ζ hζ C L Q A hQ)

private theorem descended_central (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (A : Subgroup (symplecticQuotient F ζ hζ C L))
    (hQ : (Q = rationalModel F ζ hζ ∧ A = rationalPolarization F ζ hζ C L) ∨
      (Q = productModel F ζ hζ C ∧ A = productPolarization F ζ hζ C L))
    (a : A.comap (projection F ζ hζ C L)) (ha : a.val ∈ center F ζ hζ C L) :
    descendedChar F ζ hζ C L Q A hQ a = centerCharacter F ζ hζ C L ⟨a.val, ha⟩ := by
  obtain ⟨k, hk⟩ := phaseToCenter_surjective F ζ hζ C L ⟨a.val, ha⟩
  have hv : QuotientGroup.mk (phaseElement F ζ hζ C L k) = a.val := congrArg Subtype.val hk
  have hm : projection F ζ hζ C L (QuotientGroup.mk (phaseElement F ζ hζ C L k)) ∈ A := hv.symm ▸ a.property
  have he : a = ⟨QuotientGroup.mk (phaseElement F ζ hζ C L k), hm⟩ := Subtype.ext hv.symm
  calc
    _ = descendedChar F ζ hζ C L Q A hQ ⟨QuotientGroup.mk (phaseElement F ζ hζ C L k), hm⟩ := congrArg _ he
    _ = phaseCharacter F ζ hζ C L k := char_phase F ζ hζ C L Q A hQ k hm
    _ = _ := (centerCharacter_phase F ζ hζ C L k).symm.trans (congrArg _ hk)

private theorem descended_agree (a : H F ζ hζ C L)
    (ha : projection F ζ hζ C L a ∈ rationalPolarization F ζ hζ C L)
    (hb : projection F ζ hζ C L a ∈ productPolarization F ζ hζ C L) :
    descendedChar F ζ hζ C L (rationalModel F ζ hζ) (rationalPolarization F ζ hζ C L) (Or.inl ⟨rfl,rfl⟩) ⟨a,ha⟩ =
    descendedChar F ζ hζ C L (productModel F ζ hζ C) (productPolarization F ζ hζ C L) (Or.inr ⟨rfl,rfl⟩) ⟨a,hb⟩ := by
  obtain ⟨v,hv⟩ := combinedQuotient_surj F ζ hζ C L (rationalModel F ζ hζ) (rationalPolarization F ζ hζ C L) (Or.inl ⟨rfl,rfl⟩) ⟨a,ha⟩
  have hx : QuotientGroup.mk (v.1.val * phaseElement F ζ hζ C L v.2) = a := congrArg Subtype.val hv
  have hxb : (v.1.val * phaseElement F ζ hζ C L v.2).val ∈ B F ζ hζ C := by
    apply (product_mem F ζ hζ C L _).mp
    rw [← projection_mk, hx]; exact hb
  have hub : v.1.val.val ∈ B F ζ hζ C := by
    have hh := (B F ζ hζ C).mul_mem hxb ((B F ζ hζ C).inv_mem (phase_inside_product F ζ hζ C L v.2.property))
    simpa only [Subgroup.coe_mul, phaseElement, mul_inv_cancel_right] using hh
  let uB : QR F ζ hζ C L (productModel F ζ hζ C) := ⟨v.1.val, hub⟩
  have hp : combinedQuotient F ζ hζ C L (productModel F ζ hζ C) (productPolarization F ζ hζ C L) (Or.inr ⟨rfl,rfl⟩) (uB,v.2) = ⟨a,hb⟩ := Subtype.ext hx
  rw [← hv, descendedChar_formula, ← hp, descendedChar_formula]
  have he : qChar F ζ hζ C L (rationalModel F ζ hζ) v.1 = qChar F ζ hζ C L (productModel F ζ hζ C) uB := by
    exact (compatibleAdjustment_agrees F ζ hζ C ⟨v.1.val.val, hub⟩ ⟨v.1.val.val,v.1.property⟩ rfl).symm
  rw [he]

 abbrev rationalPre : Subgroup (stageDomain F ζ hζ C L) :=
  (R F ζ hζ).comap (stageDomain F ζ hζ C L).subtype

 abbrev productPre : Subgroup (stageDomain F ζ hζ C L) :=
  (B F ζ hζ C).comap (stageDomain F ζ hζ C L).subtype

private lemma mem_rationalPre {x : stageDomain F ζ hζ C L} :
    x ∈ rationalPre F ζ hζ C L ↔ pD F ζ hζ x.val ∈ A F := by
  constructor
  · intro hx
    have hx' : (stageDomain F ζ hζ C L).subtype x ∈
        KPGlobalCenterRationalCharacter.R F ζ hζ := hx
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage] at hx'
    exact hx'
  · intro hx
    change (stageDomain F ζ hζ C L).subtype x ∈ KPGlobalCenterRationalCharacter.R F ζ hζ
    rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage]
    exact hx

private lemma mem_productPre {x : stageDomain F ζ hζ C L} :
    x ∈ productPre F ζ hζ C L ↔ pD F ζ hζ x.val ∈ M F ζ hζ C := by
  rw [productPre, Subgroup.mem_comap]
  rfl

private lemma mem_phaseInDomain {x : stageDomain F ζ hζ C L} :
    x ∈ phaseInDomain F ζ hζ C L ↔ pD F ζ hζ x.val ∈ L.K :=
  Iff.rfl

private lemma rationalPre_inf_phase_le_ker :
    rationalPre F ζ hζ C L ⊓ phaseInDomain F ζ hζ C L ≤
      ((pD F ζ hζ).ker).comap (stageDomain F ζ hζ C L).subtype := by
  intro x hx
  rw [Subgroup.mem_comap, MonoidHom.mem_ker]
  have h1 : pD F ζ hζ x.val ∈ A F := (mem_rationalPre F ζ hζ C L).mp hx.1
  have h2 : pD F ζ hζ x.val ∈ L.K := (mem_phaseInDomain F ζ hζ C L).mp hx.2
  have h3 : pD F ζ hζ x.val ∈ L.K ⊓ A F := ⟨h2, h1⟩
  rw [L.transverse] at h3
  exact h3

theorem actual_polarizations_descent
    (T : FinitePolarization.HeisenbergData
      (H F ζ hζ C L) (symplecticQuotient F ζ hζ C L))
    (hC : T.C = center F ζ hζ C L)
    (hπ : T.π = projection F ζ hζ C L)
    (hω : ∀ z : T.C, T.ω z = centerCharacter F ζ hζ C L
      ⟨z.val, hC ▸ z.property⟩)
    (hpairing : ∀ x y, T.pairing x y = ordinaryRoots F ζ hζ
      (stagePairing F ζ hζ C L x y ^ 4)) :
    ∃ P : FinitePolarization.PolarizationData T,
      P.L = rationalPolarization F ζ hζ C L ∧
      P.N = productPolarization F ζ hζ C L ∧
      ∃ eR : RestrictedSections F ζ hζ C L (rationalModel F ζ hζ) ≃ₗ[ℂ]
        FinitePolarization.inducedSpace (P.L.comap T.π) P.χL,
      ∃ eB : RestrictedSections F ζ hζ C L (productModel F ζ hζ C) ≃ₗ[ℂ]
        FinitePolarization.inducedSpace (P.N.comap T.π) P.χN,
        (∀ f x, (eR f).val (QuotientGroup.mk x) = f.val x) ∧
        (∀ f x, (eB f).val (QuotientGroup.mk x) = f.val x) := by
  rcases T with ⟨Z, hZ, π, hsur, hker, hexp, ω, hfaith, pairing, halt, hperfect, hcomm, hcommχ⟩
  dsimp only at hC hπ hω hpairing ⊢
  subst π
  subst Z
  let TR : FinitePolarization.HeisenbergData (H F ζ hζ C L) (symplecticQuotient F ζ hζ C L) :=
    ⟨center F ζ hζ C L, hZ, projection F ζ hζ C L, hsur, hker, hexp, ω, hfaith, pairing, halt, hperfect, hcomm, hcommχ⟩
  let P : FinitePolarization.PolarizationData TR :=
    { L := rationalPolarization F ζ hζ C L
      N := productPolarization F ζ hζ C L
      maximal_L := maximal_transfer F ζ hζ C L TR hpairing _ (rational_maximal_isotropic F ζ hζ C L)
      maximal_N := maximal_transfer F ζ hζ C L TR hpairing _ (product_maximal_isotropic F ζ hζ C L)
      χL := descendedChar F ζ hζ C L (rationalModel F ζ hζ) (rationalPolarization F ζ hζ C L) (Or.inl ⟨rfl,rfl⟩)
      χN := descendedChar F ζ hζ C L (productModel F ζ hζ C) (productPolarization F ζ hζ C L) (Or.inr ⟨rfl,rfl⟩)
      central_L := by
        intro a ha
        exact (descended_central F ζ hζ C L _ _ (Or.inl ⟨rfl,rfl⟩) a ha).trans (hω ⟨a.val,ha⟩).symm
      central_N := by
        intro a ha
        exact (descended_central F ζ hζ C L _ _ (Or.inr ⟨rfl,rfl⟩) a ha).trans (hω ⟨a.val,ha⟩).symm
      agree_on_intersection := descended_agree F ζ hζ C L }
  refine ⟨P, rfl, rfl,
    descentEquiv F ζ hζ C L (rationalModel F ζ hζ) (rationalPolarization F ζ hζ C L) (Or.inl ⟨rfl,rfl⟩),
    descentEquiv F ζ hζ C L (productModel F ζ hζ C) (productPolarization F ζ hζ C L) (Or.inr ⟨rfl,rfl⟩), ?_, ?_⟩
  · intro f x; rfl
  · intro f x; rfl

end
end DedekindZetaZeroFree.TorusFinitePolarizations
