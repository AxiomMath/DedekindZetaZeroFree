module

public import DedekindZetaZeroFree.Metaplectic.Torus.UnramifiedCharacterExtensions
public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTensorRealizations

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.EisensteinReferenceSections.FrozenAdjustment
open ProductPolarization
open ProductPolarization.FiniteAdjustmentSupport
variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)
local notation "ζ" => A.zeta12
local notation "hζ" => A.primitive_zeta12
open _root_.DedekindZetaZeroFree.ProductPolarization.FiniteAdjustmentSupport renaming local_discrete → local_discrete
open _root_.DedekindZetaZeroFree.ProductPolarization.FiniteAdjustmentSupport renaming local_finite → local_finite
open _root_.DedekindZetaZeroFree.ProductPolarization.FiniteAdjustmentSupport renaming trivialAdjustment → trivialAdjustment
open _root_.DedekindZetaZeroFree.ProductPolarization.FiniteAdjustmentSupport renaming rawProjection_coord → rawProjection_coord
open _root_.DedekindZetaZeroFree.ProductPolarization.FiniteAdjustmentSupport renaming pD_one_center → pD_one_center
open _root_.DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter renaming toRawData → toRawData
open _root_.DedekindZetaZeroFree.KPGlobalProductPolarizationCharacter renaming fromRawAdjustment → fromRawAdjustment

private theorem adjustment_product_frozen (P : CompatibleLocalData F ζ hζ)
    (ψ : ((q : A.Sf) → (P.localData (Sum.inr q.val)).L) →* ℂˣ) :
    ∃ T : FiniteAdjustment F ζ hζ P, T.S = A.Sf ∧
      ∀ x : rawB F ζ hζ P,
        rawProduct F ζ hζ P T x =
          rawProduct F ζ hζ P (trivialAdjustment F ζ hζ P) x *
            ψ (fun q => ⟨localProjection F ζ hζ (Sum.inr q.val)
              (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
                (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩) := by
  let S := A.Sf
  let chi (v : KPHilbert.Place F) : (P.localData v).L →* ℂˣ :=
    match v with
    | Sum.inl _ => 1
    | Sum.inr q => if h : q ∈ S then
        ψ.comp (MonoidHom.mulSingle (fun q : S => (P.localData (Sum.inr q.val)).L) ⟨q, h⟩)
      else 1
  letI : ∀ v, DiscreteTopology (LocalD F v) := local_discrete F
  let T : FiniteAdjustment F ζ hζ P := {
    S := S
    chi := fun v => { toMonoidHom := chi v, continuous_toFun := continuous_of_discreteTopology }
    unitary := by
      intro v x
      letI : Finite (LocalD F v) := local_finite F v
      exact ((Units.coeHom ℂ).comp (chi v) |>.isOfFinOrder
        (isOfFinOrder_of_finite x)).norm_eq_one
    complex_unchanged := by intro w; rfl
    outside_unchanged := by intro q hq; ext x; change (chi (Sum.inr q) x : ℂ) = 1; simp [chi, hq] }
  refine ⟨T, rfl, ?_⟩
  intro x
  let c (v : KPHilbert.Place F) := T.chi v
    ⟨localProjection F ζ hζ v (rawCoordinate F ζ hζ P x v).val,
      (rawCoordinate F ζ hζ P x v).property⟩
  have hc : Function.mulSupport c ⊆ (S.image Sum.inr : Finset (KPHilbert.Place F)) := by
    intro v hv
    cases v with
    | inl w => exact (hv rfl).elim
    | inr q =>
      have hq : q ∈ S := by
        by_contra hq
        exact hv (by change chi (Sum.inr q) _ = 1; simp [chi, hq])
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hcf : Function.HasFiniteMulSupport c := (S.image Sum.inr).finite_toSet.subset hc
  have hprod : (∏ᶠ v, c v) = ψ (fun q =>
      ⟨localProjection F ζ hζ (Sum.inr q.val)
        (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
          (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩) := by
    rw [finprod_eq_prod_of_mulSupport_subset c hc,
      Finset.prod_image (by intro a ha b hb h; exact Sum.inr_injective h)]
    rw [← Finset.prod_coe_sort]
    simp only [c, T, chi, dif_pos (Subtype.property _)]
    change (∏ q : S, ψ (Pi.mulSingle q
      (⟨localProjection F ζ hζ (Sum.inr q.val)
        (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
          (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩ :
            (P.localData (Sum.inr q.val)).L))) = _
    rw [← map_prod, Finset.univ_prod_mulSingle]
  have hi := rawProduct_finiteSupport F ζ hζ P (trivialAdjustment F ζ hζ P) x
  change (∏ᶠ v, (P.localData v).lambda (rawCoordinate F ζ hζ P x v) * c v) = _
  have hi' : Function.HasFiniteMulSupport
      (fun v => (P.localData v).lambda (rawCoordinate F ζ hζ P x v)) := by
    simpa [adjustedLocalValue, trivialAdjustment] using hi
  rw [finprod_mul_distrib hi' hcf, hprod]
  congr 1
  simp [rawProduct, adjustedLocalValue, trivialAdjustment]

theorem exists_adjustment
    (hCl : Subsingleton (ClassGroup A.R))
    (P₀ : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
    (hP : ∀ q ∉ A.Sf, (P₀.localData (Sum.inr q)).L = KPGlobalCubicIdelePairing.U F (Sum.inr q)) :
    ∃ T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P₀,
      T.S = A.Sf ∧ ∀ (b : KPGlobalProductPolarizationCharacter.B F ζ hζ P₀)
      (r : KPGlobalCenterRationalCharacter.R F ζ hζ), b.val = r.val →
      KPGlobalProductPolarizationCharacter.lambdaB F ζ hζ P₀ T b =
        KPGlobalCenterRationalCharacter.lambdaR F ζ hζ r := by
  let P := toRawData F ζ hζ P₀
  let T₀ := trivialAdjustment F ζ hζ P
  let H := KPGlobalCenterRationalCharacter.R F ζ hζ ⊓ B F ζ hζ P
  let b : H →* B F ζ hζ P := Subgroup.inclusion inf_le_right
  let r : H →* KPGlobalCenterRationalCharacter.R F ζ hζ := Subgroup.inclusion inf_le_left
  let δ : H →* ℂˣ :=
    (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ).toMonoidHom.comp r /
      (lambdaB F ζ hζ P T₀).toMonoidHom.comp b
  let S := A.Sf
  let V := (q : S) → (P.localData (Sum.inr q.val)).L
  let f : H →* V := MonoidHom.pi (fun q =>
    { toFun := fun h => ⟨KPGlobalCubicIdelePairing.classComparison F
        (pD F ζ hζ h.val) (Sum.inr q.val), h.property.2 (Sum.inr q.val)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp })
  have hk : f.ker ≤ δ.ker := by
    intro h hh
    have hd : pD F ζ hζ h.val = 1 := by
      apply FrozenTorus.principal_eq_one_of_frozen_coordinates A hCl
      · have hr := h.property.1
        rw [KPGlobalCenterRationalCharacter.R_eq_principal_preimage F ζ hζ] at hr
        exact hr
      · intro q hq
        exact congrArg Subtype.val (congrFun (show f h = 1 from hh) ⟨q,hq⟩)
      · intro q hq
        rw [← hP q hq]
        exact h.property.2 (Sum.inr q)
    have hz := pD_one_center F ζ hζ h.val hd
    let z : KPGlobalCenterRationalCharacter.Z F ζ hζ := ⟨h.val, hz⟩
    have hb : lambdaB F ζ hζ P T₀ (b h) = KPGlobalCenterRationalCharacter.omegaA F ζ hζ z := by
      apply (product_character_values F ζ hζ P T₀
        (lambdaValue F ζ hζ P T₀) (lambdaValue_raw_formula F ζ hζ P T₀)).1 (b h) z rfl
    have hr : KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (r h) =
        KPGlobalCenterRationalCharacter.omegaA F ζ hζ z :=
      KPGlobalCenterRationalCharacter.lambdaR_formula F ζ hζ (r h) 1 z (by simp [z, r])
    change KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (r h) / lambdaB F ζ hζ P T₀ (b h) = 1
    rw [hr, hb, div_self']
  let d : f.range →* ℂˣ := f.rangeRestrict.liftOfSurjective
    f.rangeRestrict_surjective ⟨δ, by simpa using hk⟩
  letI : ∀ v, Finite (LocalD F v) := local_finite F
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective ℂ f.range d
  have hψf (h : H) : ψ (f h) = δ h := by
    change ψ (f.rangeRestrict h).val = δ h
    have hh := DFunLike.congr_fun hψ (f.rangeRestrict h)
    change ψ (f.rangeRestrict h).val = d (f.rangeRestrict h) at hh
    rw [hh]
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  obtain ⟨T, hTS, hT⟩ := adjustment_product_frozen A P ψ
  have hraw : ∀ (x : rawB F ζ hζ P) (rr : KPGlobalCenterRationalCharacter.R F ζ hζ),
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ x.val) = rr.val.val →
      rawProduct F ζ hζ P T x = KPGlobalCenterRationalCharacter.lambdaR F ζ hζ rr := by
    intro x rr hx
    let bb := rawProjection F ζ hζ P x
    have he : bb.val = rr.val := Subtype.ext hx
    let h : H := ⟨rr.val, rr.property, he ▸ bb.property⟩
    have hc : (fun q : S =>
        (⟨localProjection F ζ hζ (Sum.inr q.val)
          (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val,
            (rawCoordinate F ζ hζ P x (Sum.inr q.val)).property⟩ :
              (P.localData (Sum.inr q.val)).L)) = f h := by
      funext q
      apply Subtype.ext
      change localProjection F ζ hζ (Sum.inr q.val)
        (rawCoordinate F ζ hζ P x (Sum.inr q.val)).val =
          KPGlobalCubicIdelePairing.classComparison F (pD F ζ hζ h.val) (Sum.inr q.val)
      rw [rawProjection_coord]
      change KPGlobalCubicIdelePairing.classComparison F (pD F ζ hζ bb.val) _ = _
      rw [he]
    rw [hT x, hc, hψf]
    have hi : rawProduct F ζ hζ P T₀ x = lambdaB F ζ hζ P T₀ (b h) := by
      symm
      apply lambdaValue_raw_formula
      exact hx
    change rawProduct F ζ hζ P T₀ x = _ at hi
    rw [hi]
    change lambdaB F ζ hζ P T₀ (b h) *
      (KPGlobalCenterRationalCharacter.lambdaR F ζ hζ (r h) / lambdaB F ζ hζ P T₀ (b h)) = _
    rw [mul_comm, div_mul_cancel]
    rfl
  refine ⟨fromRawAdjustment F ζ hζ P₀ T, hTS, ?_⟩
  intro b r hbr
  obtain ⟨x, hx⟩ := KPGlobalProductPolarizationCharacter.B_has_raw_lift F ζ hζ P₀ b
  rw [KPGlobalProductPolarizationCharacter.lambdaB_raw_formula F ζ hζ P₀ _ b x hx]
  exact hraw x r (hx.trans (congrArg Subtype.val hbr))

theorem exists_model (hCl : Subsingleton (ClassGroup A.R)) :
    ∃ P : KPGlobalTorusFiniteStages.CompatibleModelData F ζ hζ,
      P.adjustment.S = A.Sf ∧ ∀ q ∉ A.Sf,
        KPGlobalProductPolarizationCharacter.IsUnramified F ζ hζ q
          (P.localData.localData (Sum.inr q)) := by
  obtain ⟨P, hP⟩ := FrozenChoices.exists_initial A
  obtain ⟨T, hT, hcompat⟩ := exists_adjustment A hCl P
    (fun q hq => (hP q hq).2.1)
  exact ⟨⟨P, T, hcompat⟩, hT, hP⟩

end DedekindZetaZeroFree.EisensteinReferenceSections.FrozenAdjustment

end
