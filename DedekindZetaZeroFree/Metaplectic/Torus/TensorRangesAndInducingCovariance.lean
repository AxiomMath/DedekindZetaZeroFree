module

public import DedekindZetaZeroFree.Metaplectic.Torus.CompactTailSupportAndFactorization

@[expose] public section

section
open scoped Classical

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

theorem finite_joint_covariant_function_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    {H D : I → Type*}
    [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    [∀ i, IsTopologicalGroup (H i)] [∀ i, CommGroup (D i)] [∀ i, Finite (D i)]
    (U : ∀ i, KPLocalStoneVonNeumann.LocalHeisenbergData (H i) (D i))
    (A : ∀ i, KPLocalStoneVonNeumann.Polarization (U i))
    (G : (∀ i, H i) → ℂ)
    (hG : ∀ (i : I) (b : (A i).L.comap (U i).π) (t : ∀ j, H j),
      G (Function.update t i (b.val * t i)) = ((A i).ωL b : ℂ) * G t) :
    ∃ (n : ℕ) (c : Fin n → ℂ)
      (f : ∀ j : Fin n, ∀ i, KPLocalStoneVonNeumann.InducedModule (A i)),
      ∀ t : ∀ i, H i, G t = ∑ j : Fin n, c j * ∏ i, (f j i).val (t i) := by
  classical
  let B : ∀ i, Subgroup (H i) := fun i => (A i).L.comap (U i).π
  letI (i : I) : (B i).Normal := inferInstance
  letI (i : I) : (B i).FiniteIndex := inferInstance
  let Q := fun i => H i ⧸ B i
  letI (i : I) : Fintype (Q i) := Fintype.ofFinite _
  let q (i : I) : H i →* Q i := QuotientGroup.mk' (B i)
  let r (i : I) : Q i → H i := Function.surjInv (QuotientGroup.mk'_surjective (B i))
  have hr (i : I) (d : Q i) : q i (r i d) = d :=
    Function.surjInv_eq (QuotientGroup.mk'_surjective (B i)) d
  let a (i : I) (x : H i) : B i := ⟨x * (r i (q i x))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change q i (x * (r i (q i x))⁻¹) = 1
    rw [map_mul, map_inv, hr, mul_inv_cancel]⟩
  have ha (i : I) (b : B i) (x : H i) : a i ((b : H i) * x) = b * a i x := by
    apply Subtype.ext
    have hb : q i (b : H i) = 1 := (QuotientGroup.eq_one_iff _).mpr b.property
    simp [a, map_mul, hb, mul_assoc]
  let f (d : ∀ i, Q i) (i : I) : KPLocalStoneVonNeumann.InducedModule (A i) :=
    ⟨fun x => ((A i).ωL (a i x) : ℂ) * (if q i x = d i then 1 else 0), by
      intro b x
      have hb : q i (b : H i) = 1 := (QuotientGroup.eq_one_iff _).mpr b.property
      simp [ha, map_mul, hb, mul_assoc]⟩
  have hcov (b : ∀ i, B i) (t : ∀ i, H i) :
      G (fun i => (b i : H i) * t i) = (∏ i, ((A i).ωL (b i) : ℂ)) * G t := by
    have aux (s : Finset I) :
        G (fun i => if i ∈ s then (b i : H i) * t i else t i) =
          (∏ i ∈ s, ((A i).ωL (b i) : ℂ)) * G t := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        have he : (fun j => if j ∈ insert i s then (b j : H j) * t j else t j) =
            Function.update (fun j => if j ∈ s then (b j : H j) * t j else t j)
              i ((b i : H i) * (if i ∈ s then (b i : H i) * t i else t i)) := by
          funext j
          by_cases hj : j = i
          · subst j; simp [hi]
          · simp [Function.update_of_ne hj, hj]
        rw [he, hG, ih, Finset.prod_insert hi, mul_assoc]
    simpa using aux Finset.univ
  have htransport (t : ∀ i, H i) :
      G t = (∏ i, ((A i).ωL (a i (t i)) : ℂ)) * G (fun i => r i (q i (t i))) := by
    have he : (fun i => (a i (t i) : H i) * r i (q i (t i))) = t := by
      funext i
      simp [a]
    simpa [he] using hcov (fun i => a i (t i)) (fun i => r i (q i (t i)))
  let e : Fin (Fintype.card (∀ i, Q i)) ≃ (∀ i, Q i) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (∀ i, Q i), (fun j => G (fun i => r i (e j i))),
    (fun j i => f (e j) i), ?_⟩
  intro t
  rw [Fintype.sum_equiv e _ (fun d => G (fun i => r i (d i)) * ∏ i, (f d i).val (t i))
    (fun _ => rfl)]
  have hf (d : ∀ i, Q i) : (∏ i, (f d i).val (t i)) =
      if (fun i => q i (t i)) = d then ∏ i, ((A i).ωL (a i (t i)) : ℂ) else 0 := by
    simp only [f, Finset.prod_mul_distrib]
    rw [Fintype.prod_ite_zero]
    by_cases h : (fun i => q i (t i)) = d
    · have hh : ∀ i, q i (t i) = d i := fun i => congrFun h i
      simp [h, hh]
    · have hn : ¬ ∀ i, q i (t i) = d i := fun hh => h (funext hh)
      simp [h, hn]
  simp_rw [hf]
  rw [Finset.sum_eq_single (fun i => q i (t i))]
  · simpa [mul_comm] using htransport t
  · intro d hd hne
    simp [Ne.symm hne]
  · simp

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

end

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

open KPGlobalTorusTensorFibers

theorem rawTensorRestriction_finite_expansion
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (n : ℕ) (c : Fin n → ℂ)
    (f : ∀ j : Fin n, ∀ q : S,
      KPLocalStoneVonNeumann.InducedModule (C.polarization q.val))
    (a : RawEvaluationPoint F ζ hζ) :
    rawTensorRestriction F ζ hζ P T C S
      (∑ j : Fin n, c j • PiTensorProduct.tprod ℂ (f j)) a =
      ((∑ j : Fin n, c j * ∏ q : S, (f j q).val (a.t q.val)) /
        ∏ q : S, (Real.rpow
          (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
            ((C.canonical q.val).borel.coordinate (a.t q.val)))
          (1 / 6 : ℝ) : ℂ)) *
      (∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (a.t q)) := by
  classical
  have hpure : ∀ j : Fin n,
      rawTensorRestriction F ζ hζ P T C S
        (PiTensorProduct.tprod ℂ (f j)) a =
      (∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (a.t q)) *
        ∏ q : S, ((f j q).val (a.t q.val) /
          (Real.rpow
            (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
              ((C.canonical q.val).borel.coordinate (a.t q.val)))
            (1 / 6 : ℝ) : ℂ)) := by
    intro j
    simp only [rawTensorRestriction, LinearMap.coe_mk, AddHom.coe_mk,
      rawFiniteTensorFunctional, PiTensorProduct.lift.tprod,
      MultilinearMap.smul_apply, MultilinearMap.compLinearMap_apply,
      MultilinearMap.mkPiAlgebra_apply, rawEvaluationLinear, LinearMap.coe_mk,
      AddHom.coe_mk, smul_eq_mul]
    congr 1
    apply Finset.prod_congr rfl
    intro q _
    rw [C.evaluation_formula]
  have hlin : rawTensorRestriction F ζ hζ P T C S
      (∑ j : Fin n, c j • PiTensorProduct.tprod ℂ (f j)) a =
      ∑ j : Fin n, c j * rawTensorRestriction F ζ hζ P T C S
        (PiTensorProduct.tprod ℂ (f j)) a := by
    change rawFiniteTensorFunctional F ζ hζ P T C S a.t
      (∑ j : Fin n, c j • PiTensorProduct.tprod ℂ (f j)) =
      ∑ j : Fin n, c j * rawFiniteTensorFunctional F ζ hζ P T C S a.t
        (PiTensorProduct.tprod ℂ (f j))
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hlin]
  simp only [hpure]
  simp only [Finset.prod_div_distrib]
  set cst := ∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (a.t q)
  set den := ∏ q : S, (Real.rpow
      (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
        ((C.canonical q.val).borel.coordinate (a.t q.val))) (1 / 6 : ℝ) : ℂ)
  rw [show (∑ j : Fin n, c j * (cst *
        ((∏ q : S, (f j q).val (a.t q.val)) / den))) =
      ∑ j : Fin n, (cst / den) * (c j * ∏ q : S, (f j q).val (a.t q.val)) from
    Finset.sum_congr rfl (fun j _ => by ring)]
  rw [← Finset.mul_sum]
  ring

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

end

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

open KPGlobalTorusTensorFibers

def finiteRawNormFactor (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) : ℂ :=
  ∏ q : S, (Real.rpow
    (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
      ((C.canonical q.val).borel.coordinate (t q))) (1 / 6 : ℝ) : ℂ)

open KPAdelicCoverRestrictedProduct

private theorem raw_images_commute (x y : RestrictedCover F ζ hζ)
    (hc : ∀ v, Commute (KPPGLLocalCover.coverQuotient F ζ hζ v (x v))
      (KPPGLLocalCover.coverQuotient F ζ hζ v (y v))) :
    Commute (scalarQuotient F ζ hζ (amalgamation F ζ hζ x))
      (scalarQuotient F ζ hζ (amalgamation F ζ hζ y)) := by
  obtain ⟨e, _, _, he⟩ := scalar_quotient_commutes_with_amalgamation F ζ hζ
  change _ * _ = _ * _
  apply e.injective
  simp only [map_mul, he]
  have hr : restrictedPGLQuotient F ζ hζ x * restrictedPGLQuotient F ζ hζ y =
      restrictedPGLQuotient F ζ hζ y * restrictedPGLQuotient F ζ hζ x := by
    apply RestrictedProduct.ext
    intro v
    exact (hc v).eq
  exact congrArg (QuotientGroup.mk' (pglM F ζ hζ)) hr

private theorem maximal_mem {G : Type*} [Group G] (H : Subgroup G)
    (hH : KPLocalPolarization.IsMaximalAbelian H) (g : G)
    (hc : ∀ h ∈ H, Commute g h) : g ∈ H := by
  let A := Subgroup.closure ((H : Set G) ∪ {g})
  have hA : H ≤ A := by intro h hh; exact Subgroup.subset_closure (Or.inl hh)
  have hcomm : ((H : Set G) ∪ {g}).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact hH.1 x hx y hy
    · have : y = g := hy; subst y; exact (hc x hx).symm
    · have : x = g := hx; subst x; exact hc y hy
    · have : x = g := hx; have : y = g := hy; subst x; subst y; exact Commute.refl _
  letI := Subgroup.closureCommGroupOfComm hcomm
  have he : A = H := hH.2 A hA (by
    intro x hx y hy
    exact (congrArg Subtype.val (mul_comm (⟨x,hx⟩ : A) ⟨y,hy⟩)))
  rw [← he]
  exact Subgroup.subset_closure (Or.inr rfl)

theorem finite_raw_restored_covariance
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (R : (∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) →
      RawEvaluationPoint F ζ hζ)
    (hR : FiniteRawRepresentatives F ζ hζ S R)
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (q : S)
    (b : (C.polarization q.val).L.comap (C.canonical q.val).heisenberg.π)
    (t : ∀ r : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ r.val) :
    v.val (R (Function.update t q (b.val * t q))).g *
        finiteRawNormFactor F ζ hζ P T C S (Function.update t q (b.val * t q)) =
      ((C.polarization q.val).ωL b : ℂ) *
        (v.val (R t).g * finiteRawNormFactor F ζ hζ P T C S t) := by
  classical
  let t' := Function.update t q (b.val * t q)
  let x : RestrictedCover F ζ hζ := (R t').raw * (R t).raw⁻¹
  let g := (R t').g * (R t).g⁻¹
  have hx : scalarQuotient F ζ hζ (amalgamation F ζ hζ x) = g.val := by
    dsimp [x, g]
    rw [map_mul, map_inv, map_mul, map_inv, (R t').global_lift, (R t).global_lift]
  have hxinf : ∀ w, x (Sum.inl w) = 1 := by
    intro w
    change (R t').raw (Sum.inl w) * ((R t).raw (Sum.inl w))⁻¹ = 1
    rw [(R t').infinite_one, (R t).infinite_one]; simp
  have hxq : KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val) (x (Sum.inr q.val)) = b.val.val := by
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q.val)
      ((R t').raw (Sum.inr q.val) * ((R t).raw (Sum.inr q.val))⁻¹) = _
    rw [map_mul, map_inv, ← (R t').local_lift, ← (R t).local_lift, (hR t').1 q, (hR t).1 q]
    simp [t']
  have hxne : ∀ r, r ≠ q.val → KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr r) (x (Sum.inr r)) = 1 := by
    intro r hr
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr r)
      ((R t').raw (Sum.inr r) * ((R t).raw (Sum.inr r))⁻¹) = _
    by_cases h : r ∈ S
    · let r' : S := ⟨r,h⟩
      have hr' : r' ≠ q := fun hh => hr (congrArg Subtype.val hh)
      rw [map_mul, map_inv, ← (R t').local_lift, ← (R t).local_lift, (hR t').1 r', (hR t).1 r']
      simp [t', Function.update_of_ne hr']
    · rw [(hR t').2 r h, (hR t).2 r h]; simp
  obtain ⟨c, hc, hcb⟩ := Subgroup.mem_map.mp ((C.subgroup_matches q.val) ▸
    (Subgroup.mem_map.mpr ⟨b.val, b.property, rfl⟩))
  let c' : KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q.val)
      (P.localData (Sum.inr q.val)).L := ⟨c,hc⟩
  have hbc : b.val.val = c'.val.val := hcb.symm
  have hgB : g ∈ KPGlobalProductPolarizationCharacter.B F ζ hζ P := by
    apply maximal_mem _ (KPGlobalProductPolarizationCharacter.B_maximal_abelian F ζ hζ P) g
    intro k hk
    obtain ⟨y, hy⟩ := KPGlobalProductPolarizationCharacter.B_has_raw_lift F ζ hζ P ⟨k,hk⟩
    apply Subtype.ext
    change g.val * k.val = k.val * g.val
    rw [← hx, ← hy]
    exact (raw_images_commute F ζ hζ x y.val (by
      intro w
      cases w with
      | inl w => rw [hxinf, map_one]; exact Commute.one_left _
      | inr r =>
        by_cases hr : r = q.val
        · subst r
          obtain ⟨d, hd⟩ := KPGlobalProductPolarizationCharacter.raw_coordinate_mem F ζ hζ P y (Sum.inr q.val)
          rw [hxq, hbc, ← hd]
          exact ((ProductPolarization.local_preimage_abelian F ζ hζ (Sum.inr q.val)
            (P.localData (Sum.inr q.val)).L (P.localData (Sum.inr q.val)).maximal)
              c'.val c'.property d.val d.property).map
                (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q.val)).subtype
        · rw [hxne r hr]; exact Commute.one_left _)).eq
  let h : Q.H := ⟨g, hQ.1.symm ▸ hgB⟩
  let xb : KPGlobalProductPolarizationCharacter.rawB F ζ hζ P := ⟨x, by
    change scalarQuotient F ζ hζ (amalgamation F ζ hζ x) ∈
      (KPGlobalProductPolarizationCharacter.B F ζ hζ P).map (KPGlobalTorusFunctionData.E F ζ hζ).subtype
    rw [hx]
    exact Subgroup.mem_map.mpr ⟨g,hgB,rfl⟩⟩
  let a : ∀ r, (C.polarization r).L.comap (C.canonical r).heisenberg.π :=
    Function.update (fun r => 1) q.val b
  have ha : ∀ r, (a r).val.val = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr r) (x (Sum.inr r)) := by
    intro r
    by_cases hr : r = q.val
    · subst r; simpa [a] using hxq.symm
    · rw [hxne r hr]
      simp [a, Function.update_of_ne hr]
  have hchar := raw_reference_product_character F ζ hζ P T C Q hQ xb h a ha hxinf hx
  have heval1 (r : HeightOneSpectrum (𝓞 F)) : C.evaluation r (C.reference r) 1 = 1 := by
    rw [C.evaluation_formula, C.reference_formula]
    have hp : (C.canonical r).heisenberg.π 1 ∈ (C.polarization r).L := by simp
    rw [dif_pos hp]
    have hone : (⟨1,hp⟩ : (C.polarization r).L.comap (C.canonical r).heisenberg.π) = 1 := rfl
    rw [hone, map_one, map_one]
    have habs : KPGlobalCenterRationalCharacter.localAbs F (Sum.inr r) 1 = 1 := by
      apply NNReal.eq
      change ‖(1 : r.adicCompletion F)‖ = 1
      simp
    simp [habs]
  have hchar' : (Q.character h : ℂ) = ((C.polarization q.val).ωL b : ℂ) /
      (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
        ((C.canonical q.val).borel.coordinate b.val)) (1 / 6 : ℝ) : ℂ) := by
    rw [← hchar, finprod_eq_single _ q.val]
    · simp only [a, Function.update_self]
      rw [C.evaluation_formula, C.reference_formula]
      have hb : (C.canonical q.val).heisenberg.π b.val ∈ (C.polarization q.val).L := b.property
      rw [dif_pos hb]
    · intro r hr
      simp only [a, Function.update_of_ne hr]
      exact heval1 r
  have hval : v.val (R t').g = (Q.character h : ℂ) * v.val (R t).g := by
    have hg : (R t').g = h.val * (R t).g := by dsimp [h,g]; simp
    rw [hg]
    exact v.property h (R t).g
  have hfactor : finiteRawNormFactor F ζ hζ P T C S t' =
      (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
        ((C.canonical q.val).borel.coordinate b.val)) (1 / 6 : ℝ) : ℂ) *
      finiteRawNormFactor F ζ hζ P T C S t := by
    let d : S → ℂ := fun r => (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr r.val)
        ((C.canonical r.val).borel.coordinate (t r))) (1 / 6 : ℝ) : ℂ)
    let z : ℂ := (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
        ((C.canonical q.val).borel.coordinate b.val)) (1 / 6 : ℝ) : ℂ)
    have hf : (fun r : S => (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr r.val)
        ((C.canonical r.val).borel.coordinate (t' r))) (1 / 6 : ℝ) : ℂ)) =
        Function.update d q (z * d q) := by
      funext r
      by_cases hr : r = q
      · subst r
        simp only [t', Function.update_self]
        exact raw_local_denominator_mul F ζ hζ P T C q.val b.val (t q)
      · simp [t', Function.update_of_ne hr, d]
    change (∏ r : S, _) = z * ∏ r : S, d r
    rw [hf, Finset.prod_update_of_mem (Finset.mem_univ q)]
    have hp : (∏ r : S, d r) = d q * ∏ r ∈ Finset.univ \ {q}, d r :=
      Finset.prod_eq_mul_prod_diff_singleton q d (by simp)
    rw [hp]
    ring
  have hd : (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
        ((C.canonical q.val).borel.coordinate b.val)) (1 / 6 : ℝ) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact ne_of_gt (Real.rpow_pos_of_pos
      (by exact_mod_cast (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q.val)
        ((C.canonical q.val).borel.coordinate b.val))) _)
  change v.val (R t').g * finiteRawNormFactor F ζ hζ P T C S t' = _
  rw [hval, hchar', hfactor]
  field_simp
  <;> ring

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

end

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

open KPGlobalTorusTensorFibers

theorem raw_smooth_level_joint_covariant_descent
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hv : v ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q J) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
      (G : (∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) → ℂ),
      (∀ (q : S)
        (b : (C.polarization q.val).L.comap (C.canonical q.val).heisenberg.π)
        (t : ∀ r : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ r.val),
        G (Function.update t q (b.val * t q)) =
          ((C.polarization q.val).ωL b : ℂ) * G t) ∧
      ∀ a : RawEvaluationPoint F ζ hζ,
        v.val a.g =
          (G (fun q : S => a.t q.val) /
            ∏ q : S, (Real.rpow
              (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q.val)
                ((C.canonical q.val).borel.coordinate (a.t q.val)))
              (1 / 6 : ℝ) : ℂ)) *
          (∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (a.t q)) := by
  classical
  obtain ⟨S, hS, htail⟩ := smooth_level_reference_tail_factorization
    F ζ hζ P T C Q hQ J v hv
  obtain ⟨R, hR⟩ := finite_raw_representatives_exist F ζ hζ S
  let G := fun t => v.val (R t).g * finiteRawNormFactor F ζ hζ P T C S t
  refine ⟨S, hS, G, ?_, ?_⟩
  · intro q b t
    exact finite_raw_restored_covariance F ζ hζ P T C Q hQ S R hR v q b t
  · intro a
    have hden : finiteRawNormFactor F ζ hζ P T C S (fun q : S => a.t q.val) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro q _
      apply Complex.ofReal_ne_zero.mpr
      apply ne_of_gt
      exact Real.rpow_pos_of_pos
        (by exact_mod_cast (KPGlobalCenterRationalCharacter.localAbs_pos F (Sum.inr q.val)
          ((C.canonical q.val).borel.coordinate (a.t q.val)))) _
    change v.val a.g =
      ((v.val (R (fun q : S => a.t q.val)).g *
          finiteRawNormFactor F ζ hζ P T C S (fun q : S => a.t q.val)) /
        finiteRawNormFactor F ζ hζ P T C S (fun q : S => a.t q.val)) * _
    rw [mul_div_cancel_right₀ _ hden]
    exact htail R hR a

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

end

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

open KPGlobalTorusTensorFibers

theorem rawTensorRestriction_insert
    (C : RawLocalScalarData F ζ hζ P T)
    (S U : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : C.exceptional ⊆ S) (hSU : S ⊆ U) :
    (rawTensorRestriction F ζ hζ P T C U).comp
      (RestrictedTensorSimple.insert
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q))
        C.reference S U hSU) = rawTensorRestriction F ζ hζ P T C S := by
  classical
  apply PiTensorProduct.ext
  ext f a
  change rawFiniteTensorFunctional F ζ hζ P T C U a.t
      (RestrictedTensorSimple.insert
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q))
        C.reference S U hSU (PiTensorProduct.tprod ℂ f)) =
    rawFiniteTensorFunctional F ζ hζ P T C S a.t (PiTensorProduct.tprod ℂ f)
  rw [RestrictedTensorSimple.insert_pure,
    rawFiniteTensorFunctional_tprod F ζ hζ P T C U (hS.trans hSU)
      _ a.raw a.t a.local_lift,
    rawFiniteTensorFunctional_tprod F ζ hζ P T C S hS
      f a.raw a.t a.local_lift]
  apply finprod_congr
  intro q
  by_cases hqS : q ∈ S
  · simp only [dif_pos hqS, dif_pos (hSU hqS)]
  · by_cases hqU : q ∈ U <;> simp only [dif_neg hqS, hqU, ↓reduceDIte]

theorem rawTensorRestriction_range_mono
    (C : RawLocalScalarData F ζ hζ P T)
    (S U : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : C.exceptional ⊆ S) (hSU : S ⊆ U) :
    (rawTensorRestriction F ζ hζ P T C S).range ≤
      (rawTensorRestriction F ζ hζ P T C U).range := by
  rintro y ⟨x, rfl⟩
  refine ⟨RestrictedTensorSimple.insert
    (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q))
    C.reference S U hSU x, ?_⟩
  exact LinearMap.congr_fun (rawTensorRestriction_insert F ζ hζ P T C S U hS hSU) x

theorem rawTensorRestriction_range_directed
    (C : RawLocalScalarData F ζ hζ P T) :
    Directed (· ≤ ·) (fun S : RestrictedTensorSimple.Level C.exceptional =>
      (rawTensorRestriction F ζ hζ P T C S.val).range) := by
  intro S U
  refine ⟨⟨S.val ∪ U.val, S.property.trans Finset.subset_union_left⟩, ?_, ?_⟩
  · exact rawTensorRestriction_range_mono F ζ hζ P T C S.val _
      S.property Finset.subset_union_left
  · exact rawTensorRestriction_range_mono F ζ hζ P T C U.val _
      U.property Finset.subset_union_right

theorem mem_rawTensorRestriction_iSup_iff
    (C : RawLocalScalarData F ζ hζ P T)
    (v : RawEvaluationPoint F ζ hζ → ℂ) :
    (v ∈ ⨆ S : RestrictedTensorSimple.Level C.exceptional,
      (rawTensorRestriction F ζ hζ P T C S.val).range) ↔
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
      (x : RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S),
      rawTensorRestriction F ζ hζ P T C S x = v := by
  letI : Nonempty (RestrictedTensorSimple.Level C.exceptional) :=
    ⟨⟨C.exceptional, le_rfl⟩⟩
  rw [Submodule.mem_iSup_of_directed _
    (rawTensorRestriction_range_directed F ζ hζ P T C)]
  constructor
  · rintro ⟨S, x, hx⟩
    exact ⟨S.val, S.property, x, hx⟩
  · rintro ⟨S, hS, x, hx⟩
    exact ⟨⟨S, hS⟩, x, hx⟩

theorem raw_smooth_restriction_finite_tensor_of_levels
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hlevel : ∀ (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
      (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q),
      v ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q J →
      (fun a : RawEvaluationPoint F ζ hζ => v.val a.g) ∈
        ⨆ S : RestrictedTensorSimple.Level C.exceptional,
          (rawTensorRestriction F ζ hζ P T C S.val).range)
    (f : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
      (x : RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S),
      rawTensorRestriction F ζ hζ P T C S x = rawSmoothRestriction F ζ hζ Q f := by
  let A : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q →ₗ[ℂ]
      (RawEvaluationPoint F ζ hζ → ℂ) :=
    { toFun := fun v a => v.val a.g
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let W : Submodule ℂ (RawEvaluationPoint F ζ hζ → ℂ) :=
    ⨆ S : RestrictedTensorSimple.Level C.exceptional,
      (rawTensorRestriction F ζ hζ P T C S.val).range
  have hle : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q ≤ W.comap A := by
    apply iSup_le
    intro J v hv
    exact hlevel J v hv
  apply (mem_rawTensorRestriction_iSup_iff F ζ hζ P T C _).mp
  exact hle f.property

theorem raw_smooth_restriction_finite_tensor
    (C : KPGlobalTorusTensorFibers.RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : KPGlobalTorusTensorFibers.IsUnitProductModel F ζ hζ P T Q)
    (f : KPGlobalTorusFunctionData.TorusSmoothUnion F ζ hζ Q) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
      (x : RestrictedTensorSimple.Stage
        (fun q => KPLocalStoneVonNeumann.InducedModule (C.polarization q)) S),
      KPGlobalTorusTensorFibers.rawTensorRestriction F ζ hζ P T C S x =
        KPGlobalTorusTensorFibers.rawSmoothRestriction F ζ hζ Q f := by
  apply raw_smooth_restriction_finite_tensor_of_levels F ζ hζ P T C Q
  intro J v hv
  obtain ⟨S, hS, G, hG, hraw⟩ :=
    raw_smooth_level_joint_covariant_descent F ζ hζ P T C Q hQ J v hv
  obtain ⟨n, c, k, hk⟩ := finite_joint_covariant_function_expansion
    (fun q : S => (C.canonical q.val).heisenberg)
    (fun q : S => C.polarization q.val) G hG
  apply (mem_rawTensorRestriction_iSup_iff F ζ hζ P T C _).mpr
  refine ⟨S, hS, ∑ j : Fin n, c j • PiTensorProduct.tprod ℂ (k j), ?_⟩
  funext a
  rw [rawTensorRestriction_finite_expansion F ζ hζ P T C S n c k a]
  rw [hraw a, hk (fun q : S => a.t q.val)]

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

end
