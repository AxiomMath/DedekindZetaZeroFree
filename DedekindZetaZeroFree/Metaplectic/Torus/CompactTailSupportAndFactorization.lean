module

public import DedekindZetaZeroFree.Metaplectic.Torus.FiniteTupleRepresentatives

@[expose] public section

section
open scoped NumberField Classical ComplexOrder
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

noncomputable section

open scoped commutatorElement
set_option maxRecDepth 4000

variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : KPGlobalProductPolarizationCharacter.CompatibleLocalData F ζ hζ)
variable (T : KPGlobalProductPolarizationCharacter.FiniteAdjustment F ζ hζ P)

open KPGlobalTorusTensorFibers

private theorem raw_polarized_mem
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (b : RawEvaluationPoint F ζ hζ)
    (hb : ∀ q, (C.canonical q).heisenberg.π (b.t q) ∈ (C.polarization q).L) :
    b.g ∈ Q.H := by
  classical
  let B := KPGlobalProductPolarizationCharacter.B F ζ hζ P
  have hc : ∀ x ∈ B, Commute b.g x := by
    intro x hx
    obtain ⟨y, hy⟩ := KPGlobalProductPolarizationCharacter.B_has_raw_lift F ζ hζ P ⟨x, hx⟩
    obtain ⟨e, _, _, he⟩ := KPAdelicCoverRestrictedProduct.scalar_quotient_commutes_with_amalgamation F ζ hζ
    apply Subtype.ext
    apply e.injective
    change e (b.g.val * x.val) = e (x.val * b.g.val)
    rw [← b.global_lift, ← hy]
    simp only [← map_mul, he]
    congr 1
    apply RestrictedProduct.ext
    intro v
    change KPPGLLocalCover.coverQuotient F ζ hζ v (b.raw v * y.val v) =
      KPPGLLocalCover.coverQuotient F ζ hζ v (y.val v * b.raw v)
    rw [map_mul, map_mul]
    cases v with
    | inl w => rw [b.infinite_one, map_one, one_mul, mul_one]
    | inr q =>
      obtain ⟨k, hk⟩ := raw_local_polarization_lift F ζ hζ P T C y q
      rw [← b.local_lift, ← hk]
      exact congrArg Subtype.val (((C.canonical q).heisenberg.detects_commutation (b.t q) k.val).mpr
        ((C.polarization q).maximal.1 _ (hb q) _ k.property)).eq
  let D := Subgroup.closure ((B : Set _) ∪ {b.g})
  have hBD : B ≤ D := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hi : IsMulCommutative D := Subgroup.isMulCommutative_closure (by
    intro x hx y hy _
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact (KPGlobalProductPolarizationCharacter.B_maximal_abelian F ζ hζ P).1 x hx y hy
    · rcases hy with rfl; exact (hc x hx).symm
    · rcases hx with rfl; exact hc y hy
    · rcases hx with rfl; rcases hy with rfl; exact Commute.refl _)
  letI := hi
  have hd : D = B := (KPGlobalProductPolarizationCharacter.B_maximal_abelian F ζ hζ P).2 D hBD
    (fun x hx y hy => setLike_mul_comm hx hy)
  rw [hQ.1]
  change b.g ∈ B
  rw [← hd]
  exact Subgroup.subset_closure (Or.inr rfl)

private theorem raw_character
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (b : RawEvaluationPoint F ζ hζ)
    (hb : ∀ q, (C.canonical q).heisenberg.π (b.t q) ∈ (C.polarization q).L) :
    (Q.character ⟨b.g, raw_polarized_mem F ζ hζ P T C Q hQ b hb⟩ : ℂ) =
      ∏ᶠ q, C.evaluation q (C.reference q) (b.t q) := by
  let h : Q.H := ⟨b.g, raw_polarized_mem F ζ hζ P T C Q hQ b hb⟩
  let x : KPGlobalProductPolarizationCharacter.rawB F ζ hζ P := ⟨b.raw, by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ b.raw) ∈
        (KPGlobalProductPolarizationCharacter.B F ζ hζ P).map (KPGlobalTorusFunctionData.E F ζ hζ).subtype
    rw [b.global_lift]
    exact Subgroup.mem_map.mpr ⟨b.g, hQ.1 ▸ h.property, rfl⟩⟩
  exact (raw_reference_product_character F ζ hζ P T C Q hQ x h
    (fun q => ⟨b.t q, hb q⟩) b.local_lift b.infinite_one b.global_lift).symm

theorem raw_scalar_support_zero_of_compact_tail_invariance
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hinv : ∀ b : RawEvaluationPoint F ζ hζ,
      (∀ r ∈ S, (b.t r).val = 1) →
      (∀ r, r ∉ S → (b.t r).val ∈
        KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr r)) →
      ∀ g : KPGlobalTorusFunctionData.E F ζ hζ,
        v.val (g * b.g) = v.val g)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ S)
    (hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q)
    (a : RawEvaluationPoint F ζ hζ)
    (hpol : (C.canonical q).heisenberg.π (a.t q) ∉ (C.polarization q).L) :
    v.val a.g = 0 := by
  classical
  have hqe : q ∉ C.exceptional := fun h => hq (hS h)
  have hnc : ¬ ∀ j : KPLocalGoodSphericalImage.compactTorus
      (C.canonical q).borel (C.canonical q).iwasawa, Commute (a.t q) j.val := by
    intro hc
    apply hpol
    rw [← FinitePolarization.orthogonal_eq_of_isMaximalIsotropic
      (C.canonical q).heisenberg.pairing (C.canonical q).heisenberg.alternating
      (C.polarization q).maximal]
    apply FinitePolarization.mem_orthogonal.mpr
    intro l
    have hl : l.val ∈ (KPLocalGoodSphericalImage.compactTorus
        (C.canonical q).borel (C.canonical q).iwasawa).map (C.canonical q).heisenberg.π :=
      (C.unramified q hqe).polarization_image.symm ▸ l.property
    obtain ⟨j, hj, he⟩ := Subgroup.mem_map.mp hl
    rw [← he]
    exact ((C.canonical q).heisenberg.detects_commutation j (a.t q)).mp ((hc ⟨j, hj⟩).symm)
  obtain ⟨j, hj⟩ := not_forall.mp hnc
  have hjL : (C.canonical q).heisenberg.π j.val ∈ (C.polarization q).L := by
    rw [← (C.unramified q hqe).polarization_image]
    exact Subgroup.mem_map.mpr ⟨j.val, j.property, rfl⟩
  obtain ⟨R, hR⟩ := finite_raw_representatives_exist F ζ hζ {q}
  let t : ∀ r : ({q} : Finset _), KPLocalExceptionalConstruction.actualTorus F ζ hζ r.val :=
    fun r => (Finset.mem_singleton.mp r.property : r.val = q).symm ▸ j.val
  let b := R t
  have hbq : b.t q = j.val := (hR t).1 ⟨q, Finset.mem_singleton_self q⟩
  have hbr (r) (hr : r ≠ q) : b.t r = 1 := by
    apply Subtype.ext
    rw [b.local_lift, (hR t).2 r (by simpa using hr), map_one]
    rfl
  have hbL : ∀ r, (C.canonical r).heisenberg.π (b.t r) ∈ (C.polarization r).L := by
    intro r
    by_cases hr : r = q
    · subst r; rw [hbq]; exact hjL
    · rw [hbr r hr, map_one]; exact Subgroup.one_mem _
  have hjcompact : j.val.val ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q) := by
    obtain ⟨ht, hcompact⟩ := C.actual_compact q hqe
    have hm := j.property
    change ((C.canonical q).borel.torus j.val).val ∈ (C.canonical q).iwasawa.compact.toOpenSubgroup at hm
    rw [(C.canonical q).torus_full] at hm
    change j.val.val ∈ ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup _) at hm
    rw [hcompact] at hm
    obtain ⟨k, hk⟩ := hm
    apply Subgroup.mem_map.mpr
    refine ⟨KPGoodCompactSplitting.kStar F ζ hζ q ht k, ?_, ?_⟩
    · change KPGoodCompactSplitting.kStar F ζ hζ q ht k ∈ KPAdelicCoverRestrictedProduct.finiteCompact F ζ hζ q
      simp only [KPAdelicCoverRestrictedProduct.finiteCompact, dif_neg hgood]
      exact ⟨k, rfl⟩
    · exact hk
  have hright := hinv b (fun r hr => by
      have hn : r ≠ q := fun he => hq (he ▸ hr)
      rw [hbr r hn]; rfl) (fun r hr => by
      by_cases he : r = q
      · subst r; rw [hbq]; exact hjcompact
      · rw [hbr r he]; exact Subgroup.one_mem _)
  have hbeval : ∀ r, C.evaluation r (C.reference r) (b.t r) = 1 := by
    intro r
    by_cases hr : r = q
    · subst r
      rw [hbq, C.evaluation_formula, C.reference_formula, dif_pos hjL,
        (C.unramified q hqe).character_trivial j hjL, Units.val_one]
      have hn := (C.canonical q).iwasawa.intersection_norm
        ((C.canonical q).borel.torus j.val) j.property
      simp only [(C.canonical q).borel.retract_torus] at hn
      have h := congrArg (fun u : ℂˣ => (u : ℂ))
        (ProductPolarization.fullnorm_bridgefinite F q ((C.canonical q).borel.coordinate j.val))
      have hd : (Real.rpow (KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q)
          ((C.canonical q).borel.coordinate j.val)) (1/6 : ℝ) : ℂ) = 1 := by
        simpa [KPGlobalCenterRationalCharacter.positiveComplex,
          KPGlobalCenterRationalCharacter.sixthPower, ActualFiniteTorus.normUnit,
          KPLocalPrincipalSeries.normPower, hn, NNReal.coe_rpow] using h
      rw [hd, div_one]
    · rw [hbr r hr]
      rw [C.evaluation_formula, C.reference_formula]
      simp [KPGlobalCenterRationalCharacter.localAbs, show (⟨(1 : KPLocalExceptionalConstruction.actualTorus F ζ hζ r), by simp⟩ : (C.polarization r).L.comap (C.canonical r).heisenberg.π) = 1 from rfl]
  have hbchar : (Q.character ⟨b.g, raw_polarized_mem F ζ hζ P T C Q hQ b hbL⟩ : ℂ) = 1 := by
    rw [raw_character F ζ hζ P T C Q hQ b hbL]
    simp [hbeval]
  let c : RawEvaluationPoint F ζ hζ :=
    ⟨a.raw * b.raw * a.raw⁻¹ * b.raw⁻¹,
      fun r => a.t r * b.t r * (a.t r)⁻¹ * (b.t r)⁻¹,
      a.g * b.g * a.g⁻¹ * b.g⁻¹,
      by intro w; simp [a.infinite_one, b.infinite_one],
      by
        intro r
        change (a.t r).val * (b.t r).val * (a.t r).val⁻¹ * (b.t r).val⁻¹ =
          KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr r)
            (a.raw (Sum.inr r) * b.raw (Sum.inr r) * (a.raw (Sum.inr r))⁻¹ * (b.raw (Sum.inr r))⁻¹)
        simp only [map_mul, map_inv, ← a.local_lift, ← b.local_lift],
      by simp only [map_mul, map_inv, a.global_lift, b.global_lift]; rfl⟩
  have hcL : ∀ r, (C.canonical r).heisenberg.π (c.t r) ∈ (C.polarization r).L := by
    intro r
    have hc := (C.canonical r).heisenberg.commutator_mem (a.t r) (b.t r)
    have he : (C.canonical r).heisenberg.π (c.t r) = 1 := by
      change c.t r ∈ (C.canonical r).heisenberg.π.ker
      rw [(C.canonical r).heisenberg.quotient_kernel]
      exact hc
    rw [he]; exact Subgroup.one_mem _
  have hcr (r) (hr : r ≠ q) : c.t r = 1 := by
    change a.t r * b.t r * (a.t r)⁻¹ * (b.t r)⁻¹ = 1
    rw [hbr r hr]; group
  have hceval (r) : C.evaluation r (C.reference r) (c.t r) =
      ((C.polarization r).ωL ⟨c.t r, hcL r⟩ : ℂ) := by
    rw [C.evaluation_formula, C.reference_formula, dif_pos (hcL r)]
    have hn : (C.canonical r).borel.coordinate (c.t r) = 1 := by
      change (C.canonical r).borel.coordinate (a.t r * b.t r * (a.t r)⁻¹ * (b.t r)⁻¹) = 1
      simp only [map_mul, map_inv]
      simp [mul_assoc, mul_comm, mul_left_comm]
    rw [hn]
    simp [KPGlobalCenterRationalCharacter.localAbs]
  have hcchar : (Q.character ⟨c.g, raw_polarized_mem F ζ hζ P T C Q hQ c hcL⟩ : ℂ) ≠ 1 := by
    rw [raw_character F ζ hζ P T C Q hQ c hcL, finprod_eq_single _ q]
    · rw [hceval]
      intro he
      apply hj
      apply ((C.canonical q).heisenberg.detects_commutation (a.t q) j.val).mpr
      have hcenter := (C.canonical q).heisenberg.commutator_mem (a.t q) j.val
      have hw := (C.polarization q).extends_center ⟨c.t q, hcL q⟩ (by
        change a.t q * b.t q * (a.t q)⁻¹ * (b.t q)⁻¹ ∈ _
        rw [hbq]; exact hcenter)
      rw [hw] at he
      change ((C.canonical q).heisenberg.ω ⟨a.t q * b.t q * (a.t q)⁻¹ * (b.t q)⁻¹, _⟩ : ℂ) = 1 at he
      simp only [hbq] at he
      have heU : (C.canonical q).heisenberg.ω ⟨a.t q * j.val * (a.t q)⁻¹ * j.val⁻¹, hcenter⟩ = 1 :=
        Units.ext he
      change (C.canonical q).heisenberg.ω ⟨⁅a.t q, j.val⁆, hcenter⟩ = 1 at heU
      rw [(C.canonical q).heisenberg.commutator_pairing] at heU
      exact Subtype.ext heU
    · intro r hr
      rw [hcr r hr, C.evaluation_formula, C.reference_formula]
      simp [KPGlobalCenterRationalCharacter.localAbs, show (⟨(1 : KPLocalExceptionalConstruction.actualTorus F ζ hζ r), by simp⟩ : (C.polarization r).L.comap (C.canonical r).heisenberg.π) = 1 from rfl]
  let jb : Q.H := ⟨b.g, raw_polarized_mem F ζ hζ P T C Q hQ b hbL⟩
  let cc : Q.H := ⟨c.g, raw_polarized_mem F ζ hζ P T C Q hQ c hcL⟩
  have he : cc.val * (jb.val * a.g) = a.g * jb.val := by
    change (a.g * b.g * a.g⁻¹ * b.g⁻¹) * (b.g * a.g) = a.g * b.g
    group
  have hf := v.property cc (jb.val * a.g)
  rw [he, hright, v.property jb a.g] at hf
  change v.val a.g = (Q.character cc : ℂ) * ((Q.character jb : ℂ) * v.val a.g) at hf
  rw [hbchar, one_mul] at hf
  by_contra hn
  apply hcchar
  apply mul_right_cancel₀ hn
  simpa using hf.symm

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

private theorem diagonal_formula (t : KPGlobalTorusFunctionData.ordinaryTorus F) :
    KPGlobalCubicIdelePairing.diagonalPGL F
      (KPGlobalTorusFunctionData.torusRatio F t) = t.val := by
  let A := Classical.choose t.property
  have hA : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F) A = t.val ∧
      A 1 0 = 0 ∧ A 0 1 = 0 := Classical.choose_spec t.property
  let u := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).1.unit
  let w := (KPGlobalTorusFunctionData.diagonal_entries_units F A hA.2.1 hA.2.2).2.unit
  have hu : (u : KPAdelicCoverRestrictedProduct.Adeles F) = A 0 0 := IsUnit.unit_spec _
  have hw : (w : KPAdelicCoverRestrictedProduct.Adeles F) = A 1 1 := IsUnit.unit_spec _
  have heq : A = KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 2) w := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [KPGlobalCubicIdelePairing.diagonalHom, KPGlobalCubicIdelePairing.diagonalMatrix,
        Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
        Matrix.mul_apply, Fin.sum_univ_two, Matrix.scalar, hu, hA.2.1, hA.2.2]
    exact hw.symm
  change QuotientGroup.mk' _ (KPGlobalCubicIdelePairing.diagonalHom F (u * w⁻¹)) = t.val
  rw [← hA.1, heq]
  have hs : QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)
      (Matrix.GeneralLinearGroup.scalar (Fin 2) w) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr ⟨w, rfl⟩
  rw [(QuotientGroup.mk' (KPAdelicCoverRestrictedProduct.scalarSubgroup F)).map_mul,
    hs, mul_one]

 def baseEval (v : KPHilbert.Place F) :
    KPAdelicCoverRestrictedProduct.AdelicPGL2 F →* KPPGLLocalCover.LocalPGL2 F v :=
  QuotientGroup.lift _ ((KPPGLLocalCover.baseQuotient F v).comp
    (KPAdelicCoverRestrictedProduct.matrixEval F v)) (by
      rintro a ⟨w, rfl⟩
      change KPPGLLocalCover.baseQuotient F v
        (KPAdelicCoverRestrictedProduct.matrixEval F v
          (Matrix.GeneralLinearGroup.scalar (Fin 2) w)) = 1
      apply (QuotientGroup.eq_one_iff _).mpr
      refine ⟨KPGlobalCubicIdelePairing.ideleEval F v w, ?_⟩
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [KPScalarSplitCentral.scalarMatrix, KPAdelicCoverRestrictedProduct.matrixEval,
          Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar,
          KPGlobalCubicIdelePairing.ideleEval])

private theorem eval_diagonal (v : KPHilbert.Place F)
    (y : KPGlobalCubicIdelePairing.Ideles F) :
    baseEval F v (KPGlobalCubicIdelePairing.diagonalPGL F y) =
      KPPGLLocalCover.baseQuotient F v
        (KPGlobalProductPolarizationCharacter.diagonalHom F v
          (KPGlobalCubicIdelePairing.ideleEval F v y)) := by
  change KPPGLLocalCover.baseQuotient F v
    (KPAdelicCoverRestrictedProduct.matrixEval F v
      (KPGlobalCubicIdelePairing.diagonalHom F y)) = _
  apply congrArg (KPPGLLocalCover.baseQuotient F v)
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPAdelicCoverRestrictedProduct.matrixEval, KPGlobalCubicIdelePairing.diagonalHom,
      KPGlobalCubicIdelePairing.diagonalMatrix,
      KPGlobalProductPolarizationCharacter.diagonalHom, KubotaRankTwo.coe_d,
      KPGlobalCubicIdelePairing.ideleEval]

private theorem raw_local_projection_eq
    (raw : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (e : KPGlobalTorusFunctionData.E F ζ hζ)
    (he : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = e.val)
    (v : KPHilbert.Place F)
    (b : KPGlobalProductPolarizationCharacter.LocalE F ζ hζ v)
    (hb : b.val = KPPGLLocalCover.coverQuotient F ζ hζ v (raw v)) :
    KPGlobalProductPolarizationCharacter.localProjection F ζ hζ v b =
      KPGlobalCubicIdelePairing.classComparison F
        (KPGlobalProductPolarizationCharacter.pD F ζ hζ e) v := by
  have hproj : KPAdelicCoverRestrictedProduct.pglProjection F ζ hζ e.val =
      KPGlobalCubicIdelePairing.diagonalPGL F (KPGlobalTorusFunctionData.p F ζ hζ e) :=
    (diagonal_formula F ⟨_, e.property⟩).symm
  have h := congrArg (baseEval F v) hproj
  rw [← he, eval_diagonal] at h
  change KPPGLLocalCover.baseQuotient F v
    (KPAdelicCoverRestrictedProduct.matrixEval F v
      (KPAdelicCoverRestrictedProduct.restrictedProjection F ζ hζ raw)) = _ at h
  rw [KPAdelicCoverRestrictedProduct.restrictedProjection_eval] at h
  have hlocal : KPPGLLocalCover.projection F ζ hζ v b.val =
      KPPGLLocalCover.baseQuotient F v
        (KPGlobalProductPolarizationCharacter.diagonalHom F v
          (KPGlobalCubicIdelePairing.ideleEval F v
            (KPGlobalTorusFunctionData.p F ζ hζ e))) := by
    rw [hb]
    exact h
  have hr : KPGlobalProductPolarizationCharacter.localRatio F ζ hζ v b =
      KPGlobalCubicIdelePairing.ideleEval F v (KPGlobalTorusFunctionData.p F ζ hζ e) :=
    (ProductPolarization.localRatioValue_eq F ζ hζ v hlocal.symm).symm
  change KPGlobalCubicIdelePairing.localClass F v
    (KPGlobalProductPolarizationCharacter.localRatio F ζ hζ v b) = _
  rw [hr]
  rfl

set_option maxRecDepth 4096 in

theorem raw_quotient_mem_of_omitted_polarization
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (R : (∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) →
      RawEvaluationPoint F ζ hζ)
    (hR : FiniteRawRepresentatives F ζ hζ S R)
    (a : RawEvaluationPoint F ζ hζ)
    (hpol : ∀ q, q ∉ S →
      (C.canonical q).heisenberg.π (a.t q) ∈ (C.polarization q).L) :
    a.g * (R (fun q : S => a.t q.val)).g⁻¹ ∈ Q.H := by
  classical
  rw [hQ.1]
  let r := R (fun q : S => a.t q.val)
  let raw := a.raw * r.raw⁻¹
  let e := a.g * r.g⁻¹
  have he : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) = e.val := by
    simp only [raw, map_mul, map_inv, a.global_lift, r.global_lift]
    rfl
  change ∀ v, KPGlobalCubicIdelePairing.classComparison F
    (KPGlobalProductPolarizationCharacter.pD F ζ hζ e) v ∈ (P.localData v).L
  intro v
  cases v with
  | inl w =>
    have hb : (1 : KPGlobalProductPolarizationCharacter.LocalE F ζ hζ (Sum.inl w)).val =
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w) (raw (Sum.inl w)) := by
      change 1 = KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inl w)
        (a.raw (Sum.inl w) * (r.raw (Sum.inl w))⁻¹)
      rw [a.infinite_one, r.infinite_one]
      simp
    rw [← raw_local_projection_eq F ζ hζ raw e he (Sum.inl w) 1 hb, map_one]
    exact (P.localData (Sum.inl w)).L.one_mem
  | inr q =>
    let t := a.t q * (r.t q)⁻¹
    have ht : (C.canonical q).heisenberg.π t ∈ (C.polarization q).L := by
      by_cases hq : q ∈ S
      · have hr : r.t q = a.t q := (hR (fun q : S => a.t q.val)).1 ⟨q, hq⟩
        simp only [t, hr, mul_inv_cancel, map_one]
        exact (C.polarization q).L.one_mem
      · have hr : r.t q = 1 := by
          apply Subtype.ext
          rw [r.local_lift, (hR (fun q : S => a.t q.val)).2 q hq]
          exact map_one _
        simpa only [t, hr, inv_one, mul_one] using hpol q hq
    have hm : t.val ∈
        ((KPGlobalProductPolarizationCharacter.localPreimage F ζ hζ (Sum.inr q)
          (P.localData (Sum.inr q)).L).map
            (KPGlobalProductPolarizationCharacter.localTorus F ζ hζ (Sum.inr q)).subtype) := by
      rw [← C.subgroup_matches q]
      exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    obtain ⟨b, hb, hbt⟩ := Subgroup.mem_map.mp hm
    change b.val = t.val at hbt
    have hl : b.val =
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q) (raw (Sum.inr q)) := by
      rw [hbt]
      change (a.t q).val * ((r.t q).val)⁻¹ =
        KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
          (a.raw (Sum.inr q) * (r.raw (Sum.inr q))⁻¹)
      rw [map_mul, map_inv, ← a.local_lift, ← r.local_lift]
    rw [← raw_local_projection_eq F ζ hζ raw e he (Sum.inr q) b hl]
    exact hb

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

theorem raw_reference_tail_zero_of_omitted_nonpolarization
    (C : RawLocalScalarData F ζ hζ P T)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : C.exceptional ⊆ S)
    (a : RawEvaluationPoint F ζ hζ)
    (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ S)
    (hpol : (C.canonical q).heisenberg.π (a.t q) ∉ (C.polarization q).L) :
    (∏ᶠ r, if r ∈ S then 1 else C.evaluation r (C.reference r) (a.t r)) = 0 := by
  classical
  have hsupp : Function.HasFiniteMulSupport
      (fun r => if r ∈ S then 1 else C.evaluation r (C.reference r) (a.t r)) := by
    have hf := restricted_local_evaluations_finite_support F ζ hζ P T C S hS
      (fun q => C.reference q.val) a.raw a.t a.local_lift
    apply hf.subset
    intro r hr
    by_cases h : r ∈ S
    · exact False.elim (hr (if_pos h))
    · simpa only [Function.mem_mulSupport, dif_neg h, if_neg h] using hr
  apply finprod_eq_zero _ q _ hsupp
  rw [if_neg hq, C.evaluation_formula, C.reference_formula, dif_neg hpol, zero_div]

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
open scoped Topology commutatorElement

theorem finite_level_contains_standard_compact_tail
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), ∀ raw :
      KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ,
      (∀ w : InfinitePlace F, raw (Sum.inl w) = 1) →
      (∀ q ∈ S, KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (raw (Sum.inr q)) = 1) →
      (∀ q, q ∉ S → KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (raw (Sum.inr q)) ∈ KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q)) →
      KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ raw) ∈
          KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
  classical
  have hW : ∃ L : ActualFiniteFactor.ProductLevelData F ζ hζ,
      ((ActualFiniteFactor.productSubgroup F ζ hζ L).comap
        (KPGlobalTorusFunctionData.finitePart F ζ hζ).subtype :
          Set (KPGlobalTorusFunctionData.finitePart F ζ hζ)) ⊆
        (J.toOpenSubgroup : Set (KPGlobalTorusFunctionData.finitePart F ζ hζ)) := by
    revert J
    unfold KPGlobalTorusFunctionData.FiniteLevel
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
    intro J
    exact ActualFiniteFactor.productLevels_cofinal F ζ hζ _
      (J.toOpenSubgroup.isOpen.mem_nhds J.toOpenSubgroup.one_mem)
  obtain ⟨L, hL⟩ := hW
  have hfin := Filter.eventually_cofinite.mp L.cofinally_standard
  refine ⟨hfin.toFinset, ?_⟩
  intro raw hi hin hout
  let φ := (KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ).comp
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ)
  have hraw : raw ∈ ActualFiniteFactor.productTuples F ζ hζ L := by
    refine ⟨hi, Subgroup.mem_iInf.mpr ?_⟩
    intro q
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (raw (Sum.inr q)) ∈ (L.localLevel q).toOpenSubgroup
    by_cases hq : q ∈ hfin.toFinset
    · rw [hin q hq]
      exact (L.localLevel q).toOpenSubgroup.one_mem
    · have he : (L.localLevel q).toOpenSubgroup.toSubgroup =
          KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q) := by
        by_contra he
        exact hq (hfin.mem_toFinset.mpr he)
      change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
        (raw (Sum.inr q)) ∈ (L.localLevel q).toOpenSubgroup.toSubgroup
      rw [he]
      exact hout q hq
  have hp : φ raw ∈ ActualFiniteFactor.productSubgroup F ζ hζ L :=
    Subgroup.mem_map.mpr ⟨raw, hraw, rfl⟩
  have hf : φ raw ∈ KPGlobalTorusFunctionData.finitePart F ζ hζ := by
    rw [KPGlobalTorusFiniteStagesCofinality.finitePart_eq_closure F ζ hζ]
    exact ActualFiniteFactor.productSubgroup_le_finite F ζ hζ L hp
  have hj : (⟨φ raw, hf⟩ : KPGlobalTorusFunctionData.finitePart F ζ hζ) ∈
      J.toOpenSubgroup := hL hp
  exact Subgroup.mem_map.mpr ⟨⟨φ raw, hf⟩, hj, rfl⟩

theorem smooth_level_standard_compact_tail_invariance
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hv : v ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q J) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), C.exceptional ⊆ S ∧
      ∀ a : RawEvaluationPoint F ζ hζ,
        (∀ q ∈ S, (a.t q).val = 1) →
        (∀ q, q ∉ S → (a.t q).val ∈
          KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr q)) →
        ∀ g : KPGlobalTorusFunctionData.E F ζ hζ,
          v.val (g * a.g) = v.val g := by
  classical
  obtain ⟨S₀, hS₀⟩ := finite_level_contains_standard_compact_tail F ζ hζ J
  refine ⟨C.exceptional ∪ S₀, Finset.subset_union_left, ?_⟩
  intro a hin hout g
  have hj : a.g.val ∈ KPGlobalTorusFunctionData.globalLevel F ζ hζ J := by
    rw [← a.global_lift]
    apply hS₀ a.raw a.infinite_one
    · intro q hq
      rw [← a.local_lift]
      exact hin q (Finset.mem_union_right _ hq)
    · intro q hq
      rw [← a.local_lift]
      by_cases he : q ∈ C.exceptional
      · rw [hin q (Finset.mem_union_left _ he)]
        exact Subgroup.one_mem _
      · exact hout q (by simpa using And.intro he hq)
  have hf := hv.2 ⟨a.g, hj⟩
  exact congrArg (fun f : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q =>
    f.val g) hf

theorem reference_tail_factorization_of_quotient_mem
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (R : (∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) →
      RawEvaluationPoint F ζ hζ)
    (hR : FiniteRawRepresentatives F ζ hζ S R)
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (a : RawEvaluationPoint F ζ hζ)
    (hm : a.g * (R (fun q : S => a.t q.val)).g⁻¹ ∈ Q.H) :
    v.val a.g = v.val (R (fun q : S => a.t q.val)).g *
      (∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (a.t q)) := by
  classical
  let b := R (fun q : S => a.t q.val)
  let d := a.raw * b.raw⁻¹
  let h : Q.H := ⟨a.g * b.g⁻¹, hm⟩
  have hd : KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ d) = h.val.val := by
    simp only [d, map_mul, map_inv, a.global_lift, b.global_lift]
    rfl
  let x : KPGlobalProductPolarizationCharacter.rawB F ζ hζ P := ⟨d, by
    change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
      (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ d) ∈
        (KPGlobalProductPolarizationCharacter.B F ζ hζ P).map
          (KPGlobalProductPolarizationCharacter.E F ζ hζ).subtype
    rw [hd]
    exact Subgroup.mem_map.mpr ⟨h.val, hQ.1 ▸ h.property, rfl⟩⟩
  obtain ⟨k, hk⟩ := Classical.axiomOfChoice
    (fun q => raw_local_polarization_lift F ζ hζ P T C x q)
  have hkval (q) : (k q).val = a.t q * (b.t q)⁻¹ := by
    apply Subtype.ext
    rw [hk]
    change KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (a.raw (Sum.inr q) * (b.raw (Sum.inr q))⁻¹) = _
    rw [map_mul, map_inv, ← a.local_lift, ← b.local_lift]
    rfl
  have hi : ∀ w : InfinitePlace F, x.val (Sum.inl w) = 1 := by
    intro w
    change a.raw (Sum.inl w) * (b.raw (Sum.inl w))⁻¹ = 1
    rw [a.infinite_one, b.infinite_one, inv_one, mul_one]
  have hchar := raw_reference_product_character F ζ hζ P T C Q hQ x h k hk hi hd
  have href (q : HeightOneSpectrum (𝓞 F)) :
      C.evaluation q (C.reference q) (k q).val =
        if q ∈ S then 1 else C.evaluation q (C.reference q) (a.t q) := by
    rw [hkval]
    by_cases hq : q ∈ S
    · have he : b.t q = a.t q := (hR (fun q : S => a.t q.val)).1 ⟨q, hq⟩
      rw [he, mul_inv_cancel, if_pos hq, C.evaluation_formula, C.reference_formula]
      simp only [map_one, Subgroup.one_mem, dif_pos]
      have hn : KPGlobalCenterRationalCharacter.localAbs F (Sum.inr q) 1 = 1 := by
        simp [KPGlobalCenterRationalCharacter.localAbs]
      rw [hn]
      change ((C.polarization q).ωL 1 : ℂ) / (Real.rpow 1 (1 / 6 : ℝ) : ℂ) = 1
      simp
    · have he : b.t q = 1 := by
        apply Subtype.ext
        rw [b.local_lift, (hR (fun q : S => a.t q.val)).2 q hq, map_one]
        rfl
      rw [he, inv_one, mul_one, if_neg hq]
  simp only [href] at hchar
  have hvh := v.property h b.g
  have he : h.val * b.g = a.g := by
    change (a.g * b.g⁻¹) * b.g = a.g
    simp [mul_assoc]
  rw [he] at hvh
  change v.val a.g = (Q.character h : ℂ) * v.val b.g at hvh
  rw [← hchar, mul_comm] at hvh
  exact hvh

theorem smooth_level_reference_tail_factorization
    (C : RawLocalScalarData F ζ hζ P T)
    (Q : KPGlobalTorusFunctionData.Polarization F ζ hζ)
    (hQ : IsUnitProductModel F ζ hζ P T Q)
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ)
    (v : KPGlobalTorusFunctionData.TorusFunctions F ζ hζ Q)
    (hv : v ∈ KPGlobalTorusFunctionData.TorusSmoothLevel F ζ hζ Q J) :
    ∃ (S : Finset (HeightOneSpectrum (𝓞 F))), C.exceptional ⊆ S ∧
      ∀ (R : (∀ q : S, KPLocalExceptionalConstruction.actualTorus F ζ hζ q.val) →
          RawEvaluationPoint F ζ hζ),
        FiniteRawRepresentatives F ζ hζ S R →
        ∀ a : RawEvaluationPoint F ζ hζ,
          v.val a.g = v.val (R (fun q : S => a.t q.val)).g *
            (∏ᶠ q, if q ∈ S then 1 else C.evaluation q (C.reference q) (a.t q)) := by
  classical
  obtain ⟨S₀, hS₀, hinv₀⟩ := smooth_level_standard_compact_tail_invariance
    F ζ hζ P T C Q J v hv
  let B := (KPAdelicCoverRestrictedProduct.bad_finite F).toFinset
  let S := S₀ ∪ B
  have hS : C.exceptional ⊆ S := Finset.Subset.trans hS₀ Finset.subset_union_left
  have hinv : ∀ b : RawEvaluationPoint F ζ hζ,
      (∀ r ∈ S, (b.t r).val = 1) →
      (∀ r, r ∉ S → (b.t r).val ∈
        KPAdelicCoverRestrictedProduct.pglCompact F ζ hζ (Sum.inr r)) →
      ∀ g : KPGlobalTorusFunctionData.E F ζ hζ,
        v.val (g * b.g) = v.val g := by
    intro b hin hout g
    apply hinv₀ b
    · intro r hr
      exact hin r (Finset.mem_union_left B hr)
    · intro r _
      by_cases hr : r ∈ S
      · rw [hin r hr]
        exact Subgroup.one_mem _
      · exact hout r hr
  refine ⟨S, hS, ?_⟩
  intro R hR a
  by_cases hpol : ∀ q, q ∉ S →
      (C.canonical q).heisenberg.π (a.t q) ∈ (C.polarization q).L
  · exact reference_tail_factorization_of_quotient_mem F ζ hζ P T C Q hQ S R hR v a
      (raw_quotient_mem_of_omitted_polarization F ζ hζ P T C Q hQ S R hR a hpol)
  · push_neg at hpol
    obtain ⟨q, hq, hpol⟩ := hpol
    have hgood : ¬ KPAdelicCoverRestrictedProduct.Bad F q := by
      intro hbad
      exact hq (Finset.mem_union_right S₀
        ((KPAdelicCoverRestrictedProduct.bad_finite F).mem_toFinset.mpr hbad))
    have hz := raw_scalar_support_zero_of_compact_tail_invariance
      F ζ hζ P T C Q hQ S hS v hinv q hq hgood a hpol
    have ht := raw_reference_tail_zero_of_omitted_nonpolarization
      F ζ hζ P T C S hS a q hq hpol
    rw [hz, ht, mul_zero]

end
end DedekindZetaZeroFree.KPGlobalTorusFiniteStagesIdentification

end
