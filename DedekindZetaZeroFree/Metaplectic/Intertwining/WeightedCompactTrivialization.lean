module

public import DedekindZetaZeroFree.Metaplectic.Intertwining.WeightedWeylCenterCharacters

@[expose] public section

open scoped NumberField Valued
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPActualResidueSources

open KPLocalPrincipalSeries KPRankOneCenterInducedDiagonalComparison

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in

theorem actual_weighted_compact_trivialization
    (S : KPActualScalarBinding.ActualKPBinding F ζ hζ q)
    (I : IwasawaData S.borel)
    (E : CenterModule S.heisenberg ≃ₗ[ℂ] CenterModule S.heisenberg)
    (hE : ∀ (f : CenterModule S.heisenberg)
      (h : KPExceptionalRaw.actualTorus F ζ hζ q),
      (E f).val h =
        normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate h) (1 / 3) *
          f.val (S.borel.weyl h))
    (J : CompactOpenLevel (KPRankOneOpenCellKernel.Cover F ζ hζ q))
    (hJ : J.toOpenSubgroup ≤ I.compact.toOpenSubgroup) :
    ∃ (EJminus : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .minus J ≃ₗ[ℂ]
        centerCompactLevel F ζ hζ q S.heisenberg S.borel I .plus J)
      (EJplus : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .plus J ≃ₗ[ℂ]
        centerCompactLevel F ζ hζ q S.heisenberg S.borel I .minus J),
      EJplus = EJminus.symm ∧
      (∀ (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .minus J)
        (k : I.compact.toOpenSubgroup),
        (EJminus φ).val.val k = E (φ.val.val k)) ∧
      (∀ (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .plus J)
        (k : I.compact.toOpenSubgroup),
        (EJplus φ).val.val k = E (φ.val.val k)) ∧
      (∀ (s : ℂ)
        (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .minus J)
        (g : KPRankOneOpenCellKernel.Cover F ζ hζ q)
        (h : KPExceptionalRaw.actualTorus F ζ hζ q),
        (E ((centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
          .minus (-s) φ.val).val g)).val h =
        ((centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
          .plus (-s - 1 / 3) (EJminus φ).val).val g).val h) ∧
      (∀ (s : ℂ)
        (φ : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .plus J)
        (g : KPRankOneOpenCellKernel.Cover F ζ hζ q)
        (h : KPExceptionalRaw.actualTorus F ζ hζ q),
        (E ((centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
          .plus s φ.val).val g)).val h =
        ((centerCompactTrivialization F ζ hζ q S.heisenberg S.borel I
          .minus (s + 1 / 3) (EJplus φ).val).val g).val h) := by
  obtain ⟨E₀, hE₀, hInv₀, hAct₀⟩ := actual_center_weighted_weyl F ζ hζ q S
  have heq : E = E₀ := by
    apply LinearEquiv.ext
    intro f
    apply Subtype.ext
    funext h
    exact (hE f h).trans (hE₀ f h).symm
  have hInv : ∀ f, E (E f) = f := heq ▸ hInv₀
  have hAct : ∀ a f,
      E ((centerTorus F ζ hζ q S.heisenberg S.borel .minus) a f) =
        normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate a) (-1/3) •
          (centerTorus F ζ hζ q S.heisenberg S.borel .plus) a (E f) := heq ▸ hAct₀
  have hActPlus : ∀ a f,
      E ((centerTorus F ζ hζ q S.heisenberg S.borel .plus) a f) =
        normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate a) (1/3) •
          (centerTorus F ζ hζ q S.heisenberg S.borel .minus) a (E f) := by
    intro a f
    have h := congrArg E (hAct a (E f))
    simp only [hInv, map_smul] at h
    have hn : normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate a) (1/3) *
        normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate a) (-1/3) = 1 := by
      simp only [normPower, ← Complex.exp_add, ← add_mul]
      norm_num
    have hh := congrArg (normPower (KPExceptionalRaw.LocalField F q) (S.borel.coordinate a) (1/3) • ·) h
    simpa only [smul_smul, hn, one_smul] using hh.symm
  have hCompact (ε : Sign) (b : S.borel.B)
      (hb : (b : KPRankOneOpenCellKernel.Cover F ζ hζ q) ∈ I.compact.toOpenSubgroup)
      (f : CenterModule S.heisenberg) :
      E (centerInducingAction F ζ hζ q S.heisenberg S.borel ε 0 b f) =
        centerInducingAction F ζ hζ q S.heisenberg S.borel
          (if ε = .plus then .minus else .plus) 0 b (E f) := by
    have hn : ∀ z : ℂ, normPower (KPExceptionalRaw.LocalField F q)
        (S.borel.coordinate (S.borel.retract b)) z = 1 := by
      intro z
      simp [normPower, I.intersection_norm b hb]
    change E (inducingScalar S.borel 0 b •
      (centerTorus F ζ hζ q S.heisenberg S.borel ε) (S.borel.retract b) f) =
        inducingScalar S.borel 0 b • (centerTorus F ζ hζ q S.heisenberg S.borel
          (if ε = .plus then .minus else .plus)) (S.borel.retract b) (E f)
    cases ε <;> simp only [map_smul, hAct, hActPlus, hn, one_smul,
      reduceCtorEq, ite_true, ite_false]
  let M (ε : Sign) : centerCompactLevel F ζ hζ q S.heisenberg S.borel I ε J →ₗ[ℂ]
      centerCompactLevel F ζ hζ q S.heisenberg S.borel I
        (if ε = .plus then .minus else .plus) J := {
    toFun := fun φ => ⟨⟨fun k => E (φ.val.val k), by
      constructor
      · intro b k k' hk
        have hb : (b : KPRankOneOpenCellKernel.Cover F ζ hζ q) ∈ I.compact.toOpenSubgroup := by
          have he : (b : KPRankOneOpenCellKernel.Cover F ζ hζ q) = (k' : KPRankOneOpenCellKernel.Cover F ζ hζ q) * (k : KPRankOneOpenCellKernel.Cover F ζ hζ q)⁻¹ := by
            rw [hk, mul_inv_cancel_right]
          rw [he]
          exact I.compact.toOpenSubgroup.mul_mem k'.property (I.compact.toOpenSubgroup.inv_mem k.property)
        change E (φ.val.val k') = _
        rw [φ.val.property.1 b k k' hk]
        exact hCompact ε b hb _
      · obtain ⟨L,hL⟩ := φ.val.property.2
        refine ⟨L, ?_⟩
        intro l hl
        funext k
        exact congrArg E (congrFun (hL l hl) k)⟩, by
      intro j k k' hk
      exact congrArg E (φ.property j k k' hk)⟩
    map_add' := by
      intro φ ψ
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact E.map_add _ _
    map_smul' := by
      intro c φ
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact E.map_smul c _ }
  let EM : centerCompactLevel F ζ hζ q S.heisenberg S.borel I .minus J ≃ₗ[ℂ]
      centerCompactLevel F ζ hζ q S.heisenberg S.borel I .plus J := {
    __ := M .minus
    invFun := M .plus
    left_inv := by
      intro φ
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact hInv _
    right_inv := by
      intro φ
      apply Subtype.ext
      apply Subtype.ext
      funext k
      exact hInv _ }
  refine ⟨EM, EM.symm, rfl, fun φ k => rfl, fun φ k => rfl, ?_, ?_⟩
  · intro s φ g h
    change (E (centerInducingAction F ζ hζ q S.heisenberg S.borel .minus (-s)
      (I.borelPart g) (φ.val.val (I.compactPart g)))).val h =
      (centerInducingAction F ζ hζ q S.heisenberg S.borel .plus (-s-1/3)
        (I.borelPart g) (E (φ.val.val (I.compactPart g)))).val h
    change (E (inducingScalar S.borel (-s) (I.borelPart g) •
      (centerTorus F ζ hζ q S.heisenberg S.borel .minus) (S.borel.retract (I.borelPart g))
        (φ.val.val (I.compactPart g)))).val h =
      (inducingScalar S.borel (-s-1/3) (I.borelPart g) •
        (centerTorus F ζ hζ q S.heisenberg S.borel .plus) (S.borel.retract (I.borelPart g))
          (E (φ.val.val (I.compactPart g)))).val h
    rw [E.map_smul, hAct, smul_smul]
    have he : inducingScalar S.borel (-s) (I.borelPart g) *
        normPower (KPExceptionalRaw.LocalField F q)
          (S.borel.coordinate (S.borel.retract (I.borelPart g))) (-1/3) =
        inducingScalar S.borel (-s-1/3) (I.borelPart g) := by
      unfold inducingScalar
      rw [mul_assoc]
      congr 1
      simp only [normPower, ← Complex.exp_add]
      congr 1
      ring
    rw [he]
  · intro s φ g h
    change (E (centerInducingAction F ζ hζ q S.heisenberg S.borel .plus s
      (I.borelPart g) (φ.val.val (I.compactPart g)))).val h =
      (centerInducingAction F ζ hζ q S.heisenberg S.borel .minus (s+1/3)
        (I.borelPart g) (E (φ.val.val (I.compactPart g)))).val h
    change (E (inducingScalar S.borel s (I.borelPart g) •
      (centerTorus F ζ hζ q S.heisenberg S.borel .plus) (S.borel.retract (I.borelPart g))
        (φ.val.val (I.compactPart g)))).val h =
      (inducingScalar S.borel (s+1/3) (I.borelPart g) •
        (centerTorus F ζ hζ q S.heisenberg S.borel .minus) (S.borel.retract (I.borelPart g))
          (E (φ.val.val (I.compactPart g)))).val h
    rw [E.map_smul, hActPlus, smul_smul]
    have he : inducingScalar S.borel s (I.borelPart g) *
        normPower (KPExceptionalRaw.LocalField F q)
          (S.borel.coordinate (S.borel.retract (I.borelPart g))) (1/3) =
        inducingScalar S.borel (s+1/3) (I.borelPart g) := by
      unfold inducingScalar
      rw [mul_assoc]
      congr 1
      simp only [normPower, ← Complex.exp_add]
      congr 1
      ring
    rw [he]

end
end DedekindZetaZeroFree.KPActualResidueSources
