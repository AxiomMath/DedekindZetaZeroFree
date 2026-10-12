module

public import DedekindZetaZeroFree.Metaplectic.Torus.RationalPeriodization.TensorCovariance

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct BigOperators NNReal
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing
open MomentSources TensorActionSource KPGlobalTorusFiniteStages
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η) (N : TraceHaarTransport R)
variable (P : CompatibleModelData F R.A.zeta12 R.A.primitive_zeta12)
variable (C : LocalFiberData F R.A.zeta12 R.A.primitive_zeta12 P)
local instance : DecidableEq (KPHilbert.Place F) := Classical.decEq _

theorem localValue_torus_factor
    (u : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix R w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (p : KPHilbert.Place F) (f : Plus R N P C p)
    (g : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 p) :
    localValue R N P C p (u p * g) f =
      (Real.rpow (localNorm R P C t a d p) (1/2 : ℝ) : ℂ) •
        torusSlot R P C u t a d p (localValue R N P C p g f) := by
  cases p with
  | inr q =>
    rw [localValue_finite_torus R N P C q f _ g (t q) (ht q),
      EisensteinReferenceSections.LocalTorus.finite_deltaHalf]
    rfl
  | inl w =>
    rw [localValue_arch_torus R N P C w f _ g _ _ _ (hp w)]
    change _ = (Real.rpow _ (1/2 : ℝ) : ℂ) *
      ((KPSourceConvention.ordinaryGenuineCharacter F R.A.zeta12 R.A.primitive_zeta12
        (u (Sum.inl w)).epsilon : ℂ) * (Real.rpow _ (1/6 : ℝ) : ℂ) * _)
    rw [KPCplxPrincipalSeriesCharts.inductionWeight, KPCplxPrincipalSeriesCharts.positiveParameter]
    have hpos : 0 < localNorm R P C t a d (Sum.inl w) :=
      EisensteinReferenceSections.SourceTorusCovariance.localNorm_pos F R.A.zeta12 R.A.primitive_zeta12 P C t a d _
    have hm := EisensteinReferenceSections.SourceTorusCovariance.rpow_factor (localNorm R P C t a d (Sum.inl w)) hpos
    norm_num only [show (1/2 + 1/6 : ℝ) = 2/3 by norm_num, LinearMap.id_apply]
    change (Real.rpow (localNorm R P C t a d (Sum.inl w)) (2/3 : ℝ) : ℂ) * _ * _ =
      (Real.rpow (localNorm R P C t a d (Sum.inl w)) (1/2 : ℝ) : ℂ) * _
    rw [show ((Real.rpow (localNorm R P C t a d (Sum.inl w)) (2/3 : ℝ)) : ℂ) =
      (Real.rpow (localNorm R P C t a d (Sum.inl w)) (1/2 : ℝ) : ℂ) *
      (Real.rpow (localNorm R P C t a d (Sum.inl w)) (1/6 : ℝ) : ℂ) from hm.symm]
    dsimp only [localNorm, EisensteinReferenceSections.TorusNorms.localNorm]
    ring

theorem deltaHalf_eq_nu_cube
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) :
    KPGlobalTorusFunctionData.deltaHalf F R.A.zeta12 R.A.primitive_zeta12 e =
      ((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℂ) ^ (3 : ℕ) := by
  unfold KPGlobalTorusFunctionData.deltaHalf
  rw [Real.sqrt_eq_rpow]
  have hd : (((KPGlobalTorusFunctionData.delta F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℝ)) =
      (((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℝ)) ^ (6 : ℕ) := by
    simp only [KPGlobalCenterRationalCharacter.nu, MonoidHom.comp_apply,
      KPGlobalCenterRationalCharacter.sixthPower, Units.coe_map,
      NNReal.rpowMonoidHom_apply, NNReal.coe_rpow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [hd, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem normHalf_product
    (u : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix R w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 u) = e.val)
    (U : Finset (KPHilbert.Place F)) (hU : ∀ p, p ∉ U → localNorm R P C t a d p = 1) :
    (∏ p : U, (Real.rpow (localNorm R P C t a d p) (1/2 : ℝ) : ℂ)) =
      KPGlobalTorusFunctionData.deltaHalf F R.A.zeta12 R.A.primitive_zeta12 e := by
  have hn := (EisensteinReferenceSections.TorusNorms.given_raw_norm F R.A.zeta12 R.A.primitive_zeta12
    P C u t a d b e ht hp he).2
  have hs : Function.mulSupport (fun p => Real.rpow (localNorm R P C t a d p) (1/6 : ℝ)) ⊆ U := by
    intro p h
    by_contra hnot
    exact h (by dsimp only; rw [hU p hnot]; norm_num)
  rw [finprod_eq_prod_of_mulSupport_subset _ hs] at hn
  have hr (p : KPHilbert.Place F) :
      (Real.rpow (localNorm R P C t a d p) (1/2 : ℝ) : ℂ) =
      (Real.rpow (localNorm R P C t a d p) (1/6 : ℝ) : ℂ) ^ (3 : ℕ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul
      (EisensteinReferenceSections.SourceTorusCovariance.localNorm_pos F R.A.zeta12 R.A.primitive_zeta12 P C t a d p).le]
    norm_num
  simp_rw [hr]
  rw [Finset.prod_pow]
  have hc : (∏ p : U, (Real.rpow (localNorm R P C t a d p) (1/6 : ℝ) : ℂ)) =
      ((KPGlobalCenterRationalCharacter.nu F R.A.zeta12 R.A.primitive_zeta12 e : ℝ≥0) : ℂ) := by
    rw [Finset.prod_coe_sort U (fun p => (Real.rpow (localNorm R P C t a d p) (1/6 : ℝ) : ℂ)),
      ← Complex.ofReal_prod, ← hn]
  rw [hc, deltaHalf_eq_nu_cube R]

theorem rawRationalEvaluator_torus
    (u : Raw R)
    (t : ∀ q, KPLocalExceptionalConstruction.actualTorus F R.A.zeta12 R.A.primitive_zeta12 q)
    (a d : InfinitePlace F → ℂˣ) (b : InfinitePlace F → ℂ)
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (ht : ∀ q, (t q).val = KPPGLLocalCover.coverQuotient F R.A.zeta12
      R.A.primitive_zeta12 (Sum.inr q) (u (Sum.inr q)))
    (hp : ∀ w, complexMatrix R w (u (Sum.inl w)) =
      KPCplxPrincipalSeriesCharts.upperTriangular (a w) (d w) (b w))
    (he : KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
      (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 u) = e.val)
    (g : Raw R) (x : PlusCore R N P C)
    (r : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) :
    (comparisonSmooth R P C (rawCoreVector R N P C (u * g) x)).val.val r =
      KPGlobalTorusFunctionData.deltaHalf F R.A.zeta12 R.A.primitive_zeta12 e *
        (comparisonSmooth R P C (rawCoreVector R N P C g x)).val.val (r * e) := by
  letI : Nonempty (RestrictedTensorSimple.Level (bad R P C)) := ⟨⟨bad R P C, le_rfl⟩⟩
  obtain ⟨s, z, rfl⟩ := Module.DirectLimit.exists_of x
  obtain ⟨G, hG⟩ := exists_reference_stage R N P C g
  obtain ⟨UG, hUG⟩ := exists_reference_stage R N P C (u * g)
  obtain ⟨U0, hU0⟩ := exists_reference_stage R N P C u
  have hn := (EisensteinReferenceSections.TorusNorms.given_raw_norm F R.A.zeta12 R.A.primitive_zeta12
    P C u t a d b e ht hp he).1
  let U : RestrictedTensorSimple.Level (bad R P C) :=
    ⟨s.val ∪ G.val ∪ UG.val ∪ U0.val ∪ hn.toFinset,
      s.property.trans (Finset.subset_union_left.trans
        (Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)))⟩
  have hsU : s ≤ U := Finset.subset_union_left.trans
    (Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left))
  have hgU : ∀ p, p ∉ U.val → localValue R N P C p (g p) (plusReference R N P C p) = reference R P C p := by
    intro p hp
    exact hG p (fun h => hp (by simp [U, h]))
  have hugU : ∀ p, p ∉ U.val → localValue R N P C p ((u * g) p) (plusReference R N P C p) = reference R P C p := by
    intro p hp
    exact hUG p (fun h => hp (by simp [U, h]))
  have huU : ∀ p, p ∉ U.val → localValue R N P C p (u p) (plusReference R N P C p) = reference R P C p := by
    intro p hp
    exact hU0 p (fun h => hp (by simp [U, h]))
  have hnU : ∀ p, p ∉ U.val → localNorm R P C t a d p = 1 := by
    intro p hp
    by_contra h
    exact hp (Finset.mem_union_right _ (hn.mem_toFinset.mpr h))
  have hslot : ∀ p, p ∉ U.val → torusSlot R P C u t a d p (reference R P C p) = reference R P C p := by
    intro p hpU
    have hpbad : p ∉ bad R P C := fun h => hpU (U.property h)
    have h := localValue_torus_factor R N P C u t a d b ht hp p (plusReference R N P C p) 1
    rw [mul_one, huU p hpU, localValue_reference_one R N P C p hpbad, hnU p hpU] at h
    norm_num at h
    exact h.symm
  let y := RestrictedTensorSimple.transition (Plus R N P C) (plusReference R N P C)
    (bad R P C) s U hsU z
  have hins : RestrictedTensorSimple.stageInclusion _ _ _ U y =
      RestrictedTensorSimple.stageInclusion (Plus R N P C) (plusReference R N P C) (bad R P C) s z :=
    Module.DirectLimit.of_f
  change (comparisonSmooth R P C (rawCoreVector R N P C (u * g)
    (RestrictedTensorSimple.stageInclusion _ _ _ s z))).val.val r = _
  change (comparisonSmooth R P C (rawCoreVector R N P C (u * g)
    (RestrictedTensorSimple.stageInclusion _ _ _ s z))).val.val r =
    KPGlobalTorusFunctionData.deltaHalf F R.A.zeta12 R.A.primitive_zeta12 e *
      (comparisonSmooth R P C (rawCoreVector R N P C g
        (RestrictedTensorSimple.stageInclusion _ _ _ s z))).val.val (r * e)
  rw [← hins]
  change (comparisonSmooth R P C (rawCoreVector R N P C (u * g)
    (RestrictedTensorSimple.stageInclusion _ _ _ U y))).val.val r =
    KPGlobalTorusFunctionData.deltaHalf F R.A.zeta12 R.A.primitive_zeta12 e *
      (comparisonSmooth R P C (rawCoreVector R N P C g
        (RestrictedTensorSimple.stageInclusion _ _ _ U y))).val.val (r * e)
  rw [rawCoreVector_stage R N P C U (u * g) hugU,
    rawCoreVector_stage R N P C U g hgU]
  change (comparisonSmooth R P C (stageVector R N P C U (u * g) y)).val.val r = _
  induction y using PiTensorProduct.induction_on with
  | smul_tprod c y =>
    simp only [map_smul]
    change c * _ = _ * (c * _)
    rw [stageVector_pure, stageVector_pure]
    have hv : (fun p : U.val => localValue R N P C p ((u * g) p) (y p)) =
        (fun p : U.val => (Real.rpow (localNorm R P C t a d p) (1/2 : ℝ) : ℂ) •
          torusSlot R P C u t a d p (localValue R N P C p (g p) (y p))) := by
      funext p
      exact localValue_torus_factor R N P C u t a d b ht hp p (y p) (g p)
    rw [hv, MultilinearMap.map_smul_univ, map_smul, map_smul,
      normHalf_product R P C u t a d b e ht hp he U.val hnU]
    change c * (_ * _) = _ * (c * _)
    rw [comparisonSmooth_torus_stage R P C u t a d b e ht hp he U _ hslot r]
    ring
  | add x y hx hy =>
    simp only [map_add]
    change (_ : ℂ) + _ = _ * (_ + _)
    rw [hx, hy, mul_add]

theorem quotientRationalEvaluator_torus (x : PlusCore R N P C)
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12)
    (g : Group R) (r : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) :
    (quotientRationalEvaluator R N P C x (e.val * g)).val.val r =
      KPGlobalTorusFunctionData.deltaHalf F R.A.zeta12 R.A.primitive_zeta12 e *
        (quotientRationalEvaluator R N P C x g).val.val (r * e) := by
  obtain ⟨u, t, a, d, ht, hp, he⟩ := EisensteinReferenceSections.TorusNorms.raw_lifts F
    R.A.zeta12 R.A.primitive_zeta12 e
  induction g using QuotientGroup.induction_on with
  | H g =>
    induction g using QuotientGroup.induction_on with
    | H g =>
      rw [← he]
      change (comparisonSmooth R P C (quotientCoreVector R N P C x
        (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 u) *
        KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
          (KPAdelicCoverRestrictedProduct.amalgamation F R.A.zeta12 R.A.primitive_zeta12 g)))).val.val r = _
      rw [← map_mul, ← map_mul, quotientCoreVector_raw]
      exact rawRationalEvaluator_torus R N P C u t a d (fun _ => 0) e ht hp he g x r

def scalarSourceEvaluator : PlusCore R N P C →ₗ[ℂ] Functions R where
  toFun x g := (quotientRationalEvaluator R N P C x g).val.val 1
  map_add' x y := by
    funext g
    have h := congrFun ((quotientRationalEvaluator R N P C).map_add x y) g
    exact congrArg (fun f => f.val.val 1) h
  map_smul' c x := by
    funext g
    have h := congrFun ((quotientRationalEvaluator R N P C).map_smul c x) g
    exact congrArg (fun f => f.val.val 1) h

theorem scalarSource_fibre_recovery (x : PlusCore R N P C)
    (e : KPGlobalTorusFunctionData.E F R.A.zeta12 R.A.primitive_zeta12) (g : Group R) :
    (quotientRationalEvaluator R N P C x g).val.val e =
      (KPGlobalTorusFunctionData.deltaHalf F R.A.zeta12 R.A.primitive_zeta12 e)⁻¹ *
        scalarSourceEvaluator R N P C x (e.val * g) := by
  have h := quotientRationalEvaluator_torus R N P C x e g 1
  simp only [one_mul] at h
  change _ = _⁻¹ * (quotientRationalEvaluator R N P C x (e.val * g)).val.val 1
  rw [h, ← mul_assoc, inv_mul_cancel₀, one_mul]
  unfold KPGlobalTorusFunctionData.deltaHalf
  apply Complex.ofReal_ne_zero.mpr
  exact (Real.sqrt_pos.mpr (by
    exact_mod_cast (pos_iff_ne_zero.mpr (KPGlobalTorusFunctionData.delta F R.A.zeta12
      R.A.primitive_zeta12 e).ne_zero))).ne'

end DedekindZetaZeroFree.FourierContinuation.FaithfulSource.RepairedInducing

end
