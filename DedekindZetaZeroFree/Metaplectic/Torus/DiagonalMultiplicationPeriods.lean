module

public import DedekindZetaZeroFree.Theta.Whittaker.CentralEquivariance

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory KPAdelicCoverRestrictedProduct
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)

 def sDefect (x y : R.A.G) : CentralTuples F :=
  ⟨fun w => match w with
    | .inl _ => 1
    | .inr p => if hp : p ∈ R.A.Sf then
        KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (.inr p) (x.2 ⟨p, hp⟩) (y.2 ⟨p, hp⟩) ^ 2
      else 1,
    by
      rw [Filter.eventually_cofinite]
      apply Set.Finite.subset (R.A.Sf.finite_toSet.image Sum.inr)
      intro w hw
      cases w with
      | inl w => exact False.elim (hw rfl)
      | inr p =>
        by_cases hp : p ∈ R.A.Sf
        · exact ⟨p, hp, rfl⟩
        · exact False.elim (hw (dif_neg hp))⟩

private lemma sDefect_arch (x y : R.A.G) (w : InfinitePlace F) :
    sDefect R x y (Sum.inl w) = 1 := rfl
private lemma sDefect_finite (x y : R.A.G) (p : KPFinitePlace F) (hp : p ∈ R.A.Sf) :
    sDefect R x y (Sum.inr p) =
      KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (.inr p) (x.2 ⟨p, hp⟩) (y.2 ⟨p, hp⟩) ^ 2 := by
  change (if h : p ∈ R.A.Sf then _ else _) = _
  exact dif_pos hp
private lemma sDefect_exterior (x y : R.A.G) (p : KPFinitePlace F) (hp : p ∉ R.A.Sf) :
    sDefect R x y (Sum.inr p) = 1 := by
  change (if h : p ∈ R.A.Sf then _ else _) = _
  exact dif_neg hp

lemma raw_diagonal_mul (x y : R.A.G) :
    KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R x) *
      KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R y) =
    centralTupleMap F R.A.zeta12 R.A.primitive_zeta12 (sDefect R x y) *
      KPRationalAdelicSplitting.ATuple F R.A.zeta12 R.A.primitive_zeta12 (localIdele R (x * y)) := by
  apply RestrictedProduct.ext
  intro w
  change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
    (Units.map (adeleEval F w) (localIdele R x)) *
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
    (Units.map (adeleEval F w) (localIdele R y)) =
    KPLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12 w (sDefect R x y w) *
    KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 w
    (Units.map (adeleEval F w) (localIdele R (x * y)))
  cases w with
  | inl w =>
    rw [DigitMasks.localIdele_arch, DigitMasks.localIdele_arch, DigitMasks.localIdele_arch,
      KPStandardLocalRootLifts.A_mul]
    rw [sDefect_arch]
    simp only [KPHilbert.B3, KPHilbert.B6_infinite, map_one, one_pow, one_mul,
      Prod.fst_mul, Pi.mul_apply]
  | inr p =>
    by_cases hp : p ∈ R.A.Sf
    · rw [DigitMasks.localIdele_finite R _ p hp, DigitMasks.localIdele_finite R _ p hp,
        DigitMasks.localIdele_finite R _ p hp, KPStandardLocalRootLifts.A_mul]
      rw [sDefect_finite R x y p hp]
      rfl
    · have hx := DigitMasks.localIdele_exterior R x p hp
      have hy := DigitMasks.localIdele_exterior R y p hp
      have hxy := DigitMasks.localIdele_exterior R (x * y) p hp
      change Units.map (adeleEval F (.inr p)).toMonoidHom (localIdele R x) = 1 at hx
      change KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (.inr p)
          (Units.map (adeleEval F (.inr p)).toMonoidHom (localIdele R x)) *
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (.inr p)
          (Units.map (adeleEval F (.inr p)).toMonoidHom (localIdele R y)) =
        KPLocalCover.centralInjection F R.A.zeta12 R.A.primitive_zeta12 (.inr p)
          (sDefect R x y (.inr p)) *
        KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (.inr p)
          (Units.map (adeleEval F (.inr p)).toMonoidHom (localIdele R (x * y)))
      rw [hx, hy, hxy, sDefect_exterior R x y p hp]
      simp only [KPStandardLocalRootLifts.A_one, one_mul, map_one]

lemma diagonal_mul_center (x y : R.A.G) :
    diagonal R x * diagonal R y =
      pglCentralInjection F R.A.zeta12 R.A.primitive_zeta12 (centralProduct F (sDefect R x y)) *
        diagonal R (x * y) := by
  have h := congrArg (rawToGroup R) (raw_diagonal_mul R x y)
  rw [map_mul, map_mul, rawToGroup_central_tuple] at h
  exact h

lemma fourier_forward_diagonal_mul {Q : AdmissibleFlatSources R} (T : Realization R Q)
    (v : R.A.UnitQuotient) (x y : R.A.G) :
    fourier R Q.dq (T.theta v) (diagonal R x * diagonal R y) =
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12
        (centralProduct F (sDefect R x y)) : ℂ) *
      fourier R Q.dq (T.theta v) (diagonal R (x * y)) := by
  rw [diagonal_mul_center, fourier_center]

lemma sDefect_product (x y : R.A.G) :
    centralProduct F (sDefect R x y) =
      ∏ p : R.A.Sf, KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (.inr p.val)
        (x.2 p) (y.2 p) ^ 2 := by
  change (∏ᶠ w, sDefect R x y w) = _
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := R.A.Sf.image Sum.inr)]
  · rw [Finset.prod_image (by intro p hp q hq he; exact Sum.inr.inj he),
      ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro p hp
    exact sDefect_finite R x y p.val p.property
  · intro w hw
    cases w with
    | inl w => exact False.elim (hw (sDefect_arch R x y w))
    | inr p =>
      by_cases hp : p ∈ R.A.Sf
      · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
      · exact False.elim (hw (sDefect_exterior R x y p hp))

lemma fourier_diagonal_mul_actual {N : TraceHaarTransport R} (C : JointUpperVanishingSources R N)
    (v : R.A.UnitQuotient) (x y : R.A.G) :
    fourier R C.sources.dq (C.realization.theta v) (diagonal R x * diagonal R y) =
      (R.σ ((R.A.H_S x y : Fˣ) : F) ^ 2)⁻¹ * C.packet.forwardProfile v (x * y) := by
  rw [fourier_forward_diagonal_mul, sDefect_product, map_prod]
  have he (p : R.A.Sf) :
      (KPGlobalTorusFunctionData.iota F R.A.zeta12 R.A.primitive_zeta12
        (KPHilbert.B3 F R.A.zeta12 R.A.primitive_zeta12 (.inr p.val) (x.2 p) (y.2 p) ^ 2) : ℂ) =
      KPSourceConvention.sourceC F R.A.zeta12 R.A.primitive_zeta12 (.inr p.val) (x.2 p) (y.2 p) := rfl
  rw [Units.coe_prod]
  simp_rw [he]
  rw [KPSourceConvention.prod_sourceC_arithmetic]
  have ha : R.σ ((R.A.H_S x y : Fˣ) : F) =
      (KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12 (R.A.H_S x y) : ℂ) := by
    have h := C.aligned (R.A.H_S x y)
    have hr : KPLocalCover.coefficientEmbedding F S.zeta12 S.primitive_zeta12 =
        KPLocalCover.coefficientEmbedding F R.A.zeta12 R.A.primitive_zeta12 := by
      congr 1
      exact R.sameRoot.symm
    rwa [hr] at h
  rw [← ha, C.forward]
  simp only [zpow_neg, zpow_ofNat]

end DedekindZetaZeroFree.OrbitExpansion

end
