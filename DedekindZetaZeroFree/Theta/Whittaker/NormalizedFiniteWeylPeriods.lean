module

public import DedekindZetaZeroFree.Theta.Profiles.RadialJetsAndLocalNorms

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.SheetRescaling
open MomentSources NumberField MeasureTheory
open scoped Classical Topology
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (C : JointDigitDescentSources R N)

theorem finite_translate_period
    (s : RestrictedTensorSimple.Level C.factorization.bad)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p)
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    fourier R C.sources.dq
      (C.factorization.coreMap (RestrictedTensorSimple.stageInclusion _
        C.factorization.references C.factorization.bad s (PiTensorProduct.tprod ℂ x)))
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr q) a)) =
    ∏ p : s.val, C.factorization.ell p
      (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
          R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
          (C.factorization.finiteData q).inducing.polarization
          (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩)) p) := by
  rw [← C.factorization.product_exact s]
  unfold MomentSources.fourier
  apply integral_congr_ae
  filter_upwards [] with t
  rw [C.factorization.finite_intertwining q a s hq x]
  simp only [mul_one]

theorem selected_tensor_nonzero (v : R.A.UnitQuotient)
    (s : RestrictedTensorSimple.Level C.factorization.bad)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p)
    (hx : C.factorization.selected v = RestrictedTensorSimple.stageInclusion _
      C.factorization.references C.factorization.bad s (PiTensorProduct.tprod ℂ x)) :
    ∀ p : s.val, C.factorization.ell p (x p) ≠ 0 := by
  have h := ThetaExpansion.first_root_forward_period_ne_zero R C v
  rw [← C.factorization.selected_eq v, hx, C.factorization.product_exact] at h
  exact fun p => (Finset.prod_ne_zero_iff.mp h) p (Finset.mem_univ p)

theorem normalized_update_product {I : Type*} [Fintype I]
    (f : I → ℂ) (i : I) (b : ℂ) (hf : ∀ j, f j ≠ 0) :
    (∏ j, Function.update f i b j) / (∏ j, f j) = b / f i := by
  classical
  rw [Finset.prod_update_of_mem (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, f j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => hf j)
  simp only [Finset.sdiff_singleton_eq_erase]
  field_simp

theorem selected_finite_ratio (v : R.A.UnitQuotient)
    (s : RestrictedTensorSimple.Level C.factorization.bad)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p)
    (hx : C.factorization.selected v = RestrictedTensorSimple.stageInclusion _
      C.factorization.references C.factorization.bad s (PiTensorProduct.tprod ℂ x))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    fourier R C.sources.dq (C.realization.theta v)
      (KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
        (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
          (Sum.inr q) a)) /
      fourier R C.sources.dq (C.realization.theta v) 1 =
    C.factorization.ell (Sum.inr q)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
        (C.factorization.finiteData q).inducing.polarization
        (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
        (x ⟨Sum.inr q, hq⟩)) /
      C.factorization.ell (Sum.inr q) (x ⟨Sum.inr q, hq⟩) := by
  have hn := selected_tensor_nonzero R C v s x hx
  rw [← C.factorization.selected_eq v, hx, finite_translate_period,
    C.factorization.product_exact]
  have hu : (fun p : s.val => C.factorization.ell p
      (Function.update x ⟨Sum.inr q, hq⟩
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
          R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
          (C.factorization.finiteData q).inducing.polarization
          (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
          (x ⟨Sum.inr q, hq⟩)) p)) =
      Function.update (fun p : s.val => C.factorization.ell p (x p)) ⟨Sum.inr q, hq⟩
        (C.factorization.ell (Sum.inr q)
          (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
            R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
            (C.factorization.finiteData q).inducing.polarization
            (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
            (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
            (x ⟨Sum.inr q, hq⟩))) := by
    funext p
    by_cases hp : p = ⟨Sum.inr q, hq⟩
    · subst p; simp
    · simp [Function.update_of_ne hp]
  rw [hu]
  convert normalized_update_product (fun p : s.val => C.factorization.ell p (x p))
    ⟨Sum.inr q, hq⟩
    (C.factorization.ell (Sum.inr q)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
        (C.factorization.finiteData q).inducing.polarization
        (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
        (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) a)
        (x ⟨Sum.inr q, hq⟩))) hn using 1
  · congr 1
    apply Finset.prod_congr
    · ext p; simp
    · intro p hp
      by_cases he : p = ⟨Sum.inr q, hq⟩
      · subst p; simp
      · simp only [Function.update_apply]
        split_ifs with h <;> simp_all
  · exact hq

theorem dependent_prod_update {I : Type*} [Fintype I] [DecidableEq I] {V : I → Type*}
    (f : ∀ i, V i → ℂ) (x : ∀ i, V i) (i : I) (b : V i) :
    (∏ j, f j (Function.update x i b j)) =
      f i b * ∏ j ∈ Finset.univ.erase i, f j (x j) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun j => f j (Function.update x i b j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact congrArg (f j) (Function.update_of_ne (Finset.mem_erase.mp hj).1 b x)

theorem localWeylValue_eq (v : R.A.UnitQuotient)
    (s : RestrictedTensorSimple.Level C.factorization.bad)
    (x : ∀ p : s.val, actualLocal R C.factorization.finiteData p)
    (hx : C.factorization.selected v = RestrictedTensorSimple.stageInclusion _
      C.factorization.references C.factorization.bad s (PiTensorProduct.tprod ℂ x))
    (q : KPFinitePlace F) (hq : Sum.inr q ∈ s.val) (z : (q.adicCompletion F)ˣ) :
    ThetaExpansion.normalizedLocalWeylValue R C v (Sum.inr q) z =
    C.factorization.ell (Sum.inr q)
      (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12
        R.A.primitive_zeta12 q (C.factorization.finiteData q).inducing
        (C.factorization.finiteData q).inducing.polarization
        (C.factorization.finiteData q).haar (C.factorization.finiteData q).haar_integer
        (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) z *
          KPPGLLocalCover.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
        (x ⟨Sum.inr q, hq⟩)) /
      C.factorization.ell (Sum.inr q) (x ⟨Sum.inr q, hq⟩) := by
  have ha := KPRationalAdelicSplitting.A_local F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) z
  unfold ThetaExpansion.normalizedLocalWeylValue KPRationalAdelicSplitting.pglA
  rw [ha, ← map_mul, ← map_mul]
  have h := selected_finite_ratio R C v s x hx q hq
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q) z *
      KPStandardLocalRootLifts.W F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
  simpa only [map_mul, KPRationalAdelicSplitting.WCoordinates,
    KPPGLLocalCover.A, KPPGLLocalCover.W] using h

end DedekindZetaZeroFree.SheetRescaling

end
