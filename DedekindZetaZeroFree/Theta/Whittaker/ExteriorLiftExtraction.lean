module

public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorCompactInvariance

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace DedekindZetaZeroFree.OrbitExpansion
open MomentSources NumberField MeasureTheory
open scoped NumberField Classical
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)

lemma selected_exterior_stage (v : R.A.UnitQuotient) (p : ThetaBranch.ExteriorPrime R.A) :
    ∃ (s : RestrictedTensorSimple.Level D.bad)
      (x : ∀ j : s.val, actualLocal R D.finiteData j)
      (hp : Sum.inr p.val ∈ s.val),
      D.selected v = RestrictedTensorSimple.stageInclusion _ D.references D.bad s
        (PiTensorProduct.tprod ℂ x) ∧ x ⟨Sum.inr p.val, hp⟩ = D.references (Sum.inr p.val) := by
  obtain ⟨s, x, hs, hx⟩ := D.selected_frozen_stage v
  let t : RestrictedTensorSimple.Level D.bad :=
    ⟨insert (Sum.inr p.val) s.val, by rw [hs]; exact Finset.subset_insert _ _⟩
  have hst : s ≤ t := Finset.subset_insert _ _
  let y : ∀ j : t.val, actualLocal R D.finiteData j :=
    fun j => if h : (j : KPHilbert.Place F) ∈ s.val then x ⟨j, h⟩ else D.references j
  have hp : Sum.inr p.val ∈ t.val := Finset.mem_insert_self _ _
  refine ⟨t, y, hp, ?_, ?_⟩
  · rw [hx]
    have he : RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (RestrictedTensorSimple.insert _ D.references s.val t.val hst (PiTensorProduct.tprod ℂ x)) =
      RestrictedTensorSimple.stageInclusion _ D.references D.bad s (PiTensorProduct.tprod ℂ x) :=
      Module.DirectLimit.of_f
    rw [RestrictedTensorSimple.insert_pure] at he
    refine he.symm.trans ?_
    congr 2
    funext j
    dsimp only [y]
    split_ifs <;> rfl
  · have hn : Sum.inr p.val ∉ s.val := by
      rw [hs, D.bad_exact]
      simp only [Sum.inr_ne_inl, false_and, exists_false, Sum.inr.injEq, false_or]
      rintro ⟨q, hq, hqS⟩
      subst q
      exact p.property hqS
    exact dif_neg hn

lemma fourier_forward_exterior_single (v : R.A.UnitQuotient)
    (p : ThetaBranch.ExteriorPrime R.A) (g : Group R)
    (hg : ∀ t : p.val.adicCompletion F, Commute g
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr p.val) t)))
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) :
    fourier R Q.dq (T.theta v) (g * finiteLift R p.val a) =
      D.ell (Sum.inr p.val)
        (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
          p.val (D.finiteData p.val).inducing (D.finiteData p.val).inducing.polarization
          (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
          (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) a)
          (D.references (Sum.inr p.val))) * fourier R Q.dq (T.theta v) g := by
  obtain ⟨s, x, hp, hx, href⟩ := selected_exterior_stage R D v p
  rw [← D.selected_eq v, hx]
  let b := KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
    p.val (D.finiteData p.val).inducing (D.finiteData p.val).inducing.polarization
    (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
    (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) a)
    (D.references (Sum.inr p.val))
  have he := slotPeriod_finite_action R D s x p.val hp g a (D.references (Sum.inr p.val))
  have hr := LinearMap.congr_fun (slotPeriod_exterior R D s x p hp g hg) b
  simp only [LinearMap.smul_apply, smul_eq_mul] at hr
  have hx' : Function.update x ⟨Sum.inr p.val, hp⟩ (D.references (Sum.inr p.val)) = x := by
    rw [← href, Function.update_eq_self]
  change fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
    (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr p.val, hp⟩ b)))) g =
    fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr p.val, hp⟩ (D.references (Sum.inr p.val))))))
      (g * finiteLift R p.val a) at he
  rw [hx'] at he
  change fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
    (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr p.val, hp⟩ b)))) g =
    fourier R Q.dq (D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
      (PiTensorProduct.tprod ℂ (Function.update x ⟨Sum.inr p.val, hp⟩ (D.references (Sum.inr p.val)))))) g *
        D.ell (Sum.inr p.val) b at hr
  rw [hx'] at hr
  exact he.symm.trans (hr.trans (mul_comm _ _))

lemma finiteLift_commute_distinct (p q : KPFinitePlace F) (hpq : p ≠ q)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p))
    (b : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    Commute (finiteLift R p a) (finiteLift R q b) := by
  have he : (KPAdelicCoverRestrictedProduct.localToRestricted F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr p) a) (Sum.inr q) = 1 := by
    change Pi.mulSingle (Sum.inr p) a (Sum.inr q) = 1
    exact Pi.mulSingle_eq_of_ne (Sum.inr_injective.ne hpq.symm) a
  exact group_commute_single R _ q he b

end DedekindZetaZeroFree.OrbitExpansion

end
