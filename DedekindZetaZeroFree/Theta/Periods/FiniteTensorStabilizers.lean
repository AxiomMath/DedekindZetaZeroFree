module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.TensorNormalization

@[expose] public section

noncomputable section
open scoped Classical NumberField
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.RootDerivatives
open NumberField MeasureTheory MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}

def finiteDiagonal (p : R.A.Sf) (u : (p.val.adicCompletion F)ˣ) : Group R :=
  KPAdelicCoverRestrictedProduct.scalarQuotient F R.A.zeta12 R.A.primitive_zeta12
    (KPAdelicCoverRestrictedProduct.localInjection F R.A.zeta12 R.A.primitive_zeta12
      (Sum.inr p.val)
      (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) u))

def finiteDiagonalWord (l : List R.A.Sf) (u : ∀ p : R.A.Sf, (p.val.adicCompletion F)ˣ) : Group R :=
  (l.map (fun p => finiteDiagonal R p (u p))).prod

theorem tensor_finite_pointwise_neighborhood (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (q : R.A.Sf) (hq : Sum.inr q.val ∈ s.val) :
    ∃ V : Set (q.val.adicCompletion F)ˣ, IsOpen V ∧ 1 ∈ V ∧
      ∀ u ∈ V, ∀ g : Group R,
        tensorFunction R D s x (g * finiteDiagonal R q u) = tensorFunction R D s x g := by
  obtain ⟨V, hVo, hV1, hfix⟩ := finite_vector_fixed_near_one R q.val (D.finiteData q.val)
    (x ⟨Sum.inr q.val, hq⟩)
  refine ⟨V, hVo, hV1, fun u hu g => ?_⟩
  have hi := D.finite_intertwining q.val
    (KPStandardLocalRootLifts.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) u) s hq x g
  change tensorFunction R D s (Function.update x ⟨Sum.inr q.val, hq⟩
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      q.val (D.finiteData q.val).inducing (D.finiteData q.val).inducing.polarization
      (D.finiteData q.val).haar (D.finiteData q.val).haar_integer
      (KPPGLLocalCover.A F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q.val) u)
      (x ⟨Sum.inr q.val, hq⟩))) g = tensorFunction R D s x (g * finiteDiagonal R q u) at hi
  rw [hfix u hu, Function.update_eq_self] at hi
  exact hi.symm

theorem tensor_finite_common_neighborhood (D : SourceFactorization R Q T)
    (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    ∃ V : ∀ q : R.A.Sf, Set (q.val.adicCompletion F)ˣ,
      (∀ q, IsOpen (V q)) ∧ (∀ q, 1 ∈ V q) ∧
      ∀ (u : ∀ q : R.A.Sf, (q.val.adicCompletion F)ˣ), (∀ q, u q ∈ V q) →
        ∀ (l : List R.A.Sf) (g : Group R),
          tensorFunction R D s x (g * finiteDiagonalWord R l u) = tensorFunction R D s x g := by
  have hq (q : R.A.Sf) : Sum.inr q.val ∈ s.val :=
    s.property ((D.bad_exact _).mpr (Or.inr ⟨q.val, rfl, q.property⟩))
  choose V hVo hV1 hfix using fun q => tensor_finite_pointwise_neighborhood R D s x q (hq q)
  refine ⟨V, hVo, hV1, fun u hu l => ?_⟩
  induction l with
  | nil => intro g; simp [finiteDiagonalWord]
  | cons q l ih =>
    intro g
    change tensorFunction R D s x (g * (finiteDiagonal R q (u q) * finiteDiagonalWord R l u)) = _
    rw [← mul_assoc, ih, hfix q (u q) (hu q) g]

end DedekindZetaZeroFree.RootDerivatives

end
