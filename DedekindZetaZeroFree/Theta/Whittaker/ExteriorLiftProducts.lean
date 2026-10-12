module

public import DedekindZetaZeroFree.Theta.Whittaker.ExteriorLiftExtraction

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
lemma commute_list_product {G : Type*} [Group G] (L : List G) (b : G)
    (h : ∀ a ∈ L, Commute a b) : Commute L.prod b := by
  induction L with
  | nil => exact Commute.one_left b
  | cons a L ih =>
      exact (h a (List.mem_cons_self)).mul_left
        (ih (fun c hc => h c (List.mem_cons_of_mem a hc)))
def exteriorLiftValue (p : ThetaBranch.ExteriorPrime R.A)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val)) : ℂ :=
  D.ell (Sum.inr p.val)
    (KPRankOneShellRepair.actualCanonicalImageRepresentation F R.A.zeta12 R.A.primitive_zeta12
      p.val (D.finiteData p.val).inducing (D.finiteData p.val).inducing.polarization
      (D.finiteData p.val).haar (D.finiteData p.val).haar_integer
      (KPPGLLocalCover.coverQuotient F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val) a)
      (D.references (Sum.inr p.val)))

lemma fourier_exterior_list (v : R.A.UnitQuotient)
    (L : List (ThetaBranch.ExteriorPrime R.A)) (hL : L.Nodup)
    (a : ∀ p : ThetaBranch.ExteriorPrime R.A,
      KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr p.val))
    (g : Group R)
    (hg : ∀ p ∈ L, ∀ t : p.val.adicCompletion F, Commute g
      (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
        (KPRationalAdelicSplitting.localAdele F (Sum.inr p.val) t))) :
    fourier R Q.dq (T.theta v) (g * (L.map (fun p => finiteLift R p.val (a p))).prod) =
      (L.map (fun p => exteriorLiftValue R D p (a p))).prod * fourier R Q.dq (T.theta v) g := by
  induction L with
  | nil => simp
  | cons p L ih =>
    have hn := List.nodup_cons.mp hL
    have hc : Commute (finiteLift R p.val (a p))
        (L.map (fun q => finiteLift R q.val (a q))).prod := by
      apply Commute.symm
      apply commute_list_product
      intro b hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      exact finiteLift_commute_distinct R q.val p.val
        (by intro he; exact hn.1 ((Subtype.ext he) ▸ hq)) _ _
    have hr (t : p.val.adicCompletion F) :
        Commute (g * (L.map (fun q => finiteLift R q.val (a q))).prod)
          (KPGlobalTorusFunctionData.N F R.A.zeta12 R.A.primitive_zeta12
            (KPRationalAdelicSplitting.localAdele F (Sum.inr p.val) t)) := by
      apply (hg p (List.mem_cons_self) t).mul_left
      change Commute (L.map (fun q => finiteLift R q.val (a q))).prod _
      rw [← ExteriorWhittakerValues.StoredWhittaker.finite_root_injection R p.val t]
      apply commute_list_product
      intro b hb
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hb
      exact finiteLift_commute_distinct R q.val p.val
        (by intro he; exact hn.1 ((Subtype.ext he) ▸ hq)) _ _
    simp only [List.map_cons, List.prod_cons]
    rw [hc.eq, ← mul_assoc, fourier_forward_exterior_single R D v p _ hr,
      ih hn.2 (fun q hq => hg q (List.mem_cons_of_mem _ hq))]
    exact (mul_assoc _ _ _).symm

end DedekindZetaZeroFree.OrbitExpansion

end
