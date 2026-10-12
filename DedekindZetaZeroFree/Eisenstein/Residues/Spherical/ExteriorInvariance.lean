module

public import DedekindZetaZeroFree.Adeles.Quotients.FiniteInsertions
public import DedekindZetaZeroFree.Eisenstein.Residues.Spherical.CompactFiniteness

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology
open NumberField Filter MeasureTheory
namespace DedekindZetaZeroFree.RootDerivatives
open MomentSources KPLiteralRaw
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

 theorem tensorFunction_exterior {Q : AdmissibleFlatSources R} {T : Realization R Q}
    (D : SourceFactorization R Q T) (s : RestrictedTensorSimple.Level D.bad)
    (x : ∀ p : s.val, actualLocal R D.finiteData p) (q : KPFinitePlace F)
    (hq : Sum.inr q ∉ s.val)
    (a : KPLocalCover.CubicGL2Raw F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q))
    (ha : a ∈ KPAdelicCoverRestrictedProduct.compact F R.A.zeta12 R.A.primitive_zeta12 (Sum.inr q)) :
    ∀ g, tensorFunction R D s x (g * finiteInjection R q a) = tensorFunction R D s x g := by
  have hqS : q ∉ R.A.Sf := by
    intro h
    exact hq (s.property ((D.bad_exact _).mpr (Or.inr ⟨q,rfl,h⟩)))
  let t : RestrictedTensorSimple.Level D.bad := ⟨insert (Sum.inr q) s.val,
    s.property.trans (Finset.subset_insert _ _)⟩
  have hst : s ≤ t := Finset.subset_insert _ _
  let y : ∀ p : t.val, actualLocal R D.finiteData p := fun p =>
    if h : p.val ∈ s.val then x ⟨p.val,h⟩ else D.references p.val
  have he : tensorFunction R D t y = tensorFunction R D s x := by
    unfold tensorFunction
    have hy' : PiTensorProduct.tprod ℂ y =
        RestrictedTensorSimple.transition _ D.references D.bad s t hst (PiTensorProduct.tprod ℂ x) := by
      simp only [RestrictedTensorSimple.transition, RestrictedTensorSimple.insert_pure]
      congr 1
      funext p
      dsimp only [y]
      split_ifs <;> rfl
    rw [hy']
    change D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad t
      (RestrictedTensorSimple.transition _ D.references D.bad s t hst (PiTensorProduct.tprod ℂ x))) = _
    rw [RestrictedTensorSimple.stageInclusion, RestrictedTensorSimple.stageInclusion,
      Module.DirectLimit.of_f]
  have hqt : Sum.inr q ∈ t.val := Finset.mem_insert_self _ _
  have hy : y ⟨Sum.inr q,hqt⟩ = D.references (Sum.inr q) := by simp [y,hq]
  intro g
  rw [← he]
  have hi := D.finite_intertwining q a t hqt y g
  rw [hy,(D.spherical_reference q hqS).2 a ha] at hi
  have hup : Function.update y ⟨Sum.inr q,hqt⟩ (D.references (Sum.inr q)) = y := by
    rw [← hy,Function.update_eq_self]
  rw [hup] at hi
  exact hi.symm

 theorem normalized_tensor_exterior {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
    (D : ThetaExpansion.SphericalTransportData R A)
    (P : ThetaExpansion.NormalizedSphericalTensor R A D) :
    ExteriorFixed R (tensorFunction R A.factorization D.tensor.stage P.entries) := by
  intro q hq a ha
  apply tensorFunction_exterior R A.factorization D.tensor.stage P.entries q _ a ha
  rw [D.tensor.stage_exact]
  intro h
  rcases (A.factorization.bad_exact _).mp h with ⟨w,h⟩ | ⟨p,h,hp⟩
  · cases h
  · cases h; exact hq hp

end DedekindZetaZeroFree.RootDerivatives

end
