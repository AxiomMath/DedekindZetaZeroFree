module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.WordCutoff

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources ThetaExpansion NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
variable (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
variable (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)
variable {Q' : AdmissibleFlatSources R} (T' : Realization R Q')
variable (hdq : Q'.dq = A.sources.dq)
variable (hpin : ∀ v, T'.theta v = rootProjectorWord R I c t
  (Finset.univ : Finset R.A.Sf).toList (A.realization.theta v))

include I c t hdq hpin

theorem projected_rows_recovery
    (hn : ∀ v, fourier R Q'.dq (T'.theta v) 1 ≠ 0) :
    ∀ v, A.realization.theta v ∈ finiteTranslateSpan R T' := by
  intro v
  let D := A.factorization
  let l := (Finset.univ : Finset R.A.Sf).toList
  obtain ⟨s,x,hs,hx⟩ := D.selected_frozen_stage v
  have hS (q : R.A.Sf) : Sum.inr q.val ∈ s.val := by
    rw [hs]
    exact (D.bad_exact _).mpr (Or.inr ⟨q.val,rfl,q.property⟩)
  let y := rootTensorWord R D I c t s hS l x
  have hx' : tensorFunction R D s x = A.realization.theta v := by
    change D.coreMap _ = _
    rw [← hx]
    exact D.selected_eq v
  have hy' : tensorFunction R D s y = T'.theta v := by
    rw [hpin, ← hx', ← rootTensorWord_function]
  have hp : (∏ p : s.val, D.ell p (y p)) ≠ 0 := by
    rw [← D.product_exact]
    change fourier R A.sources.dq (tensorFunction R D s y) 1 ≠ 0
    rw [hy', ← hdq]
    exact hn v
  have hny (p : s.val) : y p ≠ 0 := by
    have he : D.ell p (y p) ≠ 0 := (Finset.prod_ne_zero_iff.mp hp) p (Finset.mem_univ p)
    exact fun h => he (by rw [h,map_zero])
  let C : Finset s.val := Finset.univ.filter (fun p => ∃ q : KPFinitePlace F, p.val = Sum.inr q)
  have hC (p : s.val) (hp : p ∈ C) : ∃ q : KPFinitePlace F, p.val = Sum.inr q :=
    (Finset.mem_filter.mp hp).2
  have hm : tensorFunction R D s y ∈ finiteTranslateSpan R T' := by
    rw [hy']
    exact Submodule.subset_span ⟨v,1,by simp⟩
  have hr := tensor_slots_recovery R D T' s x y C hC (fun p _ => hny p) hm
  have he : (fun p : s.val => if p ∈ C then x p else y p) = x := by
    funext p
    obtain ⟨p,hp⟩ := p
    cases p with
    | inl w =>
      have hpc : (⟨Sum.inl w,hp⟩ : s.val) ∉ C := by simp [C]
      rw [if_neg hpc]
      exact rootTensorWord_arch R D I c t s hS l x w hp
    | inr q =>
      have hpc : (⟨Sum.inr q,hp⟩ : s.val) ∈ C :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨q,rfl⟩⟩
      rw [if_pos hpc]
  rw [he,hx'] at hr
  exact hr

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
