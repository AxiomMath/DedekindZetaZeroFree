module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.FrozenTensorProjector

@[expose] public section

noncomputable section
open scoped Classical NumberField TensorProduct
open NumberField MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {Q : AdmissibleFlatSources R} {T : Realization R Q}
variable (D : SourceFactorization R Q T)
variable (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
variable (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)

def rootProjectorWord (l : List R.A.Sf) : Functions R →ₗ[ℂ] Functions R :=
  l.foldr (fun q a => (rightTranslateSum R Finset.univ (c q)
    (fun i => finiteRoot R q.val (t q i))).comp a) LinearMap.id

def rootTensorWord (s : RestrictedTensorSimple.Level D.bad)
    (hS : ∀ q : R.A.Sf, Sum.inr q.val ∈ s.val)
    (l : List R.A.Sf) (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    ∀ p : s.val, actualLocal R D.finiteData p :=
  l.foldr (fun q x => rootSlotSum R D s x q (hS q) (c q) (t q)) x

theorem rootTensorWord_function (s : RestrictedTensorSimple.Level D.bad)
    (hS : ∀ q : R.A.Sf, Sum.inr q.val ∈ s.val)
    (l : List R.A.Sf) (x : ∀ p : s.val, actualLocal R D.finiteData p) :
    tensorFunction R D s (rootTensorWord R D I c t s hS l x) =
      rootProjectorWord R I c t l (tensorFunction R D s x) := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    change tensorFunction R D s (rootSlotSum R D s _ q (hS q) (c q) (t q)) = _
    rw [tensor_rootSlotSum]
    change (rightTranslateSum R Finset.univ (c q) (fun i => finiteRoot R q.val (t q i)))
      (tensorFunction R D s (rootTensorWord R D I c t s hS l x)) = _
    rw [ih]
    rfl

theorem rootTensorWord_arch (s : RestrictedTensorSimple.Level D.bad)
    (hS : ∀ q : R.A.Sf, Sum.inr q.val ∈ s.val)
    (l : List R.A.Sf) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (w : InfinitePlace F) (hw : Sum.inl w ∈ s.val) :
    rootTensorWord R D I c t s hS l x ⟨Sum.inl w, hw⟩ = x ⟨Sum.inl w, hw⟩ := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    simp only [rootTensorWord, List.foldr_cons, rootSlotSum,
      Function.update_of_ne (show (⟨Sum.inl w, hw⟩ : s.val) ≠ ⟨Sum.inr q.val, hS q⟩ by
        intro h; have := congrArg Subtype.val h; cases this)]
    exact ih

theorem rootTensorWord_integrable (s : RestrictedTensorSimple.Level D.bad)
    (hS : ∀ q : R.A.Sf, Sum.inr q.val ∈ s.val)
    (l : List R.A.Sf) (x : ∀ p : s.val, actualLocal R D.finiteData p)
    (g : Group R) :
    PeriodIntegrable R Q.dq (rootProjectorWord R I c t l (tensorFunction R D s x)) g := by
  rw [← rootTensorWord_function R D I c t s hS l x]
  exact core_period_integrable R D _ g

theorem selected_rootProjectorWord_frozen (l : List R.A.Sf) (v : R.A.UnitQuotient) :
    ∃ (s : RestrictedTensorSimple.Level D.bad)
      (x : ∀ p : s.val, actualLocal R D.finiteData p), s.val = D.bad ∧
      tensorFunction R D s x = rootProjectorWord R I c t l (T.theta v) := by
  obtain ⟨s,x,hs,hx⟩ := D.selected_frozen_stage v
  have hS (q : R.A.Sf) : Sum.inr q.val ∈ s.val := by
    rw [hs]
    exact (D.bad_exact _).mpr (Or.inr ⟨q.val, rfl, q.property⟩)
  refine ⟨s,rootTensorWord R D I c t s hS l x,hs,?_⟩
  rw [rootTensorWord_function]
  congr 1
  change D.coreMap (RestrictedTensorSimple.stageInclusion _ D.references D.bad s
    (PiTensorProduct.tprod ℂ x)) = T.theta v
  rw [← hx]
  exact D.selected_eq v

end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
