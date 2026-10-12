module

public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.TensorFiniteRecovery
public import DedekindZetaZeroFree.Theta.Whittaker.FiniteProjector.CutoffPreparation

@[expose] public section

noncomputable section
open scoped Classical NumberField Topology TensorProduct
namespace DedekindZetaZeroFree.FiniteWhittakerProjectors
open MomentSources ThetaExpansion NumberField
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}
variable (R : PrincipalMellin.ActualRecipe S η)
variable {N : TraceHaarTransport R} (A : JointExteriorCoefficientSources R N)
variable (I : R.A.Sf → Type) [∀ q, Fintype (I q)]
variable (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F)

theorem rootWord_fourier (l : List R.A.Sf) (v : R.A.UnitQuotient) (y : R.A.G) :
    fourier R A.sources.dq (rootProjectorWord R I c t l (A.realization.theta v)) (diagonal R y) =
      (l.map (fun q => ∑ i, c q i * (actualFiniteCharacter q.val).toAddChar
        ((y.2 q : q.val.adicCompletion F) * t q i))).prod *
        fourier R A.sources.dq (A.realization.theta v) (diagonal R y) := by
  obtain ⟨s,x,hs,hx⟩ := A.factorization.selected_frozen_stage v
  have hS (q : R.A.Sf) : Sum.inr q.val ∈ s.val := by
    rw [hs]
    exact (A.factorization.bad_exact _).mpr (Or.inr ⟨q.val,rfl,q.property⟩)
  have hx' : tensorFunction R A.factorization s x = A.realization.theta v := by
    change A.factorization.coreMap _ = _
    rw [← hx]
    exact A.factorization.selected_eq v
  induction l with
  | nil => simp [rootProjectorWord]
  | cons q l ih =>
    have hint := rootTensorWord_integrable R A.factorization I c t s hS l x
    have hi : ∀ g, PeriodIntegrable R A.sources.dq
        (rootProjectorWord R I c t l (A.realization.theta v)) g := by
      rw [← hx']; exact hint
    have hr := (A.factorization.core_same_residue
      (RestrictedTensorSimple.stageInclusion _ A.factorization.references A.factorization.bad s
        (PiTensorProduct.tprod ℂ (rootTensorWord R A.factorization I c t s hS l x)))).2.2.1
    have hr' : ∀ γ g, rootProjectorWord R I c t l (A.realization.theta v)
        (KPLiteralRaw.rationalLift F R.A.zeta12 R.A.primitive_zeta12 γ * g) =
          rootProjectorWord R I c t l (A.realization.theta v) g := by
      rw [← hx', ← rootTensorWord_function]
      exact hr
    change fourier R A.sources.dq
      (rightTranslateSum R Finset.univ (c q) (fun i => finiteRoot R q.val (t q i))
        (rootProjectorWord R I c t l (A.realization.theta v))) (diagonal R y) = _
    rw [fourier_rightTranslateSum R A.sources.dq Finset.univ (c q)
      (fun i => finiteRoot R q.val (t q i))
      (rootProjectorWord R I c t l (A.realization.theta v)) (diagonal R y) (fun i _ => hi _)]
    letI := A.sources.quotientHaar
    have htr (i : I q) : fourier R A.sources.dq
        (rootProjectorWord R I c t l (A.realization.theta v))
          (diagonal R y * finiteRoot R q.val (t q i)) =
        (actualFiniteCharacter q.val).toAddChar ((y.2 q : q.val.adicCompletion F) * t q i) *
          fourier R A.sources.dq (rootProjectorWord R I c t l (A.realization.theta v)) (diagonal R y) := by
      unfold finiteRoot
      rw [diagonal_upper_projector, fourier_upper R _ _ hr' _ _ (hi _) (hi _), trace_finite_diagonal]
    simp only [List.map_cons, List.prod_cons]
    simp_rw [htr, ih]
    simp only [← mul_assoc, Finset.sum_mul]

theorem sphericalProduct_one_ne_zero : firstRootSphericalProduct R 1 ≠ 0 := by
  unfold firstRootSphericalProduct
  apply Finset.prod_ne_zero_iff.mpr
  intro w _
  have hn : ‖((1 : R.A.G).1 w : w.Completion)‖ = 1 := by simp
  rw [hn]
  simp only [Complex.ofReal_one, one_mul, one_pow, Real.sqrt_one, mul_one]
  exact Complex.ofReal_ne_zero.mpr (KThird_pos (4 * Real.pi) (mul_pos (by norm_num) Real.pi_pos)).ne'

theorem radialProfile_one_ne_zero (C : FirstRootCutoffs R) : firstRootRadialProfile R C 1 ≠ 0 := by
  have hc : ∀ q : R.A.Sf, (1 : R.A.G).2 q ∈ C.cutoff q := fun q => (C.cutoff q).one_mem
  simpa only [firstRootRadialProfile, if_pos hc, one_mul] using sphericalProduct_one_ne_zero R

theorem cutoff_word_exists (A : FirstRootSphericalSeed R N) (B : FirstRootCutoffs R) :
    ∃ (C : FirstRootCutoffs R) (I : R.A.Sf → Type) (inst : ∀ q, Fintype (I q))
      (c : ∀ q, I q → ℂ) (t : ∀ q, I q → q.val.adicCompletion F),
      C.exponent = B.exponent ∧ (∀ q, C.cutoff q ≤ B.cutoff q) ∧
      (∀ q, (C.cutoff q : Set _) ⊆ A.neighborhood q) ∧
      ∀ v y, letI := inst;
        fourier R A.base.sources.dq (rootProjectorWord R I c t
          (Finset.univ : Finset R.A.Sf).toList (A.base.realization.theta v)) (diagonal R y) =
            firstRootRadialProfile R C y := by
  obtain ⟨C,he,hle,hsub,hmask⟩ := prepare_cutoffs A B
  have hh := fun q => selected_cutoff_weights R A.base q (C.cutoff q) (C.congruence q)
    (C.compact_congruence q) (C.open_congruence q) (C.congruence_exact q)
  choose I inst c t ht using hh
  letI := inst
  refine ⟨C,I,inst,c,t,he,hle,hsub,?_⟩
  intro v y
  rw [rootWord_fourier]
  by_cases hw : fourier R A.base.sources.dq (A.base.realization.theta v) (diagonal R y) = 0
  · rw [hw,mul_zero]
    exact (hmask v y).symm.trans (by rw [hw,mul_zero]) |>.symm
  · simp_rw [ht _ v y hw]
    have hp : ((Finset.univ : Finset R.A.Sf).toList.map (fun q =>
        if y.2 q ∈ C.cutoff q then (1 : ℂ) else 0)).prod =
          if ∀ q : R.A.Sf, y.2 q ∈ C.cutoff q then 1 else 0 := by
      rw [Finset.prod_map_toList]
      by_cases hc : ∀ q : R.A.Sf, y.2 q ∈ C.cutoff q
      · simp [hc]
      · obtain ⟨q,hq⟩ := not_forall.mp hc
        rw [if_neg hc]
        exact Finset.prod_eq_zero (Finset.mem_univ q) (if_neg hq)
    rw [hp]
    exact hmask v y
end DedekindZetaZeroFree.FiniteWhittakerProjectors

end
