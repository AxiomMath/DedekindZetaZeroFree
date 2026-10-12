module

public import DedekindZetaZeroFree.LargeSieve.Bilinear.DivisibleColumnOperator

@[expose] public section

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedPairMask
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}

private lemma offdiag_iff (u v : Ideal (𝓞 F)) :
    u*v ≠ ⊤ ↔ u ≠ ⊤ ∨ v ≠ ⊤ := by
  have h : u*v = ⊤ ↔ u = ⊤ ∧ v = ⊤ := by
    constructor
    · intro hh
      exact ⟨top_unique (hh ▸ Ideal.mul_le_left), top_unique (hh ▸ Ideal.mul_le_right)⟩
    · rintro ⟨rfl,rfl⟩; simp
  simp only [ne_eq, h, not_and_or]

private lemma column_spec (C : Context Q) {u : Ideal (𝓞 F)} (hu : u ∈ C.columns) :
    Squarefree u ∧ u ≠ ⊥ ∧ u ⊔ c = ⊤ ∧ Squarefree (C.d*u) ∧
    (C.d*u) ⊔ c = ⊤ ∧ C.d ⊔ u = ⊤ := by
  obtain ⟨huA, huM, huG⟩ := Finset.mem_filter.mp hu
  obtain ⟨husf, huc, -⟩ := (Sieve.mem_idealAdmissibleFinset F c _ u).mp huA
  obtain ⟨hdusf, hduc, -⟩ := (Sieve.mem_paperShell F c C.N (C.d*u)).mp huM
  refine ⟨husf, husf.ne_zero, huc, hdusf, hduc, ?_⟩
  have hrel := (squarefree_mul_iff.mp hdusf).1
  exact Ideal.isUnit_iff.mp (hrel (Ideal.dvd_iff_le.mpr le_sup_left)
    (Ideal.dvd_iff_le.mpr le_sup_right))
private lemma valid_pair_of_columns (C : Context Q) {u v : Ideal (𝓞 F)}
    (hu : u ∈ C.columns) (hv : v ∈ C.columns) (huv : u ⊔ v = ⊤)
    (hoff : u*v ≠ ⊤) : Context.ValidPair C (u,v) := by
  obtain ⟨husf, hu0, huc, hdusf, hduc, hdu⟩ := column_spec C hu
  obtain ⟨hvsf, hv0, hvc, hdvsf, hdvc, hdv⟩ := column_spec C hv
  have hclass : Q.cls (C.d*u) = Q.cls (C.d*v) :=
    (Finset.mem_filter.mp hu).2.2.trans (Finset.mem_filter.mp hv).2.2.symm
  have hc : Q.cls u = Q.cls v := by
    letI := Q.instGroup
    rw [Q.cls_mul _ _ C.hdc huc, Q.cls_mul _ _ C.hdc hvc] at hclass
    exact mul_left_cancel hclass
  refine ⟨hu0,hv0,husf,hvsf,huc,hvc,hdusf,hdvsf,hduc,hdvc,huv,?_,hclass,hc,hoff⟩
  exact ((Ideal.isCoprime_iff_sup_eq.mpr hdu).mul_right
    (Ideal.isCoprime_iff_sup_eq.mpr hdv)).sup_eq

theorem pair_mask_split (C : Context Q) (f g : Ideal (𝓞 F))
    (h : Ideal (𝓞 F) → Ideal (𝓞 F) → ℂ) :
    (∑ p ∈ C.pairs, if f ∣ p.1 ∧ g ∣ p.2 then h p.1 p.2 else 0) =
    (∑ u ∈ C.columns.filter (fun u => f ∣ u ∧ u ≠ ⊤),
      ∑ v ∈ C.columns.filter (fun v => g ∣ v), if u ⊔ v = ⊤ then h u v else 0) +
    (∑ u ∈ C.columns.filter (fun u => f ∣ u ∧ u = ⊤),
      ∑ v ∈ C.columns.filter (fun v => g ∣ v ∧ v ≠ ⊤), if u ⊔ v = ⊤ then h u v else 0) := by
  unfold Context.pairs
  rw [Finset.sum_filter, Finset.sum_product]
  simp_rw [Finset.sum_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  rw [show (0 : ℂ) = ∑ _v ∈ C.columns, (0 : ℂ) from (Finset.sum_const_zero).symm,
    ← Finset.sum_ite_irrel, ← Finset.sum_ite_irrel]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  have hvalid : Context.ValidPair C (u,v) ↔ u ⊔ v = ⊤ ∧ (u ≠ ⊤ ∨ v ≠ ⊤) := by
    constructor
    · intro hp; exact ⟨hp.huv, (offdiag_iff u v).mp hp.offDiagonal⟩
    · rintro ⟨huv,hoff⟩; exact valid_pair_of_columns C hu hv huv ((offdiag_iff u v).mpr hoff)
  simp only [hvalid]
  by_cases hf : f ∣ u <;> by_cases hg : g ∣ v <;>
    by_cases huv : u ⊔ v = ⊤ <;> by_cases hu0 : u = ⊤ <;> by_cases hv0 : v = ⊤ <;>
    simp [hf,hg,huv,hu0,hv0]

end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedPairMask

end

end

section
noncomputable section
open scoped NumberField Classical BigOperators
namespace DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows
variable {F : Type} [Field F] [NumberField F] {c : Ideal (𝓞 F)}
variable {Q : DedekindZetaZeroFree.QuadraticHeckeFamily F c}
def energy (C : Context Q) (f : Ideal (𝓞 F)) : ℝ :=
  ∑ u ∈ C.columns, if f ∣ u then (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors u).toFinset.card * ‖C.lam (C.d*u)‖^2 else 0
private lemma column_spec_local (C : Context Q) {u : Ideal (𝓞 F)} (hu : u ∈ C.columns) :
    Squarefree u ∧ u ≠ ⊥ ∧ u ⊔ c = ⊤ ∧ Squarefree (C.d*u) ∧
    (C.d*u) ⊔ c = ⊤ ∧ C.d ⊔ u = ⊤ := by
  obtain ⟨huA, huM, huG⟩ := Finset.mem_filter.mp hu
  obtain ⟨husf, huc, -⟩ := (Sieve.mem_idealAdmissibleFinset F c _ u).mp huA
  obtain ⟨hdusf, hduc, -⟩ := (Sieve.mem_paperShell F c C.N (C.d*u)).mp huM
  refine ⟨husf, husf.ne_zero, huc, hdusf, hduc, ?_⟩
  have hrel := (squarefree_mul_iff.mp hdusf).1
  exact Ideal.isUnit_iff.mp (hrel (Ideal.dvd_iff_le.mpr le_sup_left)
    (Ideal.dvd_iff_le.mpr le_sup_right))
private lemma finite_coprime_sum_bound
    (R U V : Finset (Ideal (𝓞 F)))
    (hU : ∀ u ∈ U, u ≠ ⊥) (hV : ∀ v ∈ V, v ≠ ⊥)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hUA : ∀ z : Ideal (𝓞 F) → ℂ, (∑ r ∈ R, ‖∑ u ∈ U, z u * (Q.χ u) r‖^2) ≤ A * ∑ u ∈ U, ‖z u‖^2)
    (hVB : ∀ z : Ideal (𝓞 F) → ℂ, (∑ r ∈ R, ‖∑ v ∈ V, z v * (Q.χ v) r‖^2) ≤ B * ∑ v ∈ V, ‖z v‖^2)
    (x y : Ideal (𝓞 F) → ℂ) :
    (∑ r ∈ R, ‖∑ u ∈ U, ∑ v ∈ V, if u ⊔ v = ⊤ then
      x u * star (y v) * (Q.χ u) r * star ((Q.χ v) r) else 0‖) ≤
      Real.sqrt (A*B) * Real.sqrt
        ((∑ u ∈ U, (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors u).toFinset.card * ‖x u‖^2) *
         (∑ v ∈ V, (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors v).toFinset.card * ‖y v‖^2)) := by
  have h := Sieve.DivisorSeparation.rectangle_operator_bound Q
    {⊤} {⊤} R U V hU hV A B hA hB
    (by intro d hd z; have hd' : d = ⊤ := Finset.mem_singleton.mp hd; subst d; simpa using hUA z)
    (by intro d hd z; have hd' : d = ⊤ := Finset.mem_singleton.mp hd; subst d; simpa using hVB z) x y
  simp only [Sieve.DivisorSeparation.idealDivisorRectangle, Finset.sum_singleton,
    Finset.card_singleton, Nat.cast_one, one_mul] at h
  have htop : ∀ u : Ideal (𝓞 F), (⊤ : Ideal (𝓞 F)) ∣ u := fun u =>
    by simpa only [← Ideal.one_eq_top] using one_dvd u
  have hfilter : ∀ u : Ideal (𝓞 F), ({⊤} : Finset (Ideal (𝓞 F))).filter (fun d => d ∣ u) = {⊤} := by
    intro u; apply Finset.filter_eq_self.mpr
    intro d hd; rw [Finset.mem_singleton.mp hd]; exact htop u
  simp only [htop, and_true, hfilter, Finset.card_singleton,
    Nat.cast_one, mul_one, starRingEnd_apply] at h
  rw [mul_assoc (A*B)] at h
  have hs := Real.le_sqrt_of_sq_le h
  simpa only [Real.sqrt_mul (mul_nonneg hA hB)] using hs
private lemma coprime_filtered_bound
    (C : Context Q) (R V₁ V₂ : Finset (Ideal (𝓞 F)))
    (f₁ f₂ : Ideal (𝓞 F))
    (hV₁ : V₁ ⊆ C.columns) (hV₂ : V₂ ⊆ C.columns)
    (hf₁ : ∀ u ∈ V₁, f₁ ∣ u) (hf₂ : ∀ u ∈ V₂, f₂ ∣ u)
    (U₁ U₂ : ℝ) (hU₁ : 0 ≤ U₁) (hU₂ : 0 ≤ U₂)
    (hop₁ : ∀ z : Ideal (𝓞 F) → ℂ, (∑ a ∈ R, ‖∑ u ∈ V₁, z u * (Q.χ u) a‖^2) ≤ U₁ * ∑ u ∈ V₁, ‖z u‖^2)
    (hop₂ : ∀ z : Ideal (𝓞 F) → ℂ, (∑ a ∈ R, ‖∑ u ∈ V₂, z u * (Q.χ u) a‖^2) ≤ U₂ * ∑ u ∈ V₂, ‖z u‖^2)
    (x y : Ideal (𝓞 F) → ℂ)
    (hx : ∀ u ∈ C.columns, ‖x u‖ ≤ ‖C.lam (C.d*u)‖) (hy : ∀ u ∈ C.columns, ‖y u‖ ≤ ‖C.lam (C.d*u)‖) :
    (∑ a ∈ R, ‖∑ u ∈ V₁, ∑ v ∈ V₂, if u ⊔ v = ⊤ then
      x u * star (y v) *
        (Q.χ u) a * star ((Q.χ v) a) else 0‖) ≤
      Real.sqrt (U₁*U₂) * Real.sqrt (energy C f₁ * energy C f₂) := by
  have he : ∀ (V : Finset (Ideal (𝓞 F))) (f : Ideal (𝓞 F)) (z : Ideal (𝓞 F) → ℂ),
      V ⊆ C.columns → (∀ u ∈ V, f ∣ u) → (∀ u ∈ C.columns, ‖z u‖ ≤ ‖C.lam (C.d*u)‖) →
      (∑ u ∈ V, (2:ℝ)^(UniqueFactorizationMonoid.normalizedFactors u).toFinset.card *
        ‖z u‖^2) ≤ energy C f := by
    intro V f z hV hf hz
    unfold energy
    apply Finset.sum_le_sum_of_injOn (fun u => u)
    · intro u hu v hv heq; exact heq
    · intro u hu; exact hV (by simpa using hu)
    · intro u hu
      rw [if_pos (hf u hu)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ (norm_nonneg _) (hz u (hV hu)) 2
    · intros; split_ifs <;> positivity
  have hh := finite_coprime_sum_bound R V₁ V₂
    (fun u hu => (column_spec_local C (hV₁ hu)).2.1)
    (fun u hu => (column_spec_local C (hV₂ hu)).2.1)
    U₁ U₂ hU₁ hU₂ hop₁ hop₂
    x y
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  apply mul_le_mul (he V₁ f₁ x hV₁ hf₁ hx) (he V₂ f₂ y hV₂ hf₂ hy)
  · positivity
  · unfold energy; positivity

def coreBlock (C : Context Q) (f₁ f₂ : Ideal (𝓞 F))
    (x y : Ideal (𝓞 F) → ℂ) (r : Ideal (𝓞 F)) : ℂ :=
  ∑ p ∈ C.pairs, if f₁ ∣ p.1 ∧ f₂ ∣ p.2 then
    x p.1 * star (y p.2) * (Q.χ p.1) r * star ((Q.χ p.2) r) else 0

theorem core_divisible_pair_bound (D : Sieve.AllIndexNormalizedFamilyData Q) :
    ∃ A : ℝ, 0 < A ∧ ∀ C : Context Q, C.D = D → 1 ≤ C.N →
    ∀ B P₁ P₂ : ℝ, 1 ≤ B → 1 ≤ P₁ → 1 ≤ P₂ →
    ∀ f₁ f₂ : Ideal (𝓞 F), f₁ ≠ ⊥ → f₂ ≠ ⊥ → P₁ ≤ norm f₁ → P₂ ≤ norm f₂ →
    ∀ R : Finset (Ideal (𝓞 F)), R ⊆ Sieve.idealAdmissibleFinset F c (2*B) →
    ∀ x y : Ideal (𝓞 F) → ℂ,
    (∀ u ∈ C.columns, ‖x u‖ ≤ ‖C.lam (C.d*u)‖) →
    (∀ u ∈ C.columns, ‖y u‖ ≤ ‖C.lam (C.d*u)‖) →
    (∑ r ∈ R, ‖coreBlock C f₁ f₂ x y r‖) ≤
      A * Real.sqrt (ErrorRectangles.U Q B (C.N/(norm C.d*P₁)) *
        ErrorRectangles.U Q B (C.N/(norm C.d*P₂))) *
        Real.sqrt (energy C f₁ * energy C f₂) := by
  by_cases hex : ∃ C : Context Q, C.D = D
  · obtain ⟨C₀,hC₀⟩ := hex
    have core : D.bad = c := by rw [← hC₀]; exact C₀.core
    obtain ⟨A,hA,hop⟩ := DivisiblePrefix.realized_divisible_column_U D core
    refine ⟨2*A, by linarith, ?_⟩
    intro C hCD hN B P₁ P₂ hB hP₁ hP₂ f₁ f₂ hf₁ hf₂ hPf₁ hPf₂ R hR x y hx hy
    let V₁ := C.columns.filter (fun u => f₁ ∣ u ∧ u ≠ ⊤)
    let V₂ := C.columns.filter (fun u => f₂ ∣ u)
    let V₃ := C.columns.filter (fun u => f₁ ∣ u ∧ u = ⊤)
    let V₄ := C.columns.filter (fun u => f₂ ∣ u ∧ u ≠ ⊤)
    let U₁ := A * ErrorRectangles.U Q B (C.N/(norm C.d*P₁))
    let U₂ := A * ErrorRectangles.U Q B (C.N/(norm C.d*P₂))
    have hU : ∀ P, 0 ≤ A * ErrorRectangles.U Q B (C.N/(norm C.d*P)) := by
      intro P; exact mul_nonneg (by linarith) (Real.sSup_nonneg' ⟨0,Or.inl rfl,le_rfl⟩)
    have hOp : ∀ P f, 1 ≤ P → f ≠ ⊥ → P ≤ norm f →
        ∀ V : Finset (Ideal (𝓞 F)), V ⊆ C.columns → (∀ u ∈ V, f ∣ u) →
        ∀ z : Ideal (𝓞 F) → ℂ,
        (∑ r ∈ R, ‖∑ u ∈ V, z u * (Q.χ u) r‖^2) ≤
          A * ErrorRectangles.U Q B (C.N/(norm C.d*P)) * ∑ u ∈ V, ‖z u‖^2 := by
      intro P f hP hf hPf V hV hfV z

      by_cases hne : V.Nonempty
      · obtain ⟨u,hu⟩ := hne
        obtain ⟨husf,hu0,huc,-⟩ := column_spec_local C (hV hu)
        have hfsf := husf.squarefree_of_dvd (hfV u hu)
        have hfc : f ⊔ c = ⊤ := eq_top_iff.mpr (huc ▸ sup_le_sup_right (Ideal.dvd_iff_le.mp (hfV u hu)) c)
        have hh := hop C hCD hN B P hB hP f hf hfsf hfc hPf R V hR hV
          (fun _ => 1) (fun _ => 1) z (by simp) (by simp)
        simp only [one_mul,mul_one] at hh
        have he : ∀ r, (∑ u ∈ V, if f ∣ u then z u * (Q.χ u) r else 0) = ∑ u ∈ V, z u * (Q.χ u) r := by
          intro r; apply Finset.sum_congr rfl; intro u hu; rw [if_pos (hfV u hu)]
        have heE : (∑ u ∈ V, if f ∣ u then ‖z u‖^2 else 0) = ∑ u ∈ V, ‖z u‖^2 := by
          apply Finset.sum_congr rfl; intro u hu; rw [if_pos (hfV u hu)]
        simpa only [he,heE] using hh
      · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp
    have h₁ := coprime_filtered_bound C R V₁ V₂ f₁ f₂
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (fun u hu => (Finset.mem_filter.mp hu).2.1)
      (fun u hu => (Finset.mem_filter.mp hu).2)
      U₁ U₂ (hU _) (hU _)
      (hOp P₁ f₁ hP₁ hf₁ hPf₁ V₁ (Finset.filter_subset _ _) (fun u hu => (Finset.mem_filter.mp hu).2.1))
      (hOp P₂ f₂ hP₂ hf₂ hPf₂ V₂ (Finset.filter_subset _ _) (fun u hu => (Finset.mem_filter.mp hu).2)) x y hx hy
    have h₂ := coprime_filtered_bound C R V₃ V₄ f₁ f₂
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      (fun u hu => (Finset.mem_filter.mp hu).2.1)
      (fun u hu => (Finset.mem_filter.mp hu).2.1)
      U₁ U₂ (hU _) (hU _)
      (hOp P₁ f₁ hP₁ hf₁ hPf₁ V₃ (Finset.filter_subset _ _) (fun u hu => (Finset.mem_filter.mp hu).2.1))
      (hOp P₂ f₂ hP₂ hf₂ hPf₂ V₄ (Finset.filter_subset _ _) (fun u hu => (Finset.mem_filter.mp hu).2.1)) x y hx hy
    have hsqrt : Real.sqrt (U₁*U₂) = A * Real.sqrt
        (ErrorRectangles.U Q B (C.N/(norm C.d*P₁)) * ErrorRectangles.U Q B (C.N/(norm C.d*P₂))) := by
      dsimp [U₁,U₂]
      rw [show (A*ErrorRectangles.U Q B (C.N/(norm C.d*P₁)))*(A*ErrorRectangles.U Q B (C.N/(norm C.d*P₂))) =
        A^2 * (ErrorRectangles.U Q B (C.N/(norm C.d*P₁))*ErrorRectangles.U Q B (C.N/(norm C.d*P₂))) by ring,
        Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq (by linarith : 0 ≤ A)]
    calc
      _ ≤ (∑ r ∈ R, ‖∑ u ∈ V₁, ∑ v ∈ V₂, if u ⊔ v = ⊤ then x u * star (y v) * (Q.χ u) r * star ((Q.χ v) r) else 0‖) +
        (∑ r ∈ R, ‖∑ u ∈ V₃, ∑ v ∈ V₄, if u ⊔ v = ⊤ then x u * star (y v) * (Q.χ u) r * star ((Q.χ v) r) else 0‖) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro r hr
          unfold coreBlock
          rw [SupportedPairMask.pair_mask_split C f₁ f₂ (fun u v =>
            x u * star (y v) * (Q.χ u) r * star ((Q.χ v) r))]
          exact norm_add_le _ _
      _ ≤ _ := add_le_add h₁ h₂
      _ = _ := by rw [hsqrt]; ring
  · refine ⟨1,zero_lt_one,?_⟩
    intro C hC
    exact False.elim (hex ⟨C,hC⟩)
end DedekindZetaZeroFree.LargeSieve.Bilinear.ExplicitTerms.SupportedRows

end

end
