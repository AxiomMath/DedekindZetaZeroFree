module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.RepresentationsAndFixedLevels

@[expose] public section

namespace DedekindZetaZeroFree.CuspidalFiniteCosetForm

variable {G V : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup V] [Module ℂ V]

def coefficient (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V) (v : V) : G → ℂ :=
  fun g => ℓ (ρ g v)

abbrev LeftCosets (U : CompactOpenLevel G) :=
  Quotient (MulAction.orbitRel (U.toOpenSubgroup : Subgroup G) G)

def cosetMk (U : CompactOpenLevel G) (g : G) : LeftCosets U :=
  Quotient.mk _ g

def FixesFunctional (ρ : Representation ℂ G V) (U : CompactOpenLevel G)
    (ℓ : Module.Dual ℂ V) : Prop :=
  ∀ u ∈ U.toOpenSubgroup, ∀ v : V, ℓ (ρ u v) = ℓ v

noncomputable def descendedCoefficient (ρ : Representation ℂ G V)
    (ℓ : Module.Dual ℂ V) (U : CompactOpenLevel G) (v : V) : LeftCosets U → ℂ :=
  fun q => coefficient ρ ℓ v q.out

noncomputable def form (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (v w : V) : ℂ :=
  ∑ᶠ q : LeftCosets U,
    descendedCoefficient ρ ℓ U v q * star (descendedCoefficient ρ ℓ U w q)

theorem exists_fixing_level [IsTopologicalGroup G]
    (hBasis : ∀ J : OpenSubgroup G, ∃ U : CompactOpenLevel G,
      U.toOpenSubgroup ≤ J)
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (hℓ : SmoothVector ρ.dual ℓ) :
    ∃ U : CompactOpenLevel G, FixesFunctional ρ U ℓ := by
  rcases hℓ with ⟨J, hJ⟩
  rcases hBasis J with ⟨U, hUJ⟩
  refine ⟨U, fun u hu v => ?_⟩
  have h := congrArg (fun f : Module.Dual ℂ V => f v)
    (hJ u⁻¹ (J.inv_mem (hUJ hu)))
  simpa [Representation.dual, Module.Dual.transpose_apply] using h

theorem descendedCoefficient_eq (ρ : Representation ℂ G V)
    (ℓ : Module.Dual ℂ V) (U : CompactOpenLevel G)
    (hU : FixesFunctional ρ U ℓ) (v : V) (q : LeftCosets U)
    (g : G) (hg : cosetMk U g = q) :
    descendedCoefficient ρ ℓ U v q = coefficient ρ ℓ v g := by
  have he : cosetMk U q.out = cosetMk U g := (Quotient.out_eq q).trans hg.symm
  rcases Quotient.exact he with ⟨u, hu⟩
  change (u : G) * g = q.out at hu
  simp only [descendedCoefficient, coefficient, ← hu, map_mul, Module.End.mul_apply]
  exact hU u u.property (ρ g v)

theorem descendedCoefficient_finite_support [IsTopologicalGroup G] [T2Space G]
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (hU : FixesFunctional ρ U ℓ)
    (v : V) (hc : HasCompactSupport (coefficient ρ ℓ v)) :
    (Function.support (descendedCoefficient ρ ℓ U v)).Finite := by
  have hlc : IsLocallyConstant (cosetMk U) := by
    apply (IsLocallyConstant.iff_exists_open _).2
    intro g
    refine ⟨(fun u : G => u * g) '' (U.toOpenSubgroup : Set G),
      isOpenMap_mul_right g _ U.toOpenSubgroup.isOpen, ⟨1, U.toOpenSubgroup.one_mem, by simp⟩, ?_⟩
    rintro x ⟨u, hu, rfl⟩
    exact Quotient.sound ⟨⟨u, hu⟩, rfl⟩
  letI : CompactSpace (tsupport (coefficient ρ ℓ v)) := isCompact_iff_compactSpace.mp hc.isCompact
  have hf := (hlc.comp_continuous
    (continuous_subtype_val : Continuous (fun x : tsupport (coefficient ρ ℓ v) => (x : G)))).range_finite
  apply hf.subset
  intro q hq
  refine ⟨⟨q.out, ?_⟩, Quotient.out_eq q⟩
  apply subset_closure
  exact hq

private theorem pair_finite [IsTopologicalGroup G] [T2Space G]
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (hU : FixesFunctional ρ U ℓ)
    (hc : ∀ v : V, HasCompactSupport (coefficient ρ ℓ v)) (v w : V) :
    (Function.support (fun q => descendedCoefficient ρ ℓ U v q *
      star (descendedCoefficient ρ ℓ U w q))).Finite := by
  apply (descendedCoefficient_finite_support ρ ℓ U hU v (hc v)).subset
  intro q hq
  exact fun hz => hq (by simp [hz])

private theorem form_add_left [IsTopologicalGroup G] [T2Space G]
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (hU : FixesFunctional ρ U ℓ)
    (hc : ∀ v : V, HasCompactSupport (coefficient ρ ℓ v)) (v₁ v₂ w : V) :
    form ρ ℓ U (v₁ + v₂) w = form ρ ℓ U v₁ w + form ρ ℓ U v₂ w := by
  unfold form
  simp only [descendedCoefficient, coefficient, map_add, add_mul]
  exact finsum_add_distrib (pair_finite ρ ℓ U hU hc v₁ w) (pair_finite ρ ℓ U hU hc v₂ w)

private theorem form_smul_left (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (a : ℂ) (v w : V) :
    form ρ ℓ U (a • v) w = a * form ρ ℓ U v w := by
  unfold form
  simp only [descendedCoefficient, coefficient, map_smul, smul_eq_mul, mul_assoc]
  exact (mul_finsum _ _).symm

private theorem form_hermitian (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (v w : V) :
    form ρ ℓ U v w = star (form ρ ℓ U w v) := by
  unfold form
  change _ = (starAddEquiv : ℂ ≃+ ℂ) _
  rw [AddEquiv.map_finsum]
  apply finsum_congr
  intro q
  simp [mul_comm]

def rightCosetEquiv (U : CompactOpenLevel G) (g : G) : LeftCosets U ≃ LeftCosets U where
  toFun := Quotient.map (fun x => x * g) (by
    rintro a b ⟨u, hu⟩
    refine ⟨u, ?_⟩
    change (u : G) * (b * g) = a * g
    change (u : G) * b = a at hu
    rw [← mul_assoc, hu])
  invFun := Quotient.map (fun x => x * g⁻¹) (by
    rintro a b ⟨u, hu⟩
    refine ⟨u, ?_⟩
    change (u : G) * (b * g⁻¹) = a * g⁻¹
    change (u : G) * b = a at hu
    rw [← mul_assoc, hu])
  left_inv q := by induction q using Quotient.inductionOn; simp [mul_assoc]
  right_inv q := by induction q using Quotient.inductionOn; simp [mul_assoc]

private theorem form_invariant (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (hU : FixesFunctional ρ U ℓ) (g : G) (v w : V) :
    form ρ ℓ U (ρ g v) (ρ g w) = form ρ ℓ U v w := by
  have he (v : V) (q : LeftCosets U) : descendedCoefficient ρ ℓ U (ρ g v) q =
      descendedCoefficient ρ ℓ U v (rightCosetEquiv U g q) := by
    rw [descendedCoefficient_eq ρ ℓ U hU v _ (q.out * g)]
    · simp [descendedCoefficient, coefficient, map_mul, Module.End.mul_apply]
    · exact congrArg (rightCosetEquiv U g) (Quotient.out_eq q)
  unfold form
  simp_rw [he]
  exact finsum_comp_equiv (rightCosetEquiv U g)
    (f := fun q => descendedCoefficient ρ ℓ U v q * star (descendedCoefficient ρ ℓ U w q))

private theorem coefficient_separates (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) (v : V) (hv : v ≠ 0) :
    ∃ g : G, coefficient ρ ℓ v g ≠ 0 := by
  let K : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {v | ∀ g : G, coefficient ρ ℓ v g = 0}
          zero_mem' := by simp [coefficient]
          add_mem' := by intro x y hx hy g; simp [coefficient] at *; simp [hx g, hy g]
          smul_mem' := by intro a x hx g; simp [coefficient] at *; simp [hx g] }
      apply_mem_toSubmodule := by
        intro g x hx h
        simpa [coefficient, map_mul, Module.End.mul_apply] using hx (h * g) }
  have hK : K = ⊥ := by
    rcases eq_bot_or_eq_top K with h | h
    · exact h
    · exfalso
      apply hℓ
      ext x
      have hx : x ∈ K := by rw [h]; trivial
      simpa [coefficient] using hx 1
  by_contra hn
  have hx : v ∈ K := by
    change ∀ g, coefficient ρ ℓ v g = 0
    simpa using hn
  rw [hK] at hx
  exact hv hx

private theorem diagonal_sum [IsTopologicalGroup G] [T2Space G]
    (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V)
    (U : CompactOpenLevel G) (hU : FixesFunctional ρ U ℓ)
    (v : V) (hc : HasCompactSupport (coefficient ρ ℓ v)) :
    form ρ ℓ U v v =
      ((∑ q ∈ (descendedCoefficient_finite_support ρ ℓ U hU v hc).toFinset,
        Complex.normSq (descendedCoefficient ρ ℓ U v q)) : ℝ) := by
  classical
  unfold form
  rw [finsum_eq_sum_of_support_subset _ (s :=
    (descendedCoefficient_finite_support ρ ℓ U hU v hc).toFinset)]
  · rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro q hq
    exact Complex.mul_conj _
  · intro q hq
    apply (descendedCoefficient_finite_support ρ ℓ U hU v hc).mem_toFinset.mpr
    exact fun hz => hq (by simp [hz])

theorem unitarization [IsTopologicalGroup G] [T2Space G]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (hρ : SmoothRepresentation ρ)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0)
    (U : CompactOpenLevel G) (hU : FixesFunctional ρ U ℓ)
    (hc : ∀ v : V, HasCompactSupport (coefficient ρ ℓ v)) :
    (∀ v : V, (Function.support (descendedCoefficient ρ ℓ U v)).Finite) ∧
    (∀ v₁ v₂ w : V, form ρ ℓ U (v₁ + v₂) w =
      form ρ ℓ U v₁ w + form ρ ℓ U v₂ w) ∧
    (∀ (a : ℂ) (v w : V), form ρ ℓ U (a • v) w = a * form ρ ℓ U v w) ∧
    (∀ v w₁ w₂ : V, form ρ ℓ U v (w₁ + w₂) =
      form ρ ℓ U v w₁ + form ρ ℓ U v w₂) ∧
    (∀ (a : ℂ) (v w : V), form ρ ℓ U v (a • w) =
      star a * form ρ ℓ U v w) ∧
    (∀ v w : V, form ρ ℓ U v w = star (form ρ ℓ U w v)) ∧
    (∀ v : V, (form ρ ℓ U v v).im = 0 ∧ 0 ≤ (form ρ ℓ U v v).re) ∧
    (∀ v : V, v ≠ 0 → 0 < (form ρ ℓ U v v).re) ∧
    (∀ (g : G) (v w : V), form ρ ℓ U (ρ g v) (ρ g w) = form ρ ℓ U v w) ∧
    (∀ w : V, ∃ L : Module.Dual ℂ V,
      (∀ v : V, L v = form ρ ℓ U v w) ∧ SmoothVector ρ.dual L) := by
  classical
  have hadd := form_add_left ρ ℓ U hU hc
  have hsmul := form_smul_left ρ ℓ U
  have hherm := form_hermitian ρ ℓ U
  have hinv := form_invariant ρ ℓ U hU
  have hnonneg (v : V) : (form ρ ℓ U v v).im = 0 ∧ 0 ≤ (form ρ ℓ U v v).re := by
    rw [diagonal_sum ρ ℓ U hU v (hc v)]
    simp only [Complex.ofReal_im, Complex.ofReal_re]
    exact ⟨trivial, Finset.sum_nonneg (fun q hq => Complex.normSq_nonneg _)⟩
  have hpos (v : V) (hv : v ≠ 0) : 0 < (form ρ ℓ U v v).re := by
    rcases coefficient_separates ρ ℓ hℓ v hv with ⟨g, hg⟩
    have hq : descendedCoefficient ρ ℓ U v (cosetMk U g) ≠ 0 := by
      rwa [descendedCoefficient_eq ρ ℓ U hU v _ g rfl]
    rw [diagonal_sum ρ ℓ U hU v (hc v), Complex.ofReal_re]
    apply Finset.sum_pos'
    · intro q hq; exact Complex.normSq_nonneg _
    · exact ⟨cosetMk U g,
        (descendedCoefficient_finite_support ρ ℓ U hU v (hc v)).mem_toFinset.mpr hq,
        Complex.normSq_pos.mpr hq⟩
  refine ⟨fun v => descendedCoefficient_finite_support ρ ℓ U hU v (hc v),
    hadd, hsmul, ?_, ?_, hherm, hnonneg, hpos, hinv, ?_⟩
  · intro v w₁ w₂
    rw [hherm, hadd, star_add]
    rw [← hherm v w₁, ← hherm v w₂]
  · intro a v w
    rw [hherm, hsmul, star_mul, ← hherm v w, mul_comm]
  · intro w
    let L : Module.Dual ℂ V :=
      { toFun := fun v => form ρ ℓ U v w
        map_add' := fun v₁ v₂ => hadd v₁ v₂ w
        map_smul' := fun a v => hsmul a v w }
    refine ⟨L, fun v => rfl, ?_⟩
    rcases hρ w with ⟨J, hJ⟩
    refine ⟨J, fun j hj => ?_⟩
    ext v
    change form ρ ℓ U (ρ j⁻¹ v) w = form ρ ℓ U v w
    have hw := hJ j⁻¹ (J.inv_mem hj)
    calc
      form ρ ℓ U (ρ j⁻¹ v) w = form ρ ℓ U (ρ j⁻¹ v) (ρ j⁻¹ w) := by rw [hw]
      _ = form ρ ℓ U v w := hinv j⁻¹ v w

end DedekindZetaZeroFree.CuspidalFiniteCosetForm
