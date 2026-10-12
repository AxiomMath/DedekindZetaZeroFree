module

public import DedekindZetaZeroFree.Eisenstein.Induction.HolomorphicSectionsAndResidueGerms
public import DedekindZetaZeroFree.Adeles.Approximation.RationalFlagDensity

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPChamberBruhatTwoCells

open scoped MatrixGroups NumberField

variable (F : Type*) [Field F]

def rationalUnipotent (t : F) : PGL(2, F) :=
  Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![1, t; 0, 1] (by simp [Matrix.det_fin_two]))

def rationalWeyl : PGL(2, F) :=
  Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![0, -1; 1, 0] (by simp [Matrix.det_fin_two]))

def rationalBorel : Subgroup PGL(2, F) :=
  (KPRationalFlag.borel F).map Matrix.ProjGenLinGroup.mk

abbrev RationalQuotient := Quotient (QuotientGroup.rightRel (rationalBorel F))

def rationalCoset (g : PGL(2, F)) : RationalQuotient F :=
  Quotient.mk (QuotientGroup.rightRel (rationalBorel F)) g

def cellIndex : Option F → RationalQuotient F
  | none => rationalCoset F 1
  | some t => rationalCoset F (rationalWeyl F * rationalUnipotent F t)

def cellN (t : F) : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
  !![1, t; 0, 1] (by simp [Matrix.det_fin_two])

def cellW : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero
  !![0, -1; 1, 0] (by simp [Matrix.det_fin_two])

private theorem cell_mem_mk (A : GL (Fin 2) F) :
    Matrix.ProjGenLinGroup.mk A ∈ rationalBorel F ↔ A 1 0 = 0 := by
  constructor
  · rintro ⟨B, hB, he⟩
    obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp he
    have hc := congrArg (fun C : GL (Fin 2) F => C 1 0) hu
    change B 1 0 = 0 at hB
    simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_two, hB] using hc.symm
  · intro hA
    exact ⟨A, hA, rfl⟩

private theorem cell_coset_eq (A B : GL (Fin 2) F) :
    rationalCoset F (Matrix.ProjGenLinGroup.mk A) =
      rationalCoset F (Matrix.ProjGenLinGroup.mk B) ↔ (B * A⁻¹) 1 0 = 0 := by
  change Quotient.mk _ _ = Quotient.mk _ _ ↔ _
  rw [Quotient.eq, QuotientGroup.rightRel_apply, ← map_inv, ← map_mul, cell_mem_mk]

private theorem open_cell_eq (t u : F) :
    cellIndex F (some t) = cellIndex F (some u) ↔ t = u := by
  change rationalCoset F (Matrix.ProjGenLinGroup.mk (cellW F * cellN F t)) =
    rationalCoset F (Matrix.ProjGenLinGroup.mk (cellW F * cellN F u)) ↔ _
  rw [cell_coset_eq]
  simp [cellN, cellW, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
    Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, add_neg_eq_zero]

private theorem closed_ne_open (t : F) : cellIndex F none ≠ cellIndex F (some t) := by
  change rationalCoset F (Matrix.ProjGenLinGroup.mk 1) ≠
    rationalCoset F (Matrix.ProjGenLinGroup.mk (cellW F * cellN F t))
  rw [ne_eq, cell_coset_eq]
  simp [cellN, cellW, Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

private theorem cell_surjective (q : RationalQuotient F) :
    ∃ i, cellIndex F i = q := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective (Quotient.out q)
  have hq : rationalCoset F (Matrix.ProjGenLinGroup.mk A) = q := by
    rw [hA]
    exact Quotient.out_eq q
  suffices ∃ i, cellIndex F i = rationalCoset F (Matrix.ProjGenLinGroup.mk A) by
    simpa [hq] using this
  by_cases hc : A 1 0 = 0
  · refine ⟨none, ?_⟩
    change rationalCoset F (Matrix.ProjGenLinGroup.mk 1) = _
    rw [cell_coset_eq]
    simpa using hc
  · refine ⟨some (A 1 1 / A 1 0), ?_⟩
    change rationalCoset F (Matrix.ProjGenLinGroup.mk
      (cellW F * cellN F (A 1 1 / A 1 0))) = _
    rw [cell_coset_eq]
    simp [cellN, cellW, Matrix.GeneralLinearGroup.coe_mul, Matrix.GeneralLinearGroup.coe_inv,
      Matrix.inv_def, Matrix.adjugate_fin_two, Matrix.det_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring

theorem cellIndex_bijective : Function.Bijective (cellIndex F) := by
  constructor
  · intro i j hij
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some t => exact False.elim ((closed_ne_open F t) hij)
    | some t =>
      cases j with
      | none => exact False.elim ((closed_ne_open F t) hij.symm)
      | some u => exact congrArg some ((open_cell_eq F t u).mp hij)
  · intro q
    exact cell_surjective F q

section Lifts

variable [NumberField F] {G : Type*} [Group G]

abbrev Adeles := NumberField.AdeleRing (𝓞 F) F

def CompatibleUnipotentLift (s : PGL(2, F) →* G)
    (n : Multiplicative (Adeles F) →* G) : Prop :=
  ∀ t : F, s (rationalUnipotent F t) =
    n (Multiplicative.ofAdd (algebraMap F (Adeles F) t))

def ScalarUnipotentInvariant (n : Multiplicative (Adeles F) →* G)
    (fR : G → ℂ) : Prop :=
  ∀ x g, fR (n (Multiplicative.ofAdd x) * g) = fR g

def ScalarRationalBorelInvariant (s : PGL(2, F) →* G) (fR : G → ℂ) : Prop :=
  ∀ b : rationalBorel F, ∀ g, fR (s b * g) = fR g

def rationalTerm (s : PGL(2, F) →* G) (fR : G → ℂ)
    (g : G) (q : RationalQuotient F) : ℂ :=
  fR (s (Quotient.out q) * g)

theorem rationalTerm_eq (s : PGL(2, F) →* G) (fR : G → ℂ)
    (hB : ScalarRationalBorelInvariant F s fR) (g : G) (a : PGL(2, F)) :
    rationalTerm F s fR g (rationalCoset F a) = fR (s a * g) := by
  have he : rationalCoset F (Quotient.out (rationalCoset F a)) = rationalCoset F a :=
    Quotient.out_eq _
  have hb : a * (Quotient.out (rationalCoset F a))⁻¹ ∈ rationalBorel F :=
    QuotientGroup.rightRel_apply.mp (Quotient.exact he)
  have hi := hB ⟨_, hb⟩ (s (Quotient.out (rationalCoset F a)) * g)
  simpa [rationalTerm, map_mul, map_inv, mul_assoc] using hi.symm

theorem open_cell_translate (s : PGL(2, F) →* G)
    (n : Multiplicative (Adeles F) →* G)
    (hcompat : CompatibleUnipotentLift F s n)
    (fR : G → ℂ) (t : F) (x : Adeles F) (g : G) :
    fR (s (rationalWeyl F * rationalUnipotent F t) *
      n (Multiplicative.ofAdd x) * g) =
    fR (s (rationalWeyl F) *
      n (Multiplicative.ofAdd (algebraMap F (Adeles F) t + x)) * g) := by
  rw [map_mul, hcompat t]
  simp only [ofAdd_add, map_mul, mul_assoc]

theorem eisenstein_two_cells (s : PGL(2, F) →* G) (fR : G → ℂ)
    (hB : ScalarRationalBorelInvariant F s fR) (g : G)
    (hsum : KPGlobalEisensteinData.EisensteinSummable
      (fun q : RationalQuotient F => s (Quotient.out q)) fR g) :
    KPGlobalEisensteinData.eisenstein
      (fun q : RationalQuotient F => s (Quotient.out q)) fR g hsum =
    fR g + ∑' t : F, fR (s (rationalWeyl F * rationalUnipotent F t) * g) := by
  let φ : RationalQuotient F → ℂ := rationalTerm F s fR g
  have hφ : Summable φ := hsum.of_norm
  let e : Option F ≃ RationalQuotient F := Equiv.ofBijective _ (cellIndex_bijective F)
  change (∑' q, φ q) = _
  rw [← e.tsum_eq φ]
  let d : (F ⊕ PUnit.{1}) ≃ Option F := (Equiv.optionEquivSumPUnit F).symm
  rw [← d.tsum_eq (fun i => φ (e i))]
  have hd : Summable (fun i => φ (e (d i))) :=
    d.summable_iff.mpr (e.summable_iff.mpr hφ)
  have hl := hd.comp_injective Sum.inl_injective
  have hr := hd.comp_injective Sum.inr_injective
  rw [hl.tsum_sum hr]
  simp only [d, Equiv.optionEquivSumPUnit_symm_inl,
    Equiv.optionEquivSumPUnit_symm_inr]
  rw [tsum_fintype (f := fun _ : PUnit.{1} => φ (e none))]
  simp only [Fintype.sum_unique]
  change (∑' t, rationalTerm F s fR g (cellIndex F (some t))) +
    rationalTerm F s fR g (cellIndex F none) = _
  simp only [cellIndex, rationalTerm_eq F s fR hB g, map_one, one_mul]
  exact add_comm _ _

end Lifts

end DedekindZetaZeroFree.KPChamberBruhatTwoCells

end
