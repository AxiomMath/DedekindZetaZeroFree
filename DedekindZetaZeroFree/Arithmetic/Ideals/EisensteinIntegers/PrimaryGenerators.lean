module

public import DedekindZetaZeroFree.Arithmetic.Units.EisensteinUnitsModuloThree

@[expose] public section

namespace DedekindZetaZeroFree.Eisenstein

theorem existsUnique_primaryGenerator (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (A : I3 E) :
    ∃! x : R E, Ideal.span {x} = (A : Ideal (R E)) ∧ red3 E x = 1 := by
  haveI : IsPrincipalIdealRing (R E) := IsCyclotomicExtension.Rat.three_pid E
  classical
  obtain ⟨hA_ne, hA3⟩ := (mem_I3 E (A : Ideal (R E))).mp A.2
  set g : R E := Submodule.IsPrincipal.generator (A : Ideal (R E)) with hg
  have hspan : Ideal.span {g} = (A : Ideal (R E)) :=
    Submodule.IsPrincipal.span_singleton_generator (A : Ideal (R E))
  have hg_ne : g ≠ 0 := by
    intro h0
    refine hA_ne ?_
    rw [← hspan, h0]
    simp
  have hunit : IsUnit (red3 E g) := by
    rw [isUnit_red3_iff_span_sup_m3_eq_top, hspan, hA3]
  obtain ⟨u, hu, huniq⟩ := existsUnique_unit_mul_red3_eq_one E g hunit
  refine ⟨(u : R E) * g, ⟨?_, hu⟩, ?_⟩
  · rw [Ideal.span_singleton_mul_left_unit u.isUnit, hspan]
  · rintro y ⟨hy_span, hy_red⟩
    have hassoc : Associated g y :=
      Ideal.span_singleton_eq_span_singleton.mp (by rw [hspan, hy_span])
    obtain ⟨u', hu'⟩ := hassoc
    have hu'_red : red3 E ((u' : R E) * g) = 1 := by
      rw [mul_comm, hu', hy_red]
    have : u' = u := huniq u' hu'_red
    rw [← hu', this, mul_comm]

noncomputable def primaryGenerator (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (A : I3 E) : R E :=
  Classical.choose (existsUnique_primaryGenerator E A)

theorem primaryGenerator_ne_zero (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (A : I3 E) :
    primaryGenerator E A ≠ 0 := by
  intro h0
  obtain ⟨hspan, -⟩ := (Classical.choose_spec (existsUnique_primaryGenerator E A)).1
  obtain ⟨hA_ne, -⟩ := (mem_I3 E (A : Ideal (R E))).mp A.2
  refine hA_ne ?_
  rw [← hspan, Ideal.span_singleton_eq_bot]
  exact h0

@[simp] theorem span_primaryGenerator (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (A : I3 E) :
    Ideal.span {primaryGenerator E A} = (A : Ideal (R E)) :=
  (Classical.choose_spec (existsUnique_primaryGenerator E A)).1.1

@[simp] theorem red3_primaryGenerator (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (A : I3 E) :
    red3 E (primaryGenerator E A) = 1 :=
  (Classical.choose_spec (existsUnique_primaryGenerator E A)).1.2

@[simp] theorem primaryGenerator_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] :
    primaryGenerator E 1 = 1 := by
  refine ((Classical.choose_spec (existsUnique_primaryGenerator E 1)).2 1 ?_).symm
  exact ⟨by simp, by simp⟩

@[simp] theorem primaryGenerator_mul (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (A B : I3 E) :
    primaryGenerator E (A * B) = primaryGenerator E A * primaryGenerator E B := by
  refine ((Classical.choose_spec (existsUnique_primaryGenerator E (A * B))).2 _ ?_).symm
  refine ⟨?_, ?_⟩
  · rw [← Ideal.span_singleton_mul_span_singleton, span_primaryGenerator, span_primaryGenerator]
    rfl
  · rw [map_mul, red3_primaryGenerator, red3_primaryGenerator, one_mul]

theorem span_mem_I3_of_red3_eq_one (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (x : R E)
    (hx : x ≠ 0) (hx3 : red3 E x = 1) :
    Ideal.span {x} ∈ I3 E := by
  rw [mem_I3]
  refine ⟨?_, ?_⟩
  · intro h
    exact hx (Ideal.span_singleton_eq_bot.mp h)
  · rw [← isUnit_red3_iff_span_sup_m3_eq_top, hx3]
    exact isUnit_one

def primaryPrincipalIdeal (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (x : R E)
    (hx : x ≠ 0) (hx3 : red3 E x = 1) : I3 E :=
  ⟨Ideal.span {x}, span_mem_I3_of_red3_eq_one E x hx hx3⟩

@[simp] theorem primaryGenerator_primaryPrincipalIdeal (E : Type)
    [Field E] [NumberField E] [IsCyclotomicExtension {3} ℚ E]
    (x : R E) (hx : x ≠ 0) (hx3 : red3 E x = 1) :
    primaryGenerator E (primaryPrincipalIdeal E x hx hx3) = x := by
  refine ((Classical.choose_spec
    (existsUnique_primaryGenerator E (primaryPrincipalIdeal E x hx hx3))).2 x ?_).symm
  exact ⟨rfl, hx3⟩

theorem eq_of_span_eq_of_red3_eq (E : Type) [Field E] [NumberField E]
    [IsCyclotomicExtension {3} ℚ E] (x y : R E)
    (hxy : Ideal.span {x} = Ideal.span {y})
    (hx : Ideal.span {x} ≠ ⊥) (hx3 : IsUnit (red3 E x))
    (hxy3 : red3 E x = red3 E y) :
    x = y := by
  obtain ⟨u, hu⟩ :=
    (Ideal.span_singleton_eq_span_singleton.mp hxy).symm
  have hx3y : IsUnit (red3 E y) := by rw [← hxy3]; exact hx3
  have hu_red : red3 E (u : R E) = 1 := by
    have h : red3 E y * red3 E (u : R E) = red3 E y * 1 := by
      rw [mul_one, ← map_mul, hu, hxy3]
    exact (hx3y.mul_right_inj).mp h
  have hu_one : u = 1 := unit_eq_one_of_red3_eq_one E u hu_red
  rw [← hu, hu_one, Units.val_one, mul_one]

end DedekindZetaZeroFree.Eisenstein
