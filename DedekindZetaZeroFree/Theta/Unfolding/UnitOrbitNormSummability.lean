module

public import DedekindZetaZeroFree.Arithmetic.Units.PrincipalizingRayCharacterContext
public import DedekindZetaZeroFree.Arithmetic.Ideals.Counting.NormSeries
public import DedekindZetaZeroFree.Adeles.Quotients.ExteriorNormRadialSection

@[expose] public section

open scoped NumberField Classical nonZeroDivisors

noncomputable section
set_option maxHeartbeats 800000

namespace DedekindZetaZeroFree.ProbeOrbitNormSum

variable {F : Type} [Field F] [NumberField F]

abbrev Nonzero (A : SArithmeticData F) := {h : A.R // h ≠ 0}

abbrev Gamma (A : SArithmeticData F) := A.unitSixthPowers

instance gammaMulAction (A : SArithmeticData F) : MulAction (Gamma A) (Nonzero A) where
  smul γ h := ⟨(A.unitEquiv γ.val : A.R) * h.val,
    mul_ne_zero (Units.ne_zero _) h.property⟩
  one_smul h := by
    apply Subtype.ext
    change (A.unitEquiv (1 : A.U) : A.R) * h.val = h.val
    simp
  mul_smul γ δ h := by
    apply Subtype.ext
    change (A.unitEquiv (γ.val * δ.val) : A.R) * h.val =
      (A.unitEquiv γ.val : A.R) * ((A.unitEquiv δ.val : A.R) * h.val)
    simp [mul_assoc]

abbrev Orbit (A : SArithmeticData F) :=
  Quotient (MulAction.orbitRel (Gamma A) (Nonzero A))

def orbitMk (A : SArithmeticData F) (h : Nonzero A) : Orbit A :=
  Quotient.mk _ h

def principalExterior (A : SArithmeticData F) (h : Nonzero A) : A.Exterior :=
  A.exteriorIdealEquiv.symm
    ⟨Ideal.span {h.val}, Ideal.span_singleton_eq_bot.not.mpr h.property⟩

theorem principalExterior_generates (A : SArithmeticData F) (h : Nonzero A) :
    A.Generates (principalExterior A h) h.val := by
  refine ⟨h.property, ?_⟩
  rw [← A.exteriorIdealEquiv_apply]
  simp [principalExterior]

theorem principalExterior_orbitRel (A : SArithmeticData F) (h k : Nonzero A)
    (hhk : MulAction.orbitRel (Gamma A) (Nonzero A) h k) :
    principalExterior A h = principalExterior A k := by
  obtain ⟨γ, rfl⟩ := (MulAction.orbitRel_apply).mp hhk
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  simp only [principalExterior, Equiv.apply_symm_apply]
  change Ideal.span {(A.unitEquiv γ.val : A.R) * k.val} = Ideal.span {k.val}
  exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _

def orbitIdeal (A : SArithmeticData F) : Orbit A → A.Exterior :=
  Quotient.lift (principalExterior A) (principalExterior_orbitRel A)

theorem orbitIdeal_mk (A : SArithmeticData F) (h : Nonzero A) :
    orbitIdeal A (orbitMk A h) = principalExterior A h := rfl

def orbitNorm (A : SArithmeticData F) (o : Orbit A) : ℝ :=
  A.exteriorNorm (orbitIdeal A o)

theorem orbitNorm_eq_snorm (A : SArithmeticData F) (h : Nonzero A)
    (a : Fˣ) (ha : (a : F) = (h.val : F)) :
    orbitNorm A (orbitMk A h) = A.norm (A.diagonal a) := by
  exact (A.generator_norm _ _ (principalExterior_generates A h) a ha).symm

theorem orbitNorm_pos (A : SArithmeticData F) (o : Orbit A) :
    0 < orbitNorm A o := by
  exact A.exteriorNorm_pos _

abbrev IdealFiber (A : SArithmeticData F) (I : A.Exterior) :=
  {o : Orbit A // orbitIdeal A o = I}

theorem unitQuotient_finite (A : SArithmeticData F) : Finite A.UnitQuotient := by
  letI := SArithmeticData.sunitSixthPowerQuotient_finite F A
  exact Finite.of_equiv (PowerQuotient A.Rˣ 6)
    (LocalFieldTheory.nthPowerQuotientEquivOfMulEquiv A.U A.Rˣ 6 A.unitEquiv).symm.toEquiv

theorem orbitIdeal_surjective (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) : Function.Surjective (orbitIdeal A) := by
  letI := hCl
  intro I
  have hunit : IsUnit (A.extendIdeal I : FractionalIdeal A.R⁰ F) := by
    have hO : IsUnit (I.val : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F) :=
      isUnit_iff_ne_zero.mpr (FractionalIdeal.coeIdeal_ne_zero.mpr I.property.1)
    change IsUnit ((Ideal.map (algebraMap (NumberField.RingOfIntegers F) A.R) I.val : Ideal A.R) :
      FractionalIdeal A.R⁰ F)
    rw [← FractionalIdeal.extendedHom_coeIdeal_eq_map (K := F) F A.R I.val]
    exact hO.map (FractionalIdeal.extendedHom F A.R)
  letI := ClassGroup.isPrincipal_of_isUnit_coeIdeal (A.extendIdeal I) hunit
  let r := Submodule.IsPrincipal.generator (A.extendIdeal I)
  have hr : Ideal.span {r} = A.extendIdeal I := Ideal.span_singleton_generator _
  have hr0 : r ≠ 0 := by
    intro hz
    exact A.extendIdeal_ne_zero I (by simpa [hz] using hr.symm)
  refine ⟨orbitMk A ⟨r, hr0⟩, ?_⟩
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  simpa [orbitIdeal_mk, principalExterior, A.exteriorIdealEquiv_apply] using hr

 def unitTranslate (A : SArithmeticData F) (h : Nonzero A) (u : A.U) : Nonzero A :=
  ⟨(A.unitEquiv u : A.R) * h.val, mul_ne_zero (Units.ne_zero _) h.property⟩

 theorem translateIdeal (A : SArithmeticData F) (h : Nonzero A) (u : A.U) :
    principalExterior A (unitTranslate A h u) = principalExterior A h := by
  apply A.exteriorIdealEquiv.injective
  apply Subtype.ext
  simp only [principalExterior, Equiv.apply_symm_apply]
  exact Ideal.span_singleton_mul_left_unit (Units.isUnit _) _

 theorem translate_eq_iff (A : SArithmeticData F) (h : Nonzero A) (u v : A.U) :
    orbitMk A (unitTranslate A h u) = orbitMk A (unitTranslate A h v) ↔
      QuotientGroup.mk' A.unitSixthPowers u = QuotientGroup.mk' A.unitSixthPowers v := by
  unfold orbitMk
  rw [Quotient.eq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, Quotient.eq,
    QuotientGroup.leftRel_apply, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨γ, hγ⟩
    have huv : u = γ.val * v := by
      apply A.unitEquiv.injective
      apply Units.ext
      apply mul_right_cancel₀ h.property
      change (A.unitEquiv u : A.R) * h.val = _
      have hh := (congrArg Subtype.val hγ).symm
      change (A.unitEquiv u : A.R) * h.val = (A.unitEquiv γ.val : A.R) * ((A.unitEquiv v : A.R) * h.val) at hh
      simpa [map_mul, mul_assoc] using hh
    rw [huv]
    simpa [mul_comm, mul_left_comm, mul_assoc] using A.unitSixthPowers.inv_mem γ.property
  · intro huv
    have hγ : u * v⁻¹ ∈ A.unitSixthPowers := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using A.unitSixthPowers.inv_mem huv
    refine ⟨⟨u * v⁻¹, hγ⟩, ?_⟩
    apply Subtype.ext
    change (A.unitEquiv (u * v⁻¹) : A.R) * ((A.unitEquiv v : A.R) * h.val) = _
    simp [map_mul, mul_assoc, unitTranslate]

 theorem sameIdeal_translate (A : SArithmeticData F) (h k : Nonzero A)
    (hk : principalExterior A k = principalExterior A h) :
    ∃ u : A.U, unitTranslate A h u = k := by
  have hspan : Ideal.span {h.val} = Ideal.span {k.val} := by
    have he := congrArg (fun I => (A.exteriorIdealEquiv I).val) hk.symm
    simpa [principalExterior] using he
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan
  refine ⟨A.unitEquiv.symm u, ?_⟩
  apply Subtype.ext
  simpa [unitTranslate, mul_comm] using hu

 def fiberEquiv (A : SArithmeticData F) (h : Nonzero A) :
    A.UnitQuotient ≃ IdealFiber A (principalExterior A h) := by
  let f : A.UnitQuotient → IdealFiber A (principalExterior A h) :=
    Quotient.lift (fun u => ⟨orbitMk A (unitTranslate A h u), translateIdeal A h u⟩)
      (by
        intro u v huv
        apply Subtype.ext
        exact (translate_eq_iff A h u v).mpr (Quotient.sound huv))
  apply Equiv.ofBijective f
  constructor
  · intro u v
    induction u using Quotient.inductionOn with | h u =>
      induction v using Quotient.inductionOn with | h v =>
        intro he
        exact (translate_eq_iff A h u v).mp (congrArg Subtype.val he)
  · rintro ⟨o, ho⟩
    induction o using Quotient.inductionOn with | h k =>
      obtain ⟨u, hu⟩ := sameIdeal_translate A h k ho
      refine ⟨QuotientGroup.mk' A.unitSixthPowers u, ?_⟩
      apply Subtype.ext
      change orbitMk A (unitTranslate A h u) = orbitMk A k
      rw [hu]

theorem idealFiber_equiv_unitQuotient (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (I : A.Exterior) :
    Nonempty (IdealFiber A I ≃ A.UnitQuotient) := by
  obtain ⟨o, ho⟩ := orbitIdeal_surjective A hCl I
  induction o using Quotient.inductionOn with | h h =>
    subst I
    exact ⟨(fiberEquiv A h).symm⟩

theorem idealFiber_finite (A : SArithmeticData F) (I : A.Exterior) :
    Finite (IdealFiber A I) := by
  letI := unitQuotient_finite A
  by_cases he : Nonempty (IdealFiber A I)
  · obtain ⟨o, ho⟩ := he.some
    induction o using Quotient.inductionOn with | h h =>
      subst I
      exact Finite.of_equiv A.UnitQuotient (fiberEquiv A h)
  · letI : IsEmpty (IdealFiber A I) := not_nonempty_iff.mp he
    infer_instance

theorem idealFiber_card (A : SArithmeticData F)
    (hCl : Subsingleton (ClassGroup A.R)) (I : A.Exterior) :
    Nat.card (IdealFiber A I) = Nat.card A.UnitQuotient := by
  exact Nat.card_congr (idealFiber_equiv_unitQuotient A hCl I).some

theorem indices_countable (A : SArithmeticData F) :
    Countable (Nonzero A) ∧ Countable A.U ∧ Countable (Gamma A) ∧
      Countable A.UnitQuotient ∧ Countable (Orbit A) ∧ Countable A.Exterior ∧
      Countable (Orbit A × Gamma A) ∧ ∀ I : A.Exterior, Countable (IdealFiber A I) := by
  letI : Countable F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  letI : Countable A.R := inferInstance
  letI : Countable (NonzeroIdeal F) := by
    apply Set.countable_univ_iff.mp
    have hc := Set.countable_iUnion (fun n : ℕ => (normBoundedIdeals_finite F n).countable)
    apply hc.mono
    intro I _
    exact Set.mem_iUnion.mpr ⟨Ideal.absNorm I.val, show idealNorm I.val ≤ (Ideal.absNorm I.val : ℝ) from le_rfl⟩
  letI : Countable A.Exterior := by
    let e : A.Exterior → NonzeroIdeal F := fun I => ⟨I.val, I.property.1⟩
    have he : Function.Injective e := by
      intro I J h
      apply Subtype.ext
      exact congrArg (fun x : NonzeroIdeal F => x.val) h
    exact @Function.Injective.countable A.Exterior (NonzeroIdeal F) inferInstance e he
  letI : Countable Fˣ := Units.val_injective.countable
  letI : Countable A.U := inferInstance
  letI : Countable (Nonzero A) := inferInstance
  letI : Countable (Gamma A) := inferInstance
  letI : Countable A.UnitQuotient := (unitQuotient_finite A).to_countable
  letI : Countable (Orbit A) := inferInstance
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, fun _ => inferInstance⟩

def IsRepresentativeSection (A : SArithmeticData F) (ρ : Orbit A → Nonzero A) : Prop :=
  Function.RightInverse ρ (orbitMk A)

def sectionMultiply (A : SArithmeticData F) (ρ : Orbit A → Nonzero A)
    (p : Orbit A × Gamma A) : Nonzero A :=
  p.2 • ρ p.1

theorem gamma_action_free (A : SArithmeticData F) (h : Nonzero A)
    (γ δ : Gamma A) (heq : γ • h = δ • h) : γ = δ := by
  apply Subtype.ext
  apply A.unitEquiv.injective
  apply Units.ext
  exact mul_right_cancel₀ h.property (congrArg Subtype.val heq)

theorem sectionMultiply_bijective (A : SArithmeticData F) (ρ : Orbit A → Nonzero A)
    (hρ : IsRepresentativeSection A ρ) : Function.Bijective (sectionMultiply A ρ) := by
  constructor
  · rintro ⟨o, γ⟩ ⟨p, δ⟩ heq
    have hop : o = p := by
      have hγ : orbitMk A (γ • ρ o) = orbitMk A (ρ o) :=
        Quotient.sound (MulAction.orbitRel_apply.mpr ⟨γ, rfl⟩)
      have hδ : orbitMk A (δ • ρ p) = orbitMk A (ρ p) :=
        Quotient.sound (MulAction.orbitRel_apply.mpr ⟨δ, rfl⟩)
      rw [hρ o] at hγ
      rw [hρ p] at hδ
      exact hγ.symm.trans ((congrArg (orbitMk A) heq).trans hδ)
    subst p
    exact Prod.ext rfl (gamma_action_free A (ρ o) γ δ heq)
  · intro h
    have hh : orbitMk A h = orbitMk A (ρ (orbitMk A h)) := (hρ _).symm
    obtain ⟨γ, hγ⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hh)
    exact ⟨(orbitMk A h, γ), hγ⟩

def normPowerSum (A : SArithmeticData F) (σ : ℝ) : ℝ :=
  ∑' o : Orbit A, (orbitNorm A o) ^ (-σ)

private theorem exterior_summable (A : SArithmeticData F) (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun I : A.Exterior => A.exteriorNorm I ^ (-σ)) := by
  let e : A.Exterior → NonzeroIdeal F := fun I => ⟨I.val, I.property.1⟩
  have he : Function.Injective e := by
    intro I J h
    apply Subtype.ext
    exact congrArg (fun x : NonzeroIdeal F => x.val) h
  have hs := (ideal_norm_rpow_summable F σ hσ).comp_injective he
  exact hs

private theorem fiber_card_le (A : SArithmeticData F) (I : A.Exterior) :
    Nat.card (IdealFiber A I) ≤ Nat.card A.UnitQuotient := by
  by_cases he : Nonempty (IdealFiber A I)
  · obtain ⟨o, ho⟩ := he.some
    induction o using Quotient.inductionOn with | h h =>
      subst I
      exact (Nat.card_congr (fiberEquiv A h)).ge
  · letI : IsEmpty (IdealFiber A I) := not_nonempty_iff.mp he
    simp

private theorem fiberSum (A : SArithmeticData F) (σ : ℝ) (I : A.Exterior) :
    (∑' o : IdealFiber A I, orbitNorm A o.val ^ (-σ)) =
      (Nat.card (IdealFiber A I) : ℝ) * A.exteriorNorm I ^ (-σ) := by
  letI := idealFiber_finite A I
  letI := Fintype.ofFinite (IdealFiber A I)
  have he (o : IdealFiber A I) : orbitNorm A o.val = A.exteriorNorm I := by
    unfold orbitNorm
    rw [o.property]
  simp_rw [he]
  rw [tsum_fintype]
  simp [Nat.card_eq_fintype_card, nsmul_eq_mul]

theorem orbit_norm_rpow_summable (A : SArithmeticData F) (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun o : Orbit A => (orbitNorm A o) ^ (-σ)) := by
  let f : (Σ I : A.Exterior, IdealFiber A I) → ℝ :=
    fun p => orbitNorm A p.2.val ^ (-σ)
  have hf : Summable f := by
    apply (summable_sigma_of_nonneg (fun p => Real.rpow_nonneg (orbitNorm_pos A _).le _)).mpr
    constructor
    · intro I
      letI := idealFiber_finite A I
      exact summable_of_finite_support (Set.toFinite _)
    · simp only [f, fiberSum]
      apply Summable.of_nonneg_of_le (f := fun I : A.Exterior =>
        (Nat.card A.UnitQuotient : ℝ) * A.exteriorNorm I ^ (-σ))
        (fun I => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (A.exteriorNorm_pos I).le _))
        (fun I => mul_le_mul_of_nonneg_right (by exact_mod_cast fiber_card_le A I)
          (Real.rpow_nonneg (A.exteriorNorm_pos I).le _))
      exact (exterior_summable A σ hσ).mul_left (Nat.card A.UnitQuotient : ℝ)
  exact (Equiv.sigmaFiberEquiv (orbitIdeal A)).summable_iff.mp hf

end DedekindZetaZeroFree.ProbeOrbitNormSum

end
