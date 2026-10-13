module

public import DedekindZetaZeroFree.Moments.Probes.Poisson.FixedData

@[expose] public section

namespace DedekindZetaZeroFree.Quantitative.RawFrequencyCount

noncomputable section

open DedekindZetaZeroFree NumberField
open DedekindZetaZeroFree.PrincipalMellinComparison
open DedekindZetaZeroFree.PrincipalMellinComparison.NonprincipalContinuation.DetectorDyads
open scoped Classical

variable {F : Type} [Field F] [NumberField F]
variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

theorem freqOrbit_injective (R : PrincipalMellin.ActualRecipe S η) :
    Function.Injective (fun u : Frequency R =>
      ProbeOrbitNormSum.orbitMk R.A u.val) := by
  intro u v huv
  have h := Quotient.exact huv
  obtain ⟨γ, heq⟩ := MulAction.orbitRel_apply.mp h
  obtain ⟨δ, hδ⟩ := γ.property
  let I : R.A.Exterior := ⟨⊤, top_ne_bot, by simp⟩
  let r := R.probe.coefficients.generator I
  have hr := (R.probe.coefficients.generates I).1
  let m : ThetaReflectionData.Row R.A :=
    ⟨u.val.val * r ^ 6, mul_ne_zero u.val.property (pow_ne_zero _ hr)⟩
  obtain ⟨x, hx, hxuniq⟩ := R.probe.frequencies.factorization m
  have hg : R.probe.allowed.generator I = ThetaReflectionData.rowUnit R.A ⟨r, hr⟩ := by
    apply Units.ext
    exact R.probe.sameGenerator I
  have hu : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A m =
      ThetaReflectionData.rowUnit R.A u.val * R.probe.allowed.generator I ^ 6 *
        γ.val ^ 6 := by
    refine ⟨1, ?_⟩
    rw [hg]
    apply Units.ext
    simp [m, r, ThetaReflectionData.rowUnit]
  have hv : ∃ γ : R.A.U, ThetaReflectionData.rowUnit R.A m =
      ThetaReflectionData.rowUnit R.A v.val * R.probe.allowed.generator I ^ 6 *
        γ.val ^ 6 := by
    refine ⟨δ, ?_⟩
    rw [hg]
    have huu := congrArg (fun x : ThetaReflectionData.Row R.A => (x.val : F)) heq
    have hδF := congrArg (fun x : R.A.U => (x.val : F)) hδ
    apply Units.ext
    simp only [m, ThetaReflectionData.rowUnit, Units.val_mk0, map_mul, map_pow]
    change (u.val.val : F) * (r : F) ^ 6 = (v.val.val : F) * (r : F) ^ 6 * (δ.val : F) ^ 6
    change ((R.A.unitEquiv γ.val : R.A.R) : F) * (v.val.val : F) = (u.val.val : F) at huu
    have hcoe : ((R.A.unitEquiv γ.val : R.A.R) : F) = (γ.val.val : F) := by
      simp [SArithmeticData.unitEquiv, Set.unitEquivUnitsInteger]
    rw [hcoe, ← hδF] at huu
    change (δ.val : F) ^ 6 * (v.val.val : F) = (u.val.val : F) at huu
    rw [← huu]
    ring
  have he : (u, I) = (v, I) := (hxuniq _ hu).trans (hxuniq _ hv).symm
  exact congrArg Prod.fst he

theorem freqOrbit_norm (R : PrincipalMellin.ActualRecipe S η) (u : Frequency R) :
    frequencyNorm R u =
      ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) := by
  unfold frequencyNorm FiniteTransform.exteriorNorm ProbeOrbitNormSum.orbitNorm
  rw [ProbeOrbitNormSum.orbitIdeal_mk]
  change (Nat.card (R.A.R ⧸ Ideal.span {u.val.val}) : ℝ) =
    R.A.exteriorNorm (ProbeOrbitNormSum.principalExterior R.A u.val)
  rw [(ProbeOrbitNormSum.principalExterior_generates R.A u.val).2, R.A.exteriorResidue_card]
  rfl

theorem one_le_frequencyNorm (R : PrincipalMellin.ActualRecipe S η)
    (u : Frequency R) : 1 ≤ frequencyNorm R u := by
  rw [freqOrbit_norm R u]
  exact idealNorm_ge_one _
    (ProbeOrbitNormSum.orbitIdeal R.A (ProbeOrbitNormSum.orbitMk R.A u.val)).property.1

theorem frequency_count_le (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency R | frequencyNorm R u ≤ X}.Finite ∧
      (Set.ncard {u : Frequency R | frequencyNorm R u ≤ X} : ℝ) ≤ K * X := by
  obtain ⟨C, hC0, hCcount⟩ := ProbeExteriorIdealCount.ideal_count_linear (F := F) R.A.cS
  refine ⟨(Nat.card R.A.UnitQuotient : ℝ) * C + 1, by positivity, ?_⟩
  intro X hX
  obtain ⟨hBfin, hBcard⟩ := hCcount X hX
  have hBfin' : {I : R.A.Exterior | R.A.exteriorNorm I ≤ X}.Finite := hBfin
  have hfiber : ∀ I : R.A.Exterior,
      {o : ProbeOrbitNormSum.Orbit R.A | ProbeOrbitNormSum.orbitIdeal R.A o = I}.Finite ∧
      Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
        ProbeOrbitNormSum.orbitIdeal R.A o = I} ≤ Nat.card R.A.UnitQuotient := by
    intro I
    refine ⟨ProbeOrbitNormSum.idealFiber_finite R.A I, ?_⟩
    rw [ProbeOrbitNormSum.idealFiber_card R.A R.classKilled I]
  obtain ⟨hprefin, hprecard⟩ := ProbeExteriorPrincipalIdealFibers.finite_preimage_card_bound
    (ProbeOrbitNormSum.orbitIdeal R.A) (Nat.card R.A.UnitQuotient) hfiber
    {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} hBfin'
  have ht : {o : ProbeOrbitNormSum.Orbit R.A |
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X}.Finite := hprefin
  have hprecard' : Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X} ≤
      Nat.card R.A.UnitQuotient * Set.ncard {I : R.A.Exterior |
        R.A.exteriorNorm I ≤ X} := hprecard
  have hpfin : ((fun u : Frequency R => ProbeOrbitNormSum.orbitMk R.A u.val) ⁻¹'
      {o : ProbeOrbitNormSum.Orbit R.A | ProbeOrbitNormSum.orbitNorm R.A o ≤ X}).Finite :=
    ht.preimage (fun a _ b _ hab => freqOrbit_injective R hab)
  have hfin : {u : Frequency R | frequencyNorm R u ≤ X}.Finite := by
    refine hpfin.subset ?_
    intro u hu
    rw [Set.mem_setOf_eq] at hu
    show ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) ≤ X
    rw [← freqOrbit_norm R u]
    exact hu
  refine ⟨hfin, ?_⟩
  have hinj := Set.ncard_le_ncard_of_injOn
    (fun u : Frequency R => ProbeOrbitNormSum.orbitMk R.A u.val)
    (fun u hu => by
      show ProbeOrbitNormSum.orbitNorm R.A (ProbeOrbitNormSum.orbitMk R.A u.val) ≤ X
      rw [← freqOrbit_norm R u]
      exact hu)
    (fun a _ b _ h => freqOrbit_injective R h) ht
  have hnat : Nat.card {o : ProbeOrbitNormSum.Orbit R.A //
      ProbeOrbitNormSum.orbitNorm R.A o ≤ X} =
      Set.ncard {o : ProbeOrbitNormSum.Orbit R.A |
        ProbeOrbitNormSum.orbitNorm R.A o ≤ X} := Nat.card_coe_set_eq _
  have hBcard' : (Set.ncard {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} : ℝ) ≤ C * X := by
    rw [← Nat.card_coe_set_eq]
    exact hBcard
  rw [hnat] at hprecard'
  calc
    (Set.ncard {u : Frequency R | frequencyNorm R u ≤ X} : ℝ)
        ≤ (Set.ncard {o : ProbeOrbitNormSum.Orbit R.A |
            ProbeOrbitNormSum.orbitNorm R.A o ≤ X} : ℝ) := by
          exact_mod_cast hinj
    _ ≤ (Nat.card R.A.UnitQuotient : ℝ) *
          (Set.ncard {I : R.A.Exterior | R.A.exteriorNorm I ≤ X} : ℝ) := by
          exact_mod_cast hprecard'
    _ ≤ (Nat.card R.A.UnitQuotient : ℝ) * (C * X) :=
          mul_le_mul_of_nonneg_left hBcard' (Nat.cast_nonneg _)
    _ ≤ ((Nat.card R.A.UnitQuotient : ℝ) * C + 1) * X := by
          nlinarith [hC0, Nat.cast_nonneg (α := ℝ) (Nat.card R.A.UnitQuotient), hX]

theorem frequency_count_lt (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency R | frequencyNorm R u < X}.Finite ∧
      (Set.ncard {u : Frequency R | frequencyNorm R u < X} : ℝ) ≤ K * X := by
  obtain ⟨K, hK, h⟩ := frequency_count_le R
  refine ⟨K, hK, fun X hX => ?_⟩
  obtain ⟨hfin, hcard⟩ := h X hX
  have hsub : {u : Frequency R | frequencyNorm R u < X} ⊆
      {u : Frequency R | frequencyNorm R u ≤ X} :=
    fun _ hu => le_of_lt (Set.mem_setOf_eq.mp hu)
  exact ⟨hfin.subset hsub,
    (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfin)).trans hcard⟩

theorem frequency_dyad_count (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℝ, 1 ≤ U →
      {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U}.Finite ∧
      (Set.ncard {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} : ℝ)
        ≤ K * U := by
  obtain ⟨K, hK, h⟩ := frequency_count_lt R
  refine ⟨2 * K, by positivity, fun U hU => ?_⟩
  obtain ⟨hfin, hcard⟩ := h (2 * U) (by linarith)
  have hsub : {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} ⊆
      {u : Frequency R | frequencyNorm R u < 2 * U} := fun _ hu => hu.2
  refine ⟨hfin.subset hsub, ?_⟩
  calc (Set.ncard {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} : ℝ)
      ≤ (Set.ncard {u : Frequency R | frequencyNorm R u < 2 * U} : ℝ) :=
        Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfin)
    _ ≤ K * (2 * U) := hcard
    _ = 2 * K * U := by ring

theorem frequency_dyad_count_nonprincipal (R : PrincipalMellin.ActualRecipe S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℝ, 1 ≤ U →
      {u : Frequency R | u ≠ principalFrequency R ∧
        U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U}.Finite ∧
      (Set.ncard {u : Frequency R | u ≠ principalFrequency R ∧
        U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} : ℝ) ≤ K * U := by
  obtain ⟨K, hK, h⟩ := frequency_dyad_count R
  refine ⟨K, hK, fun U hU => ?_⟩
  obtain ⟨hfin, hcard⟩ := h U hU
  have hsub : {u : Frequency R | u ≠ principalFrequency R ∧
        U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} ⊆
      {u : Frequency R | U ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * U} :=
    fun _ hu => hu.2
  exact ⟨hfin.subset hsub, (Nat.cast_le.mpr (Set.ncard_le_ncard hsub hfin)).trans hcard⟩

theorem exists_dyad (R : PrincipalMellin.ActualRecipe S η) (u : Frequency R) :
    ∃ k : ℕ, (2 : ℝ) ^ k ≤ frequencyNorm R u ∧ frequencyNorm R u < 2 * (2 : ℝ) ^ k := by
  obtain ⟨n, h1, h2⟩ := exists_nat_pow_near (one_le_frequencyNorm R u)
    (one_lt_two : (1 : ℝ) < 2)
  exact ⟨n, h1, by rw [pow_succ] at h2; linarith⟩

theorem principal_unique (R : PrincipalMellin.ActualRecipe S η) :
    {u : Frequency R | (u.val.val : R.A.R) = 1} = {principalFrequency R} := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    apply Subtype.ext
    apply Subtype.ext
    exact h
  · rintro rfl
    rfl

theorem frequencyNorm_principal (R : PrincipalMellin.ActualRecipe S η) :
    frequencyNorm R (principalFrequency R) = 1 :=
  frequencyNorm_principalFrequency R

theorem fixedData_frequency_count_lt (D : FixedData S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ X : ℝ, 1 ≤ X →
      {u : Frequency D.recipe | frequencyNorm D.recipe u < X}.Finite ∧
      (Set.ncard {u : Frequency D.recipe | frequencyNorm D.recipe u < X} : ℝ) ≤ K * X :=
  frequency_count_lt D.recipe

theorem fixedData_frequency_dyad_count (D : FixedData S η) :
    ∃ K : ℝ, 0 < K ∧ ∀ U : ℝ, 1 ≤ U →
      {u : Frequency D.recipe |
        U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U}.Finite ∧
      (Set.ncard {u : Frequency D.recipe |
        U ≤ frequencyNorm D.recipe u ∧ frequencyNorm D.recipe u < 2 * U} : ℝ) ≤ K * U :=
  frequency_dyad_count D.recipe

end

end DedekindZetaZeroFree.Quantitative.RawFrequencyCount
