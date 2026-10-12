module

public import DedekindZetaZeroFree.Theta.Unfolding.AdditiveFourierExtraction

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.ThetaExpansion.BranchCoordinateSeries
open MomentSources ThetaBranch ThetaPhaseSeparation
open scoped NumberField Classical
open IsDedekindDomain UniqueFactorizationMonoid
variable {F : Type} [Field F] [NumberField F]

abbrev BranchCoordinateIndex (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) :=
  (b : Branch A G m D) × Coordinates A G m D b

def branchCoordinateSummand (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (Z : ℝ) (i : BranchCoordinateIndex A G m D) : ℂ :=
  exactCoefficient A G U σ ψ m D i.1 i.2 *
    (L (coordinateRepresentative A G U m D i.1 i.2))⁻¹ *
    H (ThetaReflectionData.frequencyClass A (coordinateFrequency A G U m D i.1 i.2))
      (Z * ThetaReflectionData.frequencyNorm A (coordinateFrequency A G U m D i.1 i.2))

def branchCoordinateSeries (A : SArithmeticData F) (G : AllowedRecipe A)
    (U : UnitRepresentatives A) (σ : F →+* ℂ)
    (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : Fˣ →* ℂ) (H : A.V → ℝ → ℂ) (m : ThetaReflectionData.Row A)
    (D : RowFactorization A G m) (Z : ℝ) : ℂ :=
  ∑' i : BranchCoordinateIndex A G m D, branchCoordinateSummand A G U σ ψ L H m D Z i

def branchCoordinateIndexMap (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) :
    BranchCoordinateIndex A G m D → RMSeparatedExpansion.Index A D.h :=
  fun i => (⟨freeze A G m D i.1 i.2, rfl⟩, ⟨i.2.c, i.2.c_squarefree⟩)

theorem branchCoordinateIndexMap_injective (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) :
    Function.Injective (branchCoordinateIndexMap A G m D) := by
  intro i j hij
  have hf : i.1.f = j.1.f := congrArg (fun k => k.1.val.f) hij
  have he : i.2.epsilon = j.2.epsilon := congrArg (fun k => k.1.val.epsilon) hij
  have ha : i.2.a = j.2.a := congrArg (fun k => k.1.val.a) hij
  have hn : i.2.n = j.2.n := congrArg (fun k => k.1.val.n) hij
  have hc : i.2.c = j.2.c := congrArg (fun k => k.2.val) hij
  rcases i with ⟨b, v⟩
  rcases j with ⟨b', v'⟩
  have hb : b = b' := by cases b; cases b'; simp_all
  subst b'
  have hv : v = v' := by cases v; cases v'; simp_all
  subst v'
  rfl

theorem branchCoordinateSummand_norm_summable_of_separated
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (hrec : SquarefreeGeneratorReciprocity A G σ) (H : A.V → ℝ → ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (Z : ℝ)
    (hs : Summable (fun i : RMSeparatedExpansion.Index A D.h =>
      ‖RMSeparatedExpansion.summand A G U σ ψ L H i.1.val D.d i.2 Z‖)) :
    Summable (fun i : BranchCoordinateIndex A G m D =>
      ‖branchCoordinateSummand A G U σ ψ L H m D Z i‖) := by
  have hs' := hs.comp_injective (branchCoordinateIndexMap_injective A G m D)
  apply hs'.congr
  intro i
  exact congrArg norm (RMSeparatedExpansion.coordinate_summand_exact_squarefree
    A G U σ ψ hψ L hL hrec H m D i.1 i.2 Z).symm

private theorem order_mul (p : HeightOneSpectrum (𝓞 F)) (x y : Fˣ) :
    order p (x * y) = order p x + order p y := by
  have hx : p.valuation F (x : F) ≠ 0 := (map_ne_zero (p.valuation F)).mpr x.ne_zero
  have hy : p.valuation F (y : F) ≠ 0 := (map_ne_zero (p.valuation F)).mpr y.ne_zero
  simp only [order, Units.val_mul, map_mul, WithZero.log_mul hx hy]
  omega
private theorem order_U (A : SArithmeticData F) (u : A.U)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∉ A.Sf) : order p u.val = 0 := by
  simp only [order, u.property p hp, WithZero.log_one, neg_zero]
private theorem exp_zero (p : HeightOneSpectrum (𝓞 F)) (I J : Ideal (𝓞 F))
    (hp : p ∈ support I) (hIJ : I ⊔ J = ⊤) : idealPrimeExponent p.asIdeal J = 0 := by
  apply Multiset.count_eq_zero.mpr
  intro hj
  have hi : p.asIdeal ∈ normalizedFactors I := by
    have hh : p.asIdeal ∈ (normalizedFactors I).toFinset := Finset.mem_preimage.mp hp
    exact Multiset.mem_toFinset.mp hh
  have hI : I ≤ p.asIdeal := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hi)
  have hJ : J ≤ p.asIdeal := Ideal.dvd_iff_le.mp (dvd_of_mem_normalizedFactors hj)
  have : (⊤ : Ideal (𝓞 F)) ≤ p.asIdeal := by rw [← hIJ]; exact sup_le hI hJ
  exact p.isPrime.ne_top (top_le_iff.mp this)
private theorem rowIndex_eq_of_mem (A : SArithmeticData F) (G : AllowedRecipe A)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (p : HeightOneSpectrum (𝓞 F)) (hp : p ∈ support D.h.val) :
    rowIndex A m p = ⟨idealPrimeExponent p.asIdeal D.h.val % 6, Nat.mod_lt _ (by decide)⟩ := by
  have hv : order p (ThetaReflectionData.rowUnit A m) = (idealPrimeExponent p.asIdeal D.h.val : ℤ) := by
    rw [D.row_eq, order_mul, order_U A D.epsilon p (support_outside A D.h p hp), zero_add,
      generator_order A G D.rowIdeal ⟨p, support_outside A D.h p hp⟩, D.factorization]
    simp only [idealPrimeExponent, normalizedFactors_mul D.h.property.1 D.d.property.1,
      Multiset.count_add]
    rw [show (normalizedFactors D.d.val).count p.asIdeal = 0 from exp_zero p D.h.val D.d.val hp D.coprime]
    simp
  apply Fin.ext
  simp only [rowIndex, hv]
  omega

theorem branch_coordinate_series_eq_expansion
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (L : Fˣ →* ℂ) (hL : ∀ x, ‖L x‖ = 1)
    (hrec : SquarefreeGeneratorReciprocity A G σ) (H : A.V → ℝ → ℂ)
    (m : ThetaReflectionData.Row A) (D : RowFactorization A G m) (Z : ℝ)
    (hsum : Summable fun i : BranchCoordinateIndex A G m D =>
      ‖branchCoordinateSummand A G U σ ψ L H m D Z i‖) :
    branchCoordinateSeries A G U σ ψ L H m D Z =
      RMSeparatedExpansion.expansion A G U σ ψ L H D.h D.d Z := by
  let Φ := branchCoordinateIndexMap A G m D
  let f : RMSeparatedExpansion.Index A D.h → ℂ :=
    fun j => RMSeparatedExpansion.summand A G U σ ψ L H j.1.val D.d j.2 Z
  let g : BranchCoordinateIndex A G m D → ℂ := fun i => f (Φ i)
  have hterm : ∀ i, g i = branchCoordinateSummand A G U σ ψ L H m D Z i := fun i =>
    (RMSeparatedExpansion.coordinate_summand_exact_squarefree A G U σ ψ hψ L hL hrec H m D i.1 i.2 Z).symm
  have hsupp : Function.support f ⊆ Set.range (fun x : Function.support g => Φ x.val) := by
    intro j hj
    obtain ⟨⟨T, hT⟩, c⟩ := j
    let cc : A.Exterior := c.val
    have hsc : separatedCoefficient A G U σ ψ L T D.d cc ≠ 0 := by
      intro h0
      exact hj (by simp only [f, RMSeparatedExpansion.summand, cc, h0, zero_mul])
    have hmask : D.d.val ⊔ (T.h.val * T.n.val) = ⊤ ∧ cc.val ⊔ T.f.val = ⊤ ∧ D.d.val ⊔ cc.val = ⊤ := by
      by_contra hcon
      exact hsc (by rw [RMSeparatedExpansion.separatedCoefficient_support, if_neg hcon])
    obtain ⟨hm1, hm2, hm3⟩ := hmask
    have hcop : (cc.val * T.n.val) ⊔ (D.d.val * T.f.val) = ⊤ := by
      have hnd : IsCoprime T.n.val D.d.val := Ideal.isCoprime_iff_sup_eq.mpr (by
        rw [sup_comm]
        have hle : D.d.val ⊔ (T.h.val * T.n.val) ≤ D.d.val ⊔ T.n.val :=
          sup_le_sup_left (Ideal.mul_le_right : T.h.val * T.n.val ≤ T.n.val) D.d.val
        rw [hm1] at hle
        exact le_antisymm le_top hle)
      have hcd : IsCoprime cc.val D.d.val := Ideal.isCoprime_iff_sup_eq.mpr (by rw [sup_comm]; exact hm3)
      have hcf : IsCoprime cc.val T.f.val := Ideal.isCoprime_iff_sup_eq.mpr hm2
      have hnf : IsCoprime T.n.val T.f.val := Ideal.isCoprime_iff_sup_eq.mpr T.n_f_coprime
      exact Ideal.isCoprime_iff_sup_eq.mp ((hcd.mul_right hcf).mul_left (hnd.mul_right hnf))
    have hdiv : T.f.val ∣ idealRadical D.h.val := by
      rw [← congrArg (fun h : A.Exterior => idealRadical h.val) hT]
      exact T.f_divides_radical
    have hmand : ∀ p ∈ support D.h.val, rowIndex A m p ≠ 0 → p ∈ support T.f.val := by
      intro p hp hr
      have hp' : p ∈ support T.h.val := by rw [congrArg (fun h : A.Exterior => support h.val) hT]; exact hp
      refine T.mandatory p hp' ?_
      intro hz
      apply hr
      have h1 : idealPrimeExponent p.asIdeal D.h.val = idealPrimeExponent p.asIdeal T.h.val := by rw [hT]
      apply Fin.ext
      rw [rowIndex_eq_of_mem A G m D p hp]
      simp only [Fin.val_zero, h1, hz]
    let b₀ : Branch A G m D := ⟨T.f, T.f_squarefree, hdiv, hmand⟩
    let v₀ : Coordinates A G m D b₀ :=
      ⟨T.epsilon, T.a, cc, T.n, T.a_supported, T.a_exponents, c.property, hcop⟩
    have hΦj : Φ ⟨b₀, v₀⟩ = (⟨T, hT⟩, c) := by
      refine Prod.ext ?_ ?_
      · apply Subtype.ext
        change freeze A G m D b₀ v₀ = T
        have ht : D.h = T.h := hT.symm
        cases T
        dsimp [freeze, b₀, v₀] at *
        subst ht
        rfl
      · exact Subtype.ext rfl
    refine ⟨⟨⟨b₀, v₀⟩, ?_⟩, hΦj⟩
    change f (Φ ⟨b₀, v₀⟩) ≠ 0
    simpa only [Function.mem_support, hΦj] using hj
  have hmain : (∑' j : RMSeparatedExpansion.Index A D.h, f j) = ∑' i : BranchCoordinateIndex A G m D, g i :=
    tsum_eq_tsum_of_ne_zero_bij (f := f) (g := g) (fun x : Function.support g => Φ x.val)
      (fun x y hxy => Subtype.ext (branchCoordinateIndexMap_injective A G m D hxy)) hsupp (fun _ => rfl)
  change (∑' i, branchCoordinateSummand A G U σ ψ L H m D Z i) = ∑' j, f j
  rw [← tsum_congr hterm]
  exact hmain.symm

variable {S : SArithmeticData F} {η : RayClassCharacter F S.modulus}

def sourceFrequencyCharacter (R : PrincipalMellin.ActualRecipe S η)
    (_ψ : ∀ p : ExteriorPrime R.A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : R.A.UnitQuotient → Fˣ →* ℂ)
    (hsource : PrincipalMellinSource.SourceCharacterCompatibility R _ψ L)
    (v : R.A.UnitQuotient) : ThetaReflectionData.Frequency R.A →* ℂ :=
  QuotientGroup.lift _ (L v) (by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨ε, rfl⟩ := QuotientGroup.mk'_surjective R.A.unitSixthPowers v
    have hone : L (QuotientGroup.mk ε) u = 1 := by
      rw [hsource.2]
      have hc : R.A.correctionLS R.probe.correction.Λ R.probe.correction.G
          R.probe.correction.η_id (R.A.diagonal u) = 1 := R.probe.correction.theta_unit ⟨u, hu⟩
      have hh : R.A.H_S (R.A.diagonal ε.val) (R.A.diagonal u) = 1 :=
        R.A.H_S_sunit_isotropy ε ⟨u, hu⟩
      simp [hc, hh]
    change L (QuotientGroup.mk ε) (u ^ 6) = 1
    rw [map_pow, hone, one_pow])

@[simp] theorem sourceFrequencyCharacter_mk (R : PrincipalMellin.ActualRecipe S η)
    (ψ : ∀ p : ExteriorPrime R.A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : R.A.UnitQuotient → Fˣ →* ℂ)
    (hsource : PrincipalMellinSource.SourceCharacterCompatibility R ψ L)
    (v : R.A.UnitQuotient) (x : Fˣ) :
    sourceFrequencyCharacter R ψ L hsource v (QuotientGroup.mk x) = L v x := rfl

set_option maxHeartbeats 800000 in
theorem branchFrequency_hasSum_iff_coordinates
    {E : Type*} [AddCommMonoid E] [TopologicalSpace E] (P : ℂ → E) (hP : P 0 = 0)
    (A : SArithmeticData F) (G : AllowedRecipe A) (U : UnitRepresentatives A)
    (σ : F →+* ℂ) (ψ : ∀ p : ExteriorPrime A, AddChar (DHCubic.Residue F p.val) ℂ)
    (hψ : ∀ p, (ψ p).IsPrimitive) (m : ThetaReflectionData.Row A) (D : RowFactorization A G m)
    (K : ThetaReflectionData.Frequency A → ℂ) (s : E) :
    HasSum (fun i : Branch A G m D × ThetaReflectionData.Frequency A =>
      P (branchFrequencyCoefficient A G σ ψ m D i.1 i.2 * K i.2)) s ↔
    HasSum (fun i : BranchCoordinateIndex A G m D =>
      P (exactCoefficient A G U σ ψ m D i.1 i.2 * K (coordinateFrequency A G U m D i.1 i.2))) s := by
  let f := fun i : Branch A G m D × ThetaReflectionData.Frequency A =>
    P (branchFrequencyCoefficient A G σ ψ m D i.1 i.2 * K i.2)
  let g := fun i : BranchCoordinateIndex A G m D =>
    P (exactCoefficient A G U σ ψ m D i.1 i.2 * K (coordinateFrequency A G U m D i.1 i.2))
  have hfg (i : BranchCoordinateIndex A G m D) : f (i.1, coordinateFrequency A G U m D i.1 i.2) = g i := by
    dsimp [f, g]
    rw [branch_frequency_coefficient_exact A G U σ ψ hψ m D i.1 i.2]
  have hsupp (i : Branch A G m D × ThetaReflectionData.Frequency A) (hf : f i ≠ 0) : Supported A G m D i.1 i.2 := by
    by_contra hn
    apply hf
    simp [f, branchCoefficient_zero_outside A G σ ψ hψ m D i.1 i.2 hn, hP]
  let e : Function.support g → Branch A G m D × ThetaReflectionData.Frequency A :=
    fun i => (i.val.1, coordinateFrequency A G U m D i.val.1 i.val.2)
  apply hasSum_iff_hasSum_of_ne_zero_bij e
  · intro i j hij
    have hb : i.val.1 = j.val.1 := congrArg Prod.fst hij
    have hv := congrArg Prod.snd hij
    apply Subtype.ext
    rcases i with ⟨⟨b, v⟩, hi⟩
    rcases j with ⟨⟨b', v'⟩, hj⟩
    dsimp at hb
    subst b'
    dsimp [e] at hv
    have hf : f (b, coordinateFrequency A G U m D b v) ≠ 0 := by rw [hfg ⟨b, v⟩]; exact hi
    have h := (coordinates_unique A G U m D b (coordinateFrequency A G U m D b v)).mp
      (hsupp (b, coordinateFrequency A G U m D b v) hf)
    have he : v = v' := h.unique rfl hv.symm
    subst v'
    rfl
  · intro i hi
    obtain ⟨v, hv, _⟩ := (coordinates_unique A G U m D i.1 i.2).mp (hsupp i hi)
    refine ⟨⟨⟨i.1, v⟩, ?_⟩, ?_⟩
    · change g ⟨i.1, v⟩ ≠ 0
      rw [← hfg, hv]
      exact hi
    · exact Prod.ext rfl hv
  · intro i
    exact hfg i.val

set_option maxHeartbeats 800000 in

theorem branchCoordinateSeries_eq_frequencySeries (R : PrincipalMellin.ActualRecipe S η)
    (ψ : ∀ p : ExteriorPrime R.A, AddChar (DHCubic.Residue F p.val) ℂ)
    (L : R.A.UnitQuotient → Fˣ →* ℂ) (hψ : ∀ p, (ψ p).IsPrimitive)
    (hsource : PrincipalMellinSource.SourceCharacterCompatibility R ψ L)
    (H : R.A.V → ℝ → ℂ) (v : R.A.UnitQuotient) (m : ThetaReflectionData.Row R.A)
    (D : RowFactorization R.A R.probe.allowed m) (Z : ℝ)
    (hs : Summable (fun i : BranchCoordinateIndex R.A R.probe.allowed m D =>
      ‖branchCoordinateSummand R.A R.probe.allowed R.probe.unitReps R.σ ψ (L v) H m D Z i‖)) :
    (Summable fun ν : ThetaReflectionData.Frequency R.A =>
      ‖exteriorFrequencyCoefficient R.A R.probe.allowed R.σ ψ m D ν *
        (sourceFrequencyCharacter R ψ L hsource v ν)⁻¹ *
        H (ThetaReflectionData.frequencyClass R.A ν) (Z * ThetaReflectionData.frequencyNorm R.A ν)‖) ∧
    branchCoordinateSeries R.A R.probe.allowed R.probe.unitReps R.σ ψ (L v) H m D Z =
      ∑' ν : ThetaReflectionData.Frequency R.A,
        exteriorFrequencyCoefficient R.A R.probe.allowed R.σ ψ m D ν *
          (sourceFrequencyCharacter R ψ L hsource v ν)⁻¹ *
          H (ThetaReflectionData.frequencyClass R.A ν) (Z * ThetaReflectionData.frequencyNorm R.A ν) := by
  let A := R.A
  let G := R.probe.allowed
  let U := R.probe.unitReps
  let K : ThetaReflectionData.Frequency A → ℂ := fun ν =>
    (sourceFrequencyCharacter R ψ L hsource v ν)⁻¹ * H (ThetaReflectionData.frequencyClass A ν) (Z * ThetaReflectionData.frequencyNorm A ν)
  let f := fun i : Branch A G m D × ThetaReflectionData.Frequency A => branchFrequencyCoefficient A G R.σ ψ m D i.1 i.2 * K i.2
  let g := fun i : BranchCoordinateIndex A G m D => exactCoefficient A G U R.σ ψ m D i.1 i.2 * K (coordinateFrequency A G U m D i.1 i.2)
  have hg (i : BranchCoordinateIndex A G m D) : g i = branchCoordinateSummand A G U R.σ ψ (L v) H m D Z i := by
    dsimp [g, K, branchCoordinateSummand, coordinateFrequency]
    rw [sourceFrequencyCharacter_mk]
    exact (mul_assoc _ _ _).symm
  have hgs : Summable g := hs.of_norm.congr (fun i => (hg i).symm)
  have hfs : Summable f := ((branchFrequency_hasSum_iff_coordinates id rfl A G U R.σ ψ hψ m D K _).mpr hgs.hasSum).summable
  have heq : (∑' i, g i) = ∑' i, f i := ((branchFrequency_hasSum_iff_coordinates id rfl A G U R.σ ψ hψ m D K _).mpr hgs.hasSum).tsum_eq.symm
  letI := branches_finite A G m D
  letI : Fintype (Branch A G m D) := Fintype.ofFinite _
  have hsum (ν : ThetaReflectionData.Frequency A) : (∑' b : Branch A G m D, f (b, ν)) = exteriorFrequencyCoefficient A G R.σ ψ m D ν * K ν := by
    rw [tsum_fintype]
    dsimp [f]
    rw [← Finset.sum_mul, sum_branches_frequency]
  have hex : Summable (fun ν => exteriorFrequencyCoefficient A G R.σ ψ m D ν * K ν) := hfs.prod_symm.prod.congr hsum
  refine ⟨hex.norm.congr (fun ν => ?_), ?_⟩
  · dsimp [K]
    rw [mul_assoc]
  · change (∑' i, branchCoordinateSummand A G U R.σ ψ (L v) H m D Z i) = _
    rw [← tsum_congr hg, heq]
    calc
      (∑' i, f i) = ∑' i : ThetaReflectionData.Frequency A × Branch A G m D, f i.swap :=
        (Equiv.prodComm (ThetaReflectionData.Frequency A) (Branch A G m D)).tsum_eq f |>.symm
      _ = ∑' ν, ∑' b, f (b, ν) := hfs.prod_symm.tsum_prod
      _ = ∑' ν, exteriorFrequencyCoefficient A G R.σ ψ m D ν * K ν := tsum_congr hsum
      _ = _ := by apply tsum_congr; intro ν; exact (mul_assoc _ _ _).symm

end DedekindZetaZeroFree.ThetaExpansion.BranchCoordinateSeries

end
