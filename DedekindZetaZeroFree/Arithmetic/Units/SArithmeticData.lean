module

public import ClassFieldTheory.AlgebraicNumberTheory.SUnit.LogLattice
public import ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.Ideal
public import DedekindZetaZeroFree.Arithmetic.Ideals.SIntegerLocalization.GeneratorNorm

@[expose] public section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree

noncomputable section
set_option maxHeartbeats 800000

structure SArithmeticData (F : Type) [Field F] [NumberField F] where
  zeta12 : F
  primitive_zeta12 : IsPrimitiveRoot zeta12 12
  Sf : Finset (HeightOneSpectrum (𝓞 F))
  S₀ : Finset (HeightOneSpectrum (𝓞 F))
  bad_subset : S₀ ⊆ Sf
  modulus : Ideal (𝓞 F)
  modulus_ne_zero : modulus ≠ ⊥
  above_six : ∀ v : HeightOneSpectrum (𝓞 F), (6 : 𝓞 F) ∈ v.asIdeal → v ∈ Sf
  modulus_support : ∀ v : HeightOneSpectrum (𝓞 F), modulus ≤ v.asIdeal → v ∈ Sf

namespace SArithmeticData

variable {F : Type} [Field F] [NumberField F]

abbrev R (A : SArithmeticData F) := (A.Sf : Set (HeightOneSpectrum (𝓞 F))).integer F

abbrev U (A : SArithmeticData F) := (A.Sf : Set (HeightOneSpectrum (𝓞 F))).unit F

def unitEquiv (A : SArithmeticData F) : A.U ≃* A.Rˣ :=
  Set.unitEquivUnitsInteger _ _

abbrev Place (A : SArithmeticData F) := InfinitePlace F ⊕ {v // v ∈ A.Sf}

abbrev Completion (A : SArithmeticData F) (v : A.Place) : Type :=
  match v with
  | Sum.inl w => w.Completion
  | Sum.inr w => w.val.adicCompletion F

instance completionField (A : SArithmeticData F) (v : A.Place) : Field (A.Completion v) := by
  cases v <;> dsimp [Completion] <;> infer_instance

abbrev G (A : SArithmeticData F) :=
  ((w : InfinitePlace F) → w.Completionˣ) ×
    ((v : {v // v ∈ A.Sf}) → (v.val.adicCompletion F)ˣ)

def diagonal (A : SArithmeticData F) : Fˣ →* A.G where
  toFun u := (fun w => Units.map (algebraMap F w.Completion).toMonoidHom u,
    fun v => Units.map (algebraMap F (v.val.adicCompletion F)).toMonoidHom u)
  map_one' := by ext <;> simp
  map_mul' := by intros; ext <;> simp

def norm (A : SArithmeticData F) (x : A.G) : ℝ :=
  (∏ w : InfinitePlace F, ‖(x.1 w : w.Completion)‖ ^ (2 : ℕ)) *
    ∏ v : {v // v ∈ A.Sf}, ‖(x.2 v : v.val.adicCompletion F)‖

def G1 (A : SArithmeticData F) : Subgroup A.G where
  carrier := {x | A.norm x = 1}
  one_mem' := by simp [norm]
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    simpa [norm, norm_mul, mul_pow, Finset.prod_mul_distrib, mul_mul_mul_comm] using
      congrArg₂ (· * ·) hx hy
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    change A.norm x⁻¹ = 1
    change A.norm x = 1 at hx
    simpa only [norm, Prod.fst_inv, Prod.snd_inv, Pi.inv_apply, Units.val_inv_eq_inv_val,
      norm_inv, inv_pow, Finset.prod_inv_distrib, ← mul_inv, inv_one] using
      congrArg Inv.inv hx

def sixthPowers (A : SArithmeticData F) : Subgroup A.G := (powMonoidHom 6).range

abbrev V (A : SArithmeticData F) := A.G ⧸ A.sixthPowers

def unitSixthPowers (A : SArithmeticData F) : Subgroup A.U := (powMonoidHom 6).range

abbrev UnitQuotient (A : SArithmeticData F) := A.U ⧸ A.unitSixthPowers

def E (A : SArithmeticData F) : Subgroup A.V :=
  (A.U.map A.diagonal).map (QuotientGroup.mk' A.sixthPowers)

def Gamma (A : SArithmeticData F) : Subgroup A.G :=
  (A.U.map (powMonoidHom 6)).map A.diagonal

def cS (A : SArithmeticData F) : Ideal (𝓞 F) := ∏ v ∈ A.Sf, v.asIdeal

abbrev Exterior (A : SArithmeticData F) := ExteriorIdeal A.cS

def extendIdeal (A : SArithmeticData F) (I : A.Exterior) : Ideal A.R :=
  Ideal.map (algebraMap (𝓞 F) A.R) I.val

def Generates (A : SArithmeticData F) (I : A.Exterior) (r : A.R) : Prop :=
  r ≠ 0 ∧ Ideal.span {r} = A.extendIdeal I

abbrev exteriorNorm (A : SArithmeticData F) (I : A.Exterior) : ℝ := idealNorm I.val

theorem primitive_sixth_root (A : SArithmeticData F) :
    (primitiveRoots 6 F).Nonempty := by
  exact ⟨A.zeta12 ^ 2, (mem_primitiveRoots (by decide)).2
    (A.primitive_zeta12.pow (by decide) (by decide : 12 = 2 * 6))⟩

theorem complex_place (A : SArithmeticData F) (w : InfinitePlace F) : w.IsComplex := by
  apply InfinitePlace.not_isReal_iff_isComplex.mp
  intro hw
  have hcard := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt
    (by decide : 2 < 12) A.primitive_zeta12
  have hempty : IsEmpty {w : InfinitePlace F // w.IsReal} :=
    Fintype.card_eq_zero_iff.mp hcard
  exact hempty.false ⟨w, hw⟩

theorem zeta12_pow_six (A : SArithmeticData F) : A.zeta12 ^ 6 = -1 :=
  (A.primitive_zeta12.pow (by decide) (by decide : 12 = 6 * 2)).eq_neg_one_of_two_right

theorem cS_ne_zero (A : SArithmeticData F) : A.cS ≠ ⊥ := by
  change (∏ v ∈ A.Sf, v.asIdeal) ≠ 0
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => v.ne_bot)

theorem exterior_iff (A : SArithmeticData F) (I : NonzeroIdeal F) :
    I.val ⊔ A.cS = ⊤ ↔ ∀ v : HeightOneSpectrum (𝓞 F), v ∈ A.Sf →
      I.val ⊔ v.asIdeal = ⊤ := by
  constructor
  · intro h v hv
    apply top_unique
    rw [← h]
    exact sup_le_sup_left
      ((Ideal.prod_le_inf : (∏ w ∈ A.Sf, w.asIdeal) ≤ A.Sf.inf (fun w => w.asIdeal)).trans
        (Finset.inf_le hv)) _
  · intro h
    exact Ideal.sup_prod_eq_top h

theorem extendIdeal_ne_zero (A : SArithmeticData F) (I : A.Exterior) :
    A.extendIdeal I ≠ ⊥ := by
  apply (Ideal.map_eq_bot_iff_of_injective ?_).not.mpr I.property.1
  intro x y h
  apply (IsFractionRing.injective (𝓞 F) F)
  exact congrArg (fun r : A.R => (r : F)) h

def exteriorIdealEquiv (A : SArithmeticData F) :
    A.Exterior ≃ {J : Ideal A.R // J ≠ ⊥} :=
  Equiv.ofBijective (fun I => ⟨A.extendIdeal I, A.extendIdeal_ne_zero I⟩) (by
    constructor
    · intro I J h
      apply Subtype.ext
      have hh := congrArg (fun K : {J : Ideal A.R // J ≠ ⊥} => K.val.under (𝓞 F)) h
      dsimp only [extendIdeal] at hh
      simpa only [SIntegerLocalization.under_map_exterior A.Sf I.val I.property.2,
        SIntegerLocalization.under_map_exterior A.Sf J.val J.property.2] using hh
    · intro J
      let I : A.Exterior := ⟨J.val.under (𝓞 F),
        SIntegerLocalization.under_ne_zero A.Sf J.val J.property,
        SIntegerLocalization.under_exterior A.Sf J.val J.property⟩
      refine ⟨I, Subtype.ext ?_⟩
      letI := SIntegerLocalization.isLocalization_away A.Sf
      exact IsLocalization.map_under (Submonoid.powers (SIntegerLocalization.denominator A.Sf)) _ J.val)

theorem exteriorIdealEquiv_apply (A : SArithmeticData F) (I : A.Exterior) :
    (A.exteriorIdealEquiv I).val = A.extendIdeal I := by
  rfl

theorem norm_diagonal_unit (A : SArithmeticData F) (u : A.U) :
    A.norm (A.diagonal u.val) = 1 := by
  have hp := NumberField.prod_abs_eq_one (Units.ne_zero u.val)
  rw [SUnitGroup.finprod_finitePlace_eq_prod_adicAbv A.Sf u] at hp
  have hinf (w : InfinitePlace F) (x : F) :
      ‖algebraMap F w.Completion x‖ = w x := by
    exact InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)
  have hfin (v : HeightOneSpectrum (𝓞 F)) (x : F) :
      ‖algebraMap F (v.adicCompletion F) x‖ = HeightOneSpectrum.adicAbv F v x := by
    exact FinitePlace.norm_embedding _ _
  change (∏ w : InfinitePlace F, ‖algebraMap F w.Completion (u.val : F)‖ ^ 2) *
    (∏ v : {v // v ∈ A.Sf}, ‖algebraMap F (v.val.adicCompletion F) (u.val : F)‖) = 1
  simp_rw [hinf, hfin]
  simpa only [InfinitePlace.mult,
    InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place _), if_false] using hp

theorem Gamma_le_G1 (A : SArithmeticData F) : A.Gamma ≤ A.G1 := by
  rintro x ⟨y, ⟨u, hu, rfl⟩, rfl⟩
  exact A.norm_diagonal_unit ⟨u ^ 6, A.U.pow_mem hu 6⟩

def Gamma1 (A : SArithmeticData F) : Subgroup A.G1 := A.Gamma.subgroupOf A.G1

theorem generator_norm (A : SArithmeticData F) (I : A.Exterior) (r : A.R)
    (hr : A.Generates I r) (u : Fˣ) (hu : (u : F) = (r : F)) :
    A.norm (A.diagonal u) = A.exteriorNorm I := by
  have hp := SIntegerLocalization.generator_norm A.Sf I.val I.property.1 I.property.2 r hr.1 hr.2
  have hinf (w : InfinitePlace F) (x : F) :
      ‖algebraMap F w.Completion x‖ = w x := by
    exact InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm x)
  have hfin (v : HeightOneSpectrum (𝓞 F)) (x : F) :
      ‖algebraMap F (v.adicCompletion F) x‖ = HeightOneSpectrum.adicAbv F v x := by
    exact FinitePlace.norm_embedding _ _
  change (∏ w : InfinitePlace F, ‖algebraMap F w.Completion (u : F)‖ ^ 2) *
    (∏ v : {v // v ∈ A.Sf}, ‖algebraMap F (v.val.adicCompletion F) (u : F)‖) = _
  simp_rw [hinf, hfin, hu]
  simpa only [InfinitePlace.mult,
    InfinitePlace.not_isReal_iff_isComplex.mpr (A.complex_place _), if_false,
    exteriorNorm, idealNorm] using hp

theorem exterior_norm_mod_twelve (A : SArithmeticData F)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ A.Sf) :
    Ideal.absNorm v.asIdeal % 12 = 1 := by
  have h6 : (6 : 𝓞 F) ∉ v.asIdeal := fun h => hv (A.above_six v h)
  have hp (p : ℕ) (hprime : Nat.Prime p) (hpd : p ∣ 6) :
      ¬ p ∣ Ideal.absNorm v.asIdeal := by
    intro hpn
    obtain ⟨P, hP, hunder, hPv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hprime v.asIdeal hpn
    have heq : P = v.asIdeal := (v.isMaximal.eq_of_le hP.ne_top (Ideal.le_of_dvd hPv)).symm
    have hmem : (p : 𝓞 F) ∈ v.asIdeal := by
      rw [← heq]
      have : (p : ℤ) ∈ P.under ℤ := by
        rw [hunder]
        exact Ideal.subset_span (Set.mem_singleton _)
      change algebraMap ℤ (𝓞 F) (p : ℤ) ∈ P at this
      simpa using this
    apply h6
    obtain ⟨n, hn⟩ := hpd
    have hn' := congrArg (fun k : ℕ => (k : 𝓞 F)) hn
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hn'
    rw [hn']
    exact v.asIdeal.mul_mem_right _ hmem
  have hc : (Ideal.absNorm v.asIdeal).Coprime 12 := by
    rw [Nat.coprime_comm, show 12 = 2 ^ 2 * 3 from rfl, Nat.coprime_mul_iff_left, Nat.coprime_pow_left_iff (by decide)]
    exact ⟨(Nat.prime_two.coprime_iff_not_dvd).mpr (hp 2 Nat.prime_two (by decide)),
      (Nat.prime_three.coprime_iff_not_dvd).mpr (hp 3 Nat.prime_three (by decide))⟩
  have hd := AlgebraicNumberTheory.PowerResidueSymbols.dvd_absNorm_sub_one_of_primitiveRoots
    F v ⟨12, by decide⟩ ⟨A.zeta12, (mem_primitiveRoots (by decide)).mpr A.primitive_zeta12⟩ hc
  have hn := NumberField.HeightOneSpectrum.one_lt_absNorm v
  change 12 ∣ Ideal.absNorm v.asIdeal - 1 at hd
  have hmod := Nat.mod_eq_zero_of_dvd hd
  omega

end SArithmeticData
end
end DedekindZetaZeroFree
