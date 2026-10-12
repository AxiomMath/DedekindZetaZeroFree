module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.CosetSignsAndNorms
public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralRepresentatives
public import ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable {K : Type} [Field K] [NumberField K]

private theorem elementIdeal_mul (D : Data K) (α : Cx D) :
    elementIdeal D α * D.a = Ideal.span {α.val} := by
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change ((elementIdeal D α * D.a : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  rw [FractionalIdeal.coeIdeal_mul, elementIdeal_fractionalImage]
  rw [mul_assoc, inv_mul_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr D.ideal_ne_bot), mul_one]

theorem elementIdeal_ne_bot (D : Data K) (α : Cx D) :
    elementIdeal D α ≠ ⊥ := by
  intro h
  have he := elementIdeal_mul D α
  rw [h, Ideal.bot_mul] at he
  have hz : α.val = 0 := by simpa using he.symm
  exact (mem_Cnonzero_iff D α.val).mp α.property |>.2 hz

theorem elementIdeal_coprime (D : Data K) (α : Cx D) :
    elementIdeal D α ⊔ D.m = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have hα : α.val ∈ elementIdeal D α := by
    have hle : Ideal.span {α.val} ≤ elementIdeal D α := by
      rw [← elementIdeal_mul D α]
      exact Ideal.mul_le_left
    exact hle (Ideal.subset_span (Set.mem_singleton α.val))
  have hm := ((mem_C_iff D α.val).mp ((mem_Cnonzero_iff D α.val).mp α.property).1).2
  have h := (elementIdeal D α ⊔ D.m).sub_mem
    (show α.val ∈ elementIdeal D α ⊔ D.m from Ideal.mem_sup_left hα)
    (show α.val - 1 ∈ elementIdeal D α ⊔ D.m from Ideal.mem_sup_right hm)
  simpa using h

theorem elementIdeal_absNorm (D : Data K) (α : Cx D) :
    (Ideal.absNorm (elementIdeal D α) : ℝ) =
      |(Algebra.norm ℚ (α.val : K) : ℝ)| / (Ideal.absNorm D.a : ℝ) := by
  have ha : (Ideal.absNorm D.a : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr D.ideal_ne_bot)
  apply (eq_div_iff ha).mpr
  rw [← Nat.cast_mul, ← map_mul, elementIdeal_mul, Ideal.absNorm_span_singleton]
  rw [← Algebra.coe_norm_int]
  rw [← Int.cast_natCast, Int.natCast_natAbs]
  push_cast
  rfl

theorem elementIdeal_smul (D : Data K) (u : U K D.m) (α : Cx D) :
    elementIdeal D (u • α) = elementIdeal D α := by
  unfold elementIdeal
  rw [smul_val, Ideal.span_singleton_mul_left_unit u.val.isUnit]

def orbitIdeal (D : Data K) : X D → Ideal (𝓞 K) :=
  Quotient.lift (elementIdeal D) (by
    intro α β h
    obtain ⟨u, hu⟩ := h
    exact hu ▸ elementIdeal_smul D u β)

@[simp] theorem orbitIdeal_orbitMk (D : Data K) (α : Cx D) :
    orbitIdeal D (orbitMk D α) = elementIdeal D α := rfl

theorem orbitIdeal_absNorm (D : Data K) (x : X D) :
    (Ideal.absNorm (orbitIdeal D x) : ℝ) = normWeight D x := by
  induction x using Quotient.inductionOn with
  | h α => exact elementIdeal_absNorm D α

theorem orbitIdeal_rayIdealClass (D : Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some (c⁻¹))
    (x : Xpos D) :
    rayIdealClass K D.m D.modulus_ne_bot (orbitIdeal D x.val) = some c := by
  obtain ⟨x, hx⟩ := x
  induction x using Quotient.inductionOn with
  | h α =>
    change rayIdealClass K D.m D.modulus_ne_bot (elementIdeal D α) = some c
    have hpos : TotallyPositive K α.val := hx
    have hmem := (mem_Cnonzero_iff D α.val).mp α.property
    have hcong := ((mem_C_iff D α.val).mp hmem.1).2
    have hmul := rayIdealClass_mul K D.m D.modulus_ne_bot (elementIdeal D α) D.a
    rw [elementIdeal_mul, rayIdealClass_span K D.m D.modulus_ne_bot α.val hmem.2 hcong hpos,
      hc] at hmul
    rw [rayIdealClass_eq_some K D.m D.modulus_ne_bot (elementIdeal D α)
      (elementIdeal_ne_bot D α) (elementIdeal_coprime D α)] at hmul ⊢
    simp only [Option.bind_some, Option.map_some, Option.some.injEq] at hmul
    apply congrArg some
    exact (mul_inv_eq_iff_eq_mul.mp hmul.symm).trans (one_mul c)

def positiveIdealMap (D : Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some (c⁻¹)) :
    Xpos D → {I : Ideal (𝓞 K) | rayIdealClass K D.m D.modulus_ne_bot I = some c} :=
  fun x => ⟨orbitIdeal D x.val, orbitIdeal_rayIdealClass D c hc x⟩

private theorem positiveIdealMap_surjective (D : Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some c⁻¹) :
    Function.Surjective (positiveIdealMap D c hc) := by
  intro I
  have hIa : rayIdealClass K D.m D.modulus_ne_bot (I.val * D.a) = some 1 := by
    rw [rayIdealClass_mul, I.property, hc]
    simp
  have hn : I.val * D.a ≠ ⊥ := by
    intro h
    have hh := rayIdealClass_eq_none K D.m D.modulus_ne_bot (I.val * D.a) (Or.inl h)
    rw [hIa] at hh
    contradiction
  have hcop : I.val * D.a ⊔ D.m = ⊤ := by
    by_contra h
    have hh := rayIdealClass_eq_none K D.m D.modulus_ne_bot (I.val * D.a) (Or.inr h)
    rw [hIa] at hh
    contradiction
  rw [rayIdealClass_eq_some K D.m D.modulus_ne_bot (I.val * D.a) hn hcop] at hIa
  have hp := (QuotientGroup.eq_one_iff _).mp (Option.some.inj hIa)
  change rayIdealFractionalIdeal K (I.val * D.a) hn ∈
    ClassFieldTheory.rayPrincipalIdealSubgroup (narrowIdealModulus K D.m D.modulus_ne_bot) at hp
  obtain ⟨x, hx, hxI⟩ := (ClassFieldTheory.mem_rayPrincipalIdealSubgroup_iff _ _).mp hp
  have he : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (x : K) =
      ((I.val * D.a : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    simpa [coe_toPrincipalIdeal] using congrArg Units.val hxI
  have hxm : (x : K) ∈ ((I.val * D.a : Ideal (𝓞 K)) : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) := by
    rw [← he]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨α, hα, hαx⟩ := (FractionalIdeal.mem_coeIdeal _).mp hxm
  change (α : K) = (x : K) at hαx
  have hαK : (α : K) ≠ 0 := by
    rw [hαx]
    exact x.ne_zero
  have hux : Units.mk0 (α : K) hαK = x := by
    apply Units.ext
    exact hαx
  have hray := (integralNarrowRayCongruence K D.m D.modulus_ne_bot α hαK).mp (hux ▸ hx)
  have hαa : α ∈ D.a := Ideal.mul_le_right hα
  have hαC : α ∈ C D := (mem_C_iff D α).mpr ⟨hαa, hray.1⟩
  let a : Cx D := ⟨α, (mem_Cnonzero_iff D α).mpr ⟨hαC, NumberField.RingOfIntegers.coe_ne_zero_iff.mp hαK⟩⟩
  let y : Xpos D := ⟨orbitMk D a, hray.2⟩
  refine ⟨y, ?_⟩
  apply Subtype.ext
  change elementIdeal D a = I.val
  apply FractionalIdeal.coeIdeal_injective (K := K)
  change (elementIdeal D a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) = _
  rw [elementIdeal_fractionalImage, FractionalIdeal.coeIdeal_span_singleton]
  change FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (α : K) *
    (D.a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹ = _
  rw [hαx, he, FractionalIdeal.coeIdeal_mul, mul_assoc,
    mul_inv_cancel₀ (FractionalIdeal.coeIdeal_ne_zero.mpr D.ideal_ne_bot), mul_one]

abbrev RealSignVector (K : Type) [Field K] := RealPlaces K → Bool

def representativeSignVector (α : 𝓞 K) : RealSignVector K :=
  fun v => decide (0 < realEmbedding K v (α : K))

theorem representativeSignVector_smul (D : Data K) (u : U K D.m) (α : Cx D) :
    representativeSignVector (u • α).val = representativeSignVector α.val := by
  funext v
  unfold representativeSignVector
  congr 1
  rw [smul_val]
  push_cast
  rw [map_mul]
  exact propext (mul_pos_iff_of_pos_left (u.property.2 (realEmbedding K v)))

def signVector (D : Data K) : X D → RealSignVector K :=
  Quotient.lift (fun α : Cx D => representativeSignVector α.val) (by
    intro α β h
    obtain ⟨u, hu⟩ := h
    exact hu ▸ representativeSignVector_smul D u β)

@[simp] theorem signVector_orbitMk (D : Data K) (α : Cx D) :
    signVector D (orbitMk D α) = representativeSignVector α.val := rfl

private theorem realEmbedding_exists (φ : K →+* ℝ) :
    ∃ v : RealPlaces K, realEmbedding K v = φ := by
  let ψ : K →+* ℂ := Complex.ofRealHom.comp φ
  have hp : NumberField.ComplexEmbedding.IsReal ψ := by
    ext x
    simp [ψ, NumberField.ComplexEmbedding.conjugate]
  let v : RealPlaces K := ⟨NumberField.InfinitePlace.mk ψ, ⟨ψ, hp, rfl⟩⟩
  refine ⟨v, ?_⟩
  ext x
  apply Complex.ofReal_injective
  change ((NumberField.InfinitePlace.embedding_of_isReal v.property) x : ℂ) = _
  rw [NumberField.InfinitePlace.embedding_of_isReal_apply]
  change NumberField.InfinitePlace.embedding (NumberField.InfinitePlace.mk ψ) x = _
  rw [NumberField.InfinitePlace.embedding_mk_eq_of_isReal hp]
  rfl

private theorem associated_rayUnit (D : Data K) (α β : Cx D)
    (hi : Ideal.span {α.val} = Ideal.span {β.val})
    (hs : representativeSignVector α.val = representativeSignVector β.val) :
    ∃ u : U K D.m, u • β = α := by
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hi.symm
  have hαm := ((mem_C_iff D α.val).mp ((mem_Cnonzero_iff D α.val).mp α.property).1).2
  have hβm := ((mem_C_iff D β.val).mp ((mem_Cnonzero_iff D β.val).mp β.property).1).2
  have hum : (u : 𝓞 K) - 1 ∈ D.m := by
    have h := D.m.sub_mem hαm (D.m.mul_mem_left (u : 𝓞 K) hβm)
    rw [← hu] at h
    convert h using 1 <;> ring
  have hup : TotallyPositive K (u : 𝓞 K) := by
    intro φ
    obtain ⟨v, rfl⟩ := realEmbedding_exists φ
    have hv : (0 < realEmbedding K v (α.val : K)) ↔ (0 < realEmbedding K v (β.val : K)) := by
      have h := congrFun hs v
      simpa only [representativeSignVector, decide_eq_decide] using h
    have hn : realEmbedding K v (β.val : K) ≠ 0 := by
      apply (map_ne_zero (realEmbedding K v)).mpr
      exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr ((mem_Cnonzero_iff D β.val).mp β.property).2
    have he : realEmbedding K v (β.val : K) * realEmbedding K v ((u : 𝓞 K) : K) =
        realEmbedding K v (α.val : K) := by
      rw [← map_mul, ← map_mul, hu]
    rcases lt_or_gt_of_ne hn with hb | hb
    · have ha := not_lt.mp (mt hv.mp (not_lt.mpr hb.le))
      have hun : realEmbedding K v ((u : 𝓞 K) : K) ≠ 0 := by
        apply (map_ne_zero (realEmbedding K v)).mpr
        exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr u.ne_zero
      by_contra h
      have hneg : realEmbedding K v ((u : 𝓞 K) : K) < 0 := lt_of_le_of_ne (not_lt.mp h) hun
      have hpos := mul_pos_of_neg_of_neg hb hneg
      rw [he] at hpos
      exact (not_lt.mpr ha) hpos
    · have ha := hv.mpr hb
      nlinarith
  refine ⟨⟨u, hum, hup⟩, ?_⟩
  apply Subtype.ext
  change (u : 𝓞 K) * β.val = α.val
  rw [mul_comm, hu]

theorem signVector_injective_on_fibre (D : Data K) (I : Ideal (𝓞 K)) :
    Function.Injective
      (fun x : {x : X D | orbitIdeal D x = I} => signVector D x.val) := by
  intro x y hs
  apply Subtype.ext
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  change x = y
  revert hx hy hs
  induction x using Quotient.inductionOn with
  | h α =>
    induction y using Quotient.inductionOn with
    | h β =>
      intro hx hy hs
      have hi : elementIdeal D α = elementIdeal D β := hx.trans hy.symm
      have hspan : Ideal.span {α.val} = Ideal.span {β.val} := by
        rw [← elementIdeal_mul D α, ← elementIdeal_mul D β, hi]
      obtain ⟨u, hu⟩ := associated_rayUnit D α β hspan hs
      apply Quotient.sound
      exact ⟨u, hu⟩

private theorem positive_signVector (D : Data K) (x : Xpos D) :
    signVector D x.val = fun _ => true := by
  obtain ⟨x, hx⟩ := x
  induction x using Quotient.inductionOn with
  | h α =>
    have hp : TotallyPositive K α.val := hx
    funext v
    change decide (0 < realEmbedding K v (α.val : K)) = true
    exact decide_eq_true (hp (realEmbedding K v))

theorem positiveIdealMap_bijective (D : Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some (c⁻¹)) :
    Function.Bijective (positiveIdealMap D c hc) := by
  refine ⟨?_, positiveIdealMap_surjective D c hc⟩
  intro x y h
  have hi : orbitIdeal D x.val = orbitIdeal D y.val := congrArg Subtype.val h
  have hs : signVector D x.val = signVector D y.val :=
    (positive_signVector D x).trans (positive_signVector D y).symm
  have he := signVector_injective_on_fibre D (orbitIdeal D y.val)
    (a₁ := ⟨x.val, hi⟩) (a₂ := ⟨y.val, rfl⟩) hs
  exact Subtype.ext (congrArg (fun z : {z : X D | orbitIdeal D z = orbitIdeal D y.val} => z.val) he)

def positiveIdealEquiv (D : Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some (c⁻¹)) :
    Xpos D ≃ {I : Ideal (𝓞 K) | rayIdealClass K D.m D.modulus_ne_bot I = some c} :=
  Equiv.ofBijective (positiveIdealMap D c hc) (positiveIdealMap_bijective D c hc)

@[simp] theorem positiveIdealEquiv_apply_val (D : Data K)
    (c : RayIdealClass K D.m D.modulus_ne_bot)
    (hc : rayIdealClass K D.m D.modulus_ne_bot D.a = some (c⁻¹)) (x : Xpos D) :
    (positiveIdealEquiv D c hc x).val = orbitIdeal D x.val := rfl

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
