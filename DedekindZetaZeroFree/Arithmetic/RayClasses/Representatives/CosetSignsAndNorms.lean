module

public import DedekindZetaZeroFree.Arithmetic.RayClasses.Representatives.IntegralIdealClasses

@[expose] public section

noncomputable section

open scoped NumberField Classical

namespace DedekindZetaZeroFree.AbelianQuotient.RayCoset

variable (K : Type) [Field K] [NumberField K]

abbrev RealPlaces := {v : NumberField.InfinitePlace K // v.IsReal}

def realEmbedding (v : RealPlaces K) : K →+* ℝ :=
  NumberField.InfinitePlace.embedding_of_isReal v.property

def TotallyPositive (α : 𝓞 K) : Prop :=
  ∀ φ : K →+* ℝ, 0 < φ (α : K)

structure Data where
  m : Ideal (𝓞 K)
  modulus_ne_bot : m ≠ ⊥
  a : Ideal (𝓞 K)
  ideal_ne_bot : a ≠ ⊥
  coprime : a ⊔ m = ⊤
  b : 𝓞 K
  basepoint_mem : b ∈ a
  basepoint_congruent_one : b - 1 ∈ m

def IsRayUnit (m : Ideal (𝓞 K)) (u : (𝓞 K)ˣ) : Prop :=
  (u : 𝓞 K) - 1 ∈ m ∧ TotallyPositive K (u : 𝓞 K)

theorem isRayUnit_one (m : Ideal (𝓞 K)) : IsRayUnit K m 1 := by
  constructor
  · simp
  · intro φ
    simp

theorem isRayUnit_mul (m : Ideal (𝓞 K)) (u v : (𝓞 K)ˣ)
    (hu : IsRayUnit K m u) (hv : IsRayUnit K m v) :
    IsRayUnit K m (u * v) := by
  constructor
  · change (u : 𝓞 K) * (v : 𝓞 K) - 1 ∈ m
    have h := m.add_mem (m.mul_mem_left (u : 𝓞 K) hv.1) hu.1
    convert h using 1 <;> ring
  · intro φ
    simpa only [Units.val_mul, map_mul] using mul_pos (hu.2 φ) (hv.2 φ)

theorem isRayUnit_inv (m : Ideal (𝓞 K)) (u : (𝓞 K)ˣ)
    (hu : IsRayUnit K m u) : IsRayUnit K m u⁻¹ := by
  constructor
  · have h := m.neg_mem (m.mul_mem_left (↑u⁻¹ : 𝓞 K) hu.1)
    convert h using 1
    rw [mul_sub, Units.inv_mul, mul_one]
    ring
  · intro φ
    have hprod : φ ((↑u⁻¹ : 𝓞 K) : K) * φ ((↑u : 𝓞 K) : K) = 1 := by
      rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
    have hp := hu.2 φ
    nlinarith

def positiveRayUnits (m : Ideal (𝓞 K)) : Subgroup (𝓞 K)ˣ where
  carrier := IsRayUnit K m
  one_mem' := isRayUnit_one K m
  mul_mem' := fun hu hv => isRayUnit_mul K m _ _ hu hv
  inv_mem' := fun hu => isRayUnit_inv K m _ hu

abbrev U (m : Ideal (𝓞 K)) := positiveRayUnits K m

variable {K}

def C (D : Data K) : Set (𝓞 K) := {α | α - D.b ∈ D.a * D.m}

def Cnonzero (D : Data K) : Set (𝓞 K) := C D \ {0}

abbrev Cx (D : Data K) := {α : 𝓞 K // α ∈ Cnonzero D}

theorem mem_C_iff (D : Data K) (α : 𝓞 K) :
    α ∈ C D ↔ α ∈ D.a ∧ α - 1 ∈ D.m := by
  change α - D.b ∈ D.a * D.m ↔ _
  rw [Ideal.mul_eq_inf_of_coprime D.coprime]
  constructor
  · intro h
    constructor
    · have := D.a.add_mem h.1 D.basepoint_mem
      simpa using this
    · have := D.m.add_mem h.2 D.basepoint_congruent_one
      convert this using 1 <;> ring
  · rintro ⟨ha, hm⟩
    constructor
    · exact D.a.sub_mem ha D.basepoint_mem
    · change α - D.b ∈ D.m
      have := D.m.sub_mem hm D.basepoint_congruent_one
      convert this using 1 <;> ring

@[simp] theorem mem_Cnonzero_iff (D : Data K) (α : 𝓞 K) :
    α ∈ Cnonzero D ↔ α ∈ C D ∧ α ≠ 0 := by
  simp [Cnonzero]

theorem rayUnit_mul_mem_Cnonzero (D : Data K) (u : U K D.m) (α : Cx D) :
    (u.val : 𝓞 K) * α.val ∈ Cnonzero D := by
  obtain ⟨hc, hn⟩ := (mem_Cnonzero_iff D α.val).mp α.property
  obtain ⟨ha, hm⟩ := (mem_C_iff D α.val).mp hc
  apply (mem_Cnonzero_iff D _).mpr
  refine ⟨(mem_C_iff D _).mpr ⟨D.a.mul_mem_left _ ha, ?_⟩,
    mul_ne_zero u.val.ne_zero hn⟩
  have hu : IsRayUnit K D.m u.val := u.property
  have := D.m.add_mem (D.m.mul_mem_left (u.val : 𝓞 K) hm) hu.1
  convert this using 1 <;> ring

instance rayUnitMulAction (D : Data K) : MulAction (U K D.m) (Cx D) where
  smul u α := ⟨(u.val : 𝓞 K) * α.val, rayUnit_mul_mem_Cnonzero D u α⟩
  one_smul α := by
    apply Subtype.ext
    change (1 : 𝓞 K) * α.val = α.val
    exact one_mul _
  mul_smul u v α := by
    apply Subtype.ext
    change ((u.val : 𝓞 K) * (v.val : 𝓞 K)) * α.val =
      (u.val : 𝓞 K) * ((v.val : 𝓞 K) * α.val)
    exact mul_assoc _ _ _

@[simp] theorem smul_val (D : Data K) (u : U K D.m) (α : Cx D) :
    (u • α).val = (u.val : 𝓞 K) * α.val := rfl

abbrev orbitSetoid (D : Data K) : Setoid (Cx D) :=
  MulAction.orbitRel (U K D.m) (Cx D)

abbrev X (D : Data K) := Quotient (orbitSetoid D)

def orbitMk (D : Data K) (α : Cx D) : X D := Quotient.mk (orbitSetoid D) α

theorem totallyPositive_smul (D : Data K) (u : U K D.m) (α : Cx D) :
    TotallyPositive K (u • α).val ↔ TotallyPositive K α.val := by
  have hu : IsRayUnit K D.m u.val := u.property
  constructor
  · intro h φ
    have hp := hu.2 φ
    have hmul := h φ
    simp only [smul_val, map_mul] at hmul
    exact (mul_pos_iff_of_pos_left hp).mp hmul
  · intro h φ
    simpa only [smul_val, map_mul] using mul_pos (hu.2 φ) (h φ)

def IsPositive (D : Data K) : X D → Prop :=
  Quotient.lift (fun α : Cx D => TotallyPositive K α.val) (by
    intro α β h
    obtain ⟨u, hu⟩ := h
    exact propext (hu ▸ totallyPositive_smul D u β))

def positiveOrbits (D : Data K) : Set (X D) := {x | IsPositive D x}

abbrev Xpos (D : Data K) := {x : X D // x ∈ positiveOrbits D}

def elementIdeal (D : Data K) (α : Cx D) : Ideal (𝓞 K) :=
  Ideal.span {α.val} / D.a

theorem elementIdeal_fractionalImage (D : Data K) (α : Cx D) :
    (elementIdeal D α : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      (Ideal.span {α.val} : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) *
        (D.a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)⁻¹ := by
  have ha : α.val ∈ D.a := ((mem_C_iff D α.val).mp
    ((mem_Cnonzero_iff D α.val).mp α.property).1).1
  have hspan : Ideal.span {α.val} ≤ D.a := Ideal.span_le.mpr (by simpa)
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hspan
  have ha' : (D.a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr D.ideal_ne_bot
  have hquot : (D.a * J) / D.a = J := by
    apply le_antisymm
    · have h : ((D.a * J) / D.a) * D.a ≤ D.a * J :=
        Submodule.le_div_iff_mul_le.mp le_rfl
      have hc := (FractionalIdeal.coeIdeal_le_coeIdeal K).mpr h
      rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
        mul_comm (D.a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)] at hc
      exact (FractionalIdeal.coeIdeal_le_coeIdeal K).mp
        ((mul_le_mul_iff_left₀ (pos_iff_ne_zero.mpr ha')).mp hc)
    · apply Submodule.le_div_iff_mul_le.mpr
      rw [mul_comm]
  unfold elementIdeal
  rw [hJ, hquot, FractionalIdeal.coeIdeal_mul, mul_comm
    (D.a : FractionalIdeal (nonZeroDivisors (𝓞 K)) K),
    mul_assoc, mul_inv_cancel₀ ha', mul_one]

def representativeSign (δ : Finset (RealPlaces K)) (α : 𝓞 K) : ℝ :=
  ∏ v ∈ δ, Real.sign (realEmbedding K v (α : K))

theorem representativeSign_smul (D : Data K) (δ : Finset (RealPlaces K))
    (u : U K D.m) (α : Cx D) :
    representativeSign δ (u • α).val = representativeSign δ α.val := by
  unfold representativeSign
  apply Finset.prod_congr rfl
  intro v hv
  simp only [smul_val, map_mul]
  have hu : IsRayUnit K D.m u.val := u.property
  have hp := hu.2 (realEmbedding K v)
  rcases lt_trichotomy (realEmbedding K v (α.val : K)) 0 with hn | hz | hn
  · rw [Real.sign_of_neg hn, Real.sign_of_neg (mul_neg_of_pos_of_neg hp hn)]
  · rw [hz, mul_zero]
  · rw [Real.sign_of_pos hn, Real.sign_of_pos (mul_pos hp hn)]

def signδ (D : Data K) (δ : Finset (RealPlaces K)) : X D → ℝ :=
  Quotient.lift (fun α : Cx D => representativeSign δ α.val) (by
    intro α β h
    obtain ⟨u, hu⟩ := h
    exact hu ▸ representativeSign_smul D δ u β)

def representativeNormWeight (D : Data K) (α : 𝓞 K) : ℝ :=
  |(Algebra.norm ℚ (α : K) : ℝ)| / (Ideal.absNorm D.a : ℝ)

theorem abs_norm_unit (u : (𝓞 K)ˣ) :
    |(Algebra.norm ℚ ((u : 𝓞 K) : K) : ℝ)| = 1 := by
  rw [← Rat.cast_abs, NumberField.Units.norm K u, Rat.cast_one]

theorem representativeNormWeight_smul (D : Data K) (u : U K D.m) (α : Cx D) :
    representativeNormWeight D (u • α).val = representativeNormWeight D α.val := by
  unfold representativeNormWeight
  simp only [smul_val, map_mul, Rat.cast_mul, abs_mul, abs_norm_unit, one_mul]

def normWeight (D : Data K) : X D → ℝ :=
  Quotient.lift (fun α : Cx D => representativeNormWeight D α.val) (by
    intro α β h
    obtain ⟨u, hu⟩ := h
    exact hu ▸ representativeNormWeight_smul D u β)

@[simp] theorem isPositive_orbitMk (D : Data K) (α : Cx D) :
    IsPositive D (orbitMk D α) ↔ TotallyPositive K α.val := Iff.rfl

@[simp] theorem signδ_orbitMk (D : Data K) (δ : Finset (RealPlaces K)) (α : Cx D) :
    signδ D δ (orbitMk D α) = representativeSign δ α.val := rfl

@[simp] theorem normWeight_orbitMk (D : Data K) (α : Cx D) :
    normWeight D (orbitMk D α) = representativeNormWeight D α.val := rfl

end DedekindZetaZeroFree.AbelianQuotient.RayCoset

end
