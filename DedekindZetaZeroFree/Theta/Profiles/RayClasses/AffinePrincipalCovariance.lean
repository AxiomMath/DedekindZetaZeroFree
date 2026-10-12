module

public import DedekindZetaZeroFree.Theta.Profiles.RayClasses.PrincipalLogarithmicCoordinates

@[expose] public section

noncomputable section

open scoped NumberField nonZeroDivisors
open DedekindZetaZeroFree.AbelianQuotient

namespace DedekindZetaZeroFree.Hecke.Theta

variable {F : Type} [Field F] [NumberField F]

theorem principalMul_mem_ideal
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)}) :
    (γ : F) * x.val ∈ (J : FractionalIdeal (𝓞 F)⁰ F) := by
  rw [hJ, FractionalIdeal.mem_singleton_mul]
  exact ⟨x.val, x.property, rfl⟩

 theorem principalMul_modulus_eq
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F)) :
    ((J * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        ((I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F) := by
  simp only [Units.val_mul, hJ, mul_assoc]

 theorem inverseMul_mem
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (x : {x : F // x ∈ (J : FractionalIdeal (𝓞 F)⁰ F)}) :
    ((γ⁻¹ : Fˣ) : F) * x.val ∈ (I : FractionalIdeal (𝓞 F)⁰ F) := by
  have hx := x.property
  simp only [hJ, FractionalIdeal.mem_singleton_mul] at hx
  rcases hx with ⟨y, hy, he⟩
  simpa [he, ← mul_assoc] using hy

def affineResiduePrimalIndexMulEquiv
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F)) :
    {l : F // l ∈ ((I * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F)} ≃
    {l : F // l ∈ ((J * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F)} where
  toFun l := ⟨(γ : F) * l.val,
    principalMul_mem_ideal (I * rayIdealFractionalIdeal F m hm) (J * rayIdealFractionalIdeal F m hm) γ (principalMul_modulus_eq m hm I J γ hJ) l⟩
  invFun l := ⟨((γ⁻¹ : Fˣ) : F) * l.val,
    inverseMul_mem (I * rayIdealFractionalIdeal F m hm) (J * rayIdealFractionalIdeal F m hm) γ (principalMul_modulus_eq m hm I J γ hJ) l⟩
  left_inv l := by apply Subtype.ext; simp [← mul_assoc]
  right_inv l := by apply Subtype.ext; simp [← mul_assoc]

@[simp] theorem affineResiduePrimalIndexMulEquiv_apply_val
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (l : {l : F // l ∈ ((I * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F)}) :
    (affineResiduePrimalIndexMulEquiv m hm I J γ hJ l).val =
      (γ : F) * l.val := by
  rfl

@[simp] theorem affineResiduePrimalIndexMulEquiv_symm_apply_val
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (l : {l : F // l ∈ ((J * rayIdealFractionalIdeal F m hm) :
      FractionalIdeal (𝓞 F)⁰ F)}) :
    ((affineResiduePrimalIndexMulEquiv m hm I J γ hJ).symm l).val =
      ((γ⁻¹ : Fˣ) : F) * l.val := by
  rfl

theorem inverseMul_mem_dual
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F I :
      FractionalIdeal (𝓞 F)⁰ F)}) :
    ((γ⁻¹ : Fˣ) : F) * β.val ∈ (Theta.traceDualIdealUnit F J :
      FractionalIdeal (𝓞 F)⁰ F) := by
  rw [Theta.coe_traceDualIdealUnit, FractionalIdeal.mem_dual (Units.ne_zero J)]
  have hb := β.property
  simp only [Theta.coe_traceDualIdealUnit, FractionalIdeal.mem_dual (Units.ne_zero I)] at hb
  intro a ha
  rw [hJ, FractionalIdeal.mem_singleton_mul] at ha
  rcases ha with ⟨b, hbI, rfl⟩
  have he : (((γ⁻¹ : Fˣ) : F) * β.val) * ((γ : F) * b) = β.val * b := by
    calc
      _ = (((γ⁻¹ : Fˣ) : F) * (γ : F)) * (β.val * b) := by ring
      _ = β.val * b := by simp
  simpa only [Algebra.traceForm_apply, he] using hb b hbI

 theorem principalMul_mem_dual
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F J :
      FractionalIdeal (𝓞 F)⁰ F)}) :
    (γ : F) * β.val ∈ (Theta.traceDualIdealUnit F I :
      FractionalIdeal (𝓞 F)⁰ F) := by
  rw [Theta.coe_traceDualIdealUnit, FractionalIdeal.mem_dual (Units.ne_zero I)]
  have hb := β.property
  simp only [Theta.coe_traceDualIdealUnit, FractionalIdeal.mem_dual (Units.ne_zero J)] at hb
  intro a ha
  have ht := hb ((γ : F) * a) (principalMul_mem_ideal I J γ hJ ⟨a, ha⟩)
  simpa [Algebra.traceForm_apply, mul_left_comm, mul_assoc, mul_comm] using ht

def affineResidueDualIndexMulEquiv
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F)) :
    {β : F // β ∈ (Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)} ≃
    {β : F // β ∈ (Theta.traceDualIdealUnit F
      (J * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)} where
  toFun β := ⟨((γ⁻¹ : Fˣ) : F) * β.val,
    inverseMul_mem_dual _ _ γ (principalMul_modulus_eq m hm I J γ hJ) β⟩
  invFun β := ⟨(γ : F) * β.val,
    principalMul_mem_dual _ _ γ (principalMul_modulus_eq m hm I J γ hJ) β⟩
  left_inv β := by apply Subtype.ext; simp [← mul_assoc]
  right_inv β := by apply Subtype.ext; simp [← mul_assoc]

@[simp] theorem affineResidueDualIndexMulEquiv_apply_val
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (I * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)}) :
    (affineResidueDualIndexMulEquiv m hm I J γ hJ β).val =
      ((γ⁻¹ : Fˣ) : F) * β.val := by
  rfl

@[simp] theorem affineResidueDualIndexMulEquiv_symm_apply_val
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (β : {β : F // β ∈ (Theta.traceDualIdealUnit F
      (J * rayIdealFractionalIdeal F m hm) : FractionalIdeal (𝓞 F)⁰ F)}) :
    ((affineResidueDualIndexMulEquiv m hm I J γ hJ).symm β).val =
      (γ : F) * β.val := by
  rfl

theorem trace_principalMul_inverseMul (γ : Fˣ) (x β : F) :
    Algebra.trace ℚ F (((γ : F) * x) * (((γ⁻¹ : Fˣ) : F) * β)) =
      Algebra.trace ℚ F (x * β) := by
  congr 1
  calc
    _ = ((γ : F) * ((γ⁻¹ : Fˣ) : F)) * (x * β) := by ring
    _ = x * β := by simp

theorem affineResidueTheta_principal_mul
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (u : ℝ) (hu : 0 < u) (h : RayCoset.logHyperplane F) :
    affineResidueTheta m hm J
      ⟨(γ : F) * x.val, principalMul_mem_ideal I J γ hJ x⟩ u h =
    affineResidueTheta m hm I x u (h + principalNormalizedLogShift hF γ) := by
  unfold affineResidueTheta
  rw [← (affineResiduePrimalIndexMulEquiv m hm I J γ hJ).tsum_eq]
  apply tsum_congr
  intro l
  simp only [affineResiduePrimalIndexMulEquiv_apply_val]
  rw [← mul_add]
  exact affineResidueKernel_principal_mul hF I J γ hJ u hu h (x.val + l.val)

theorem affineResidueDualTheta_principal_mul
    (hF : NumberField.IsTotallyComplex F)
    (m : Ideal (𝓞 F)) (hm : m ≠ ⊥)
    (I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (γ : Fˣ)
    (hJ : (J : FractionalIdeal (𝓞 F)⁰ F) =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (γ : F) *
        (I : FractionalIdeal (𝓞 F)⁰ F))
    (x : {x : F // x ∈ (I : FractionalIdeal (𝓞 F)⁰ F)})
    (u : ℝ) (hu : 0 < u) (h : RayCoset.logHyperplane F) :
    affineResidueDualTheta m hm J
      ⟨(γ : F) * x.val, principalMul_mem_ideal I J γ hJ x⟩ u h =
    affineResidueDualTheta m hm I x u (h + principalNormalizedLogShift hF γ) := by
  unfold affineResidueDualTheta
  rw [← (affineResidueDualIndexMulEquiv m hm I J γ hJ).tsum_eq]
  apply tsum_congr
  intro β
  simp only [affineResidueDualIndexMulEquiv_apply_val, trace_principalMul_inverseMul]
  rw [affineResidueDualKernel_principal_mul hF I J γ hJ u hu h β.val]

end DedekindZetaZeroFree.Hecke.Theta

end
