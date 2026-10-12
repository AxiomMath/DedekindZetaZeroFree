module

public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanAdditiveCharacters
public import DedekindZetaZeroFree.Adeles.Lattices.FractionalIdealTraceDual

@[expose] public section

noncomputable section
open scoped Classical InnerProductSpace
open Additive Multiplicative
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPArchTrace

variable (F : Type) [Field F] [NumberField F]

abbrev FractionalOIdeal := FractionalIdeal (nonZeroDivisors (RingOfIntegers F)) F

def embedding (a : F) : PoissonArch.Space F :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm (NumberField.mixedEmbedding F a)

def inverseDifferent : FractionalOIdeal F :=
  (↑(differentIdeal ℤ (RingOfIntegers F)) : FractionalOIdeal F)⁻¹

theorem character_parameter_mem_inverseDifferent
    (I : FractionalOIdeal F) (hI : I ≠ 0)
    (χ : AddChar (PoissonArch.Space F) Circle) (hχ : Continuous χ)
    (y : PoissonArch.Space F)
    (hy : ∀ x, χ x = Circle.exp (2 * Real.pi * PoissonArch.tracePairing F x y))
    (hIχ : ∀ a : F, a ∈ I → χ (embedding F a) = 1) :
    y ∈ embedding F '' (↑(inverseDifferent F * I⁻¹) : Set F) := by
  let J : PoissonArch.NonzeroFractionalIdeal F := Units.mk0 I hI
  have hydual : y ∈ PoissonArch.idealTraceDual F J := by
    intro a ha
    have hexp : Circle.exp (2 * Real.pi * PoissonArch.tracePairing F
        (PoissonArch.minkowskiEmbedding F a) y) = 1 := by
      exact (hy (embedding F a)).symm.trans (hIχ a ha)
    obtain ⟨n, hn⟩ := Circle.exp_eq_one.mp hexp
    refine ⟨n, ?_⟩
    have hpi : 2 * Real.pi ≠ 0 := by positivity
    apply (mul_left_cancel₀ hpi)
    simpa [mul_comm] using hn.symm
  rw [PoissonArch.idealTraceDual_eq] at hydual
  obtain ⟨a, ha, rfl⟩ := (PoissonArch.mem_idealLattice F _ y).mp hydual
  refine ⟨a, ?_, rfl⟩
  change a ∈ inverseDifferent F * I⁻¹
  simpa only [Units.val_mul, Units.val_inv_eq_inv_val,
    PoissonArch.codifferentIdeal_eq_inv_different, J, Units.val_mk0,
    inverseDifferent] using ha

def infiniteToSpace (x : InfiniteAdeleRing F) : PoissonArch.Space F :=
  (NumberField.mixedEmbedding.euclidean.toMixed F).symm
    (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)

private theorem infiniteToSpace_eq (x : InfiniteAdeleRing F) :
    infiniteToSpace F x = PoissonArch.infiniteAdeleToSpace F x := by
  apply (NumberField.mixedEmbedding.euclidean.toMixed F).injective
  rw [PoissonArch.infiniteAdeleToSpace_coordinates]
  exact (NumberField.mixedEmbedding.euclidean.toMixed F).apply_symm_apply _

def infiniteTracePairing (x y : InfiniteAdeleRing F) : ℝ :=
  PoissonArch.tracePairing F (infiniteToSpace F x) (infiniteToSpace F y)

theorem infinite_character_classification
    (χ : AddChar (InfiniteAdeleRing F) Circle) (hχ : Continuous χ) :
    ∃! y : InfiniteAdeleRing F,
      ∀ x, χ x = Circle.exp (2 * Real.pi * infiniteTracePairing F x y) := by
  simpa only [Real.fourierChar_apply', infiniteTracePairing, infiniteToSpace_eq] using
    kp_additive_infinite_adele_character F χ hχ

theorem infinite_character_parameter_mem_inverseDifferent
    (I : FractionalOIdeal F) (hI : I ≠ 0)
    (χ : AddChar (InfiniteAdeleRing F) Circle) (hχ : Continuous χ)
    (y : InfiniteAdeleRing F)
    (hy : ∀ x, χ x = Circle.exp (2 * Real.pi * infiniteTracePairing F x y))
    (hIχ : ∀ a : F, a ∈ I → χ (algebraMap F (InfiniteAdeleRing F) a) = 1) :
    y ∈ (algebraMap F (InfiniteAdeleRing F)) ''
      (↑(inverseDifferent F * I⁻¹) : Set F) := by
  let e := PoissonArch.infiniteAdeleToSpace F
  let ψ := χ.compAddMonoidHom e.symm.toLinearEquiv.toAddMonoidHom
  have hψ : Continuous ψ := hχ.comp e.symm.continuous
  have hdiag (a : F) : e (algebraMap F (InfiniteAdeleRing F) a) = embedding F a := by
    rw [← infiniteToSpace_eq]
    unfold infiniteToSpace embedding
    rw [NumberField.InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  have hψy : ∀ x, ψ x = Circle.exp (2 * Real.pi * PoissonArch.tracePairing F x (e y)) := by
    intro x
    change χ (e.symm x) = _
    simpa only [infiniteTracePairing, infiniteToSpace_eq, e,
      ContinuousLinearEquiv.apply_symm_apply] using hy (e.symm x)
  have hψI : ∀ a : F, a ∈ I → ψ (embedding F a) = 1 := by
    intro a ha
    change χ (e.symm (embedding F a)) = 1
    rw [← hdiag, ContinuousLinearEquiv.symm_apply_apply]
    exact hIχ a ha
  obtain ⟨a, ha, hea⟩ := character_parameter_mem_inverseDifferent F I hI ψ hψ (e y) hψy hψI
  refine ⟨a, ha, ?_⟩
  apply e.injective
  exact (hdiag a).trans hea

end DedekindZetaZeroFree.KPArchTrace

end
