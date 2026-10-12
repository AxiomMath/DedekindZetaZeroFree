module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Archimedean.TraceNormalization
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.RealContinuousCharacters

@[expose] public section

noncomputable section
open scoped Classical
namespace DedekindZetaZeroFree.PoissonArch
variable (F : Type) [Field F] [NumberField F]
def infiniteAdeleCoordinates : NumberField.InfiniteAdeleRing F ≃+ Space F :=
  (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toAddEquiv.trans
    (NumberField.mixedEmbedding.euclidean.toMixed F).symm.toLinearEquiv.toAddEquiv

instance infiniteAdeleRealModule : Module ℝ (NumberField.InfiniteAdeleRing F) :=
  (infiniteAdeleCoordinates F).module ℝ

def infiniteAdeleMixedHomeomorph :
    NumberField.InfiniteAdeleRing F ≃ₜ NumberField.mixedEmbedding.mixedSpace F :=
  (Homeomorph.piEquivPiSubtypeProd (fun v : NumberField.InfinitePlace F => v.IsReal)
    (fun v => v.Completion)).trans
    (Homeomorph.prodCongr
      (Homeomorph.piCongrRight fun v =>
        (NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal v.2).toHomeomorph)
      ((Homeomorph.piCongrRight fun v =>
        (NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex
          (NumberField.InfinitePlace.not_isReal_iff_isComplex.mp v.2)).toHomeomorph).trans
        (Homeomorph.piCongrLeft (Y := fun _ => ℂ)
          (Equiv.subtypeEquivRight fun _ =>
            NumberField.InfinitePlace.not_isReal_iff_isComplex))))

def infiniteAdeleToSpace : NumberField.InfiniteAdeleRing F ≃L[ℝ] Space F :=
  { (infiniteAdeleCoordinates F).linearEquiv ℝ with
    continuous_toFun :=
      (NumberField.mixedEmbedding.euclidean.toMixed F).symm.continuous.comp
        (infiniteAdeleMixedHomeomorph F).continuous
    continuous_invFun :=
      (infiniteAdeleMixedHomeomorph F).symm.continuous.comp
        (NumberField.mixedEmbedding.euclidean.toMixed F).continuous }

theorem infiniteAdeleToSpace_coordinates (x : NumberField.InfiniteAdeleRing F) :
    NumberField.mixedEmbedding.euclidean.toMixed F (infiniteAdeleToSpace F x) =
      NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x := by
  change (NumberField.mixedEmbedding.euclidean.toMixed F)
    ((NumberField.mixedEmbedding.euclidean.toMixed F).symm
      (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)) = _
  exact (NumberField.mixedEmbedding.euclidean.toMixed F).apply_symm_apply _
end DedekindZetaZeroFree.PoissonArch

namespace DedekindZetaZeroFree

private theorem arch_character_inner
    (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (χ : AddChar E Circle) (hχ : Continuous χ) :
    ∃! z : E, ∀ x : E, χ x = Real.fourierChar (inner ℝ x z) := by
  obtain ⟨g, ⟨hg0, hgexp⟩, hguniq⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
      ⟨χ, hχ⟩ 0 0 (by simp)
  have hgexp' (x : E) : Circle.exp (g x) = χ x := congr_fun hgexp x
  have hgadd (x y : E) : g (x + y) = g x + g y := by
    let H : C(E, ℝ) := ⟨fun t => g (x + t) - g x, by fun_prop⟩
    have hH : H = g := hguniq H ⟨by simp [H], ?_⟩
    · have := DFunLike.congr_fun hH y
      dsimp [H] at this
      linarith
    · funext t
      dsimp [H]
      rw [Circle.exp_sub, hgexp', hgexp', χ.map_add_eq_mul]
      simp
  let G : E →+ ℝ := { toFun := g, map_zero' := hg0, map_add' := hgadd }
  let L : E →L[ℝ] ℝ :=
    { toFun := fun x => g x / (2 * Real.pi)
      map_add' := by intro x y; simp [hgadd, add_div]
      map_smul' := by
        intro r x
        have h := map_real_smul G g.continuous r x
        change g (r • x) = r * g x at h
        simp [h, mul_div_assoc]
      cont := by fun_prop }
  let z := (InnerProductSpace.toDual ℝ E).symm L
  have hz (x : E) : inner ℝ x z = L x := by
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  refine ⟨z, ?_, ?_⟩
  · intro x
    rw [hz, Real.fourierChar_apply', ← hgexp']
    congr 1
    dsimp [L]
    field_simp
  · intro w hw
    let H : C(E, ℝ) := ⟨fun x => 2 * Real.pi * inner ℝ x w, by fun_prop⟩
    have hH : H = g := hguniq H ⟨by simp [H], ?_⟩
    · apply (InnerProductSpace.toDual ℝ E).injective
      ext x
      rw [InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDual_apply_apply,
        real_inner_comm x w, real_inner_comm x z, hz]
      have hx := DFunLike.congr_fun hH x
      dsimp [H, L] at hx ⊢
      apply (eq_div_iff (by positivity : 2 * Real.pi ≠ 0)).2
      simpa [mul_comm] using hx
    · funext x
      exact (hw x).symm

theorem kp_additive_arch_character
    (F : Type) [Field F] [NumberField F]
    (χ : AddChar (PoissonArch.Space F) Circle) (hχ : Continuous χ) :
    ∃! y : PoissonArch.Space F, ∀ x : PoissonArch.Space F,
      χ x = Real.fourierChar (PoissonArch.tracePairing F x y) := by
  obtain ⟨z, hz, huniq⟩ := arch_character_inner (PoissonArch.Space F) χ hχ
  refine ⟨(PoissonArch.traceAdapter F).symm z, ?_, ?_⟩
  · intro x
    simpa [PoissonArch.tracePairing_eq_inner] using hz x
  · intro y hy
    apply (PoissonArch.traceAdapter F).injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    exact huniq _ (by simpa [PoissonArch.tracePairing_eq_inner] using hy)

theorem kp_additive_infinite_adele_character
    (F : Type) [Field F] [NumberField F]
    (χ : AddChar (NumberField.InfiniteAdeleRing F) Circle) (hχ : Continuous χ) :
    ∃! y : NumberField.InfiniteAdeleRing F, ∀ x : NumberField.InfiniteAdeleRing F,
      χ x = Real.fourierChar (PoissonArch.tracePairing F
        (PoissonArch.infiniteAdeleToSpace F x) (PoissonArch.infiniteAdeleToSpace F y)) := by
  let e := PoissonArch.infiniteAdeleToSpace F
  let ψ := χ.compAddMonoidHom e.symm.toLinearEquiv.toAddMonoidHom
  have hψ : Continuous ψ := hχ.comp e.symm.continuous
  obtain ⟨z, hz, huniq⟩ := kp_additive_arch_character F ψ hψ
  refine ⟨e.symm z, ?_, ?_⟩
  · intro x
    simpa [ψ, e] using hz (e x)
  · intro y hy
    apply e.injective
    simp only [ContinuousLinearEquiv.apply_symm_apply]
    apply huniq
    intro x
    simpa [ψ, e] using hy (e.symm x)

end DedekindZetaZeroFree

end
