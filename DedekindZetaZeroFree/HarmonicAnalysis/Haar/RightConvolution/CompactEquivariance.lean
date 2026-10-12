module

public import DedekindZetaZeroFree.RepresentationTheory.Smooth.Convolution.GaussChartBumps

@[expose] public section

noncomputable section
namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.RightConvolution
open MeasureTheory
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

private theorem arch_conjugation_transport
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (a : L F) (k : G F ζ hζ) :
    PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * k =
      k * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k)⁻¹ * a *
          PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k) := by
  obtain ⟨e, he, hep, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  let p := PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k
  have hp : (e.symm k).1 = p := hep k
  have hpair : (a, (1 : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)) * e.symm k =
      e.symm k * (p⁻¹ * a * p, 1) := by
    ext <;> simp [hp, mul_assoc]
  have h := congrArg e hpair
  change e ((a, 1) * e.symm k) = e (e.symm k * (p⁻¹ * a * p, 1)) at h
  rw [map_mul, map_mul, e.apply_symm_apply, he, he] at h
  simp only [Subgroup.coe_one, mul_one] at h
  exact h

theorem conjugation_equivariance
    (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (μL : Measure (L F)) [μL.IsHaarMeasure]
    (q : L F → ℝ) (k : G F ζ hζ)
    (hmap : Measure.map (fun a : L F =>
      (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k)⁻¹ * a *
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k) μL = μL)
    (hq : ∀ a : L F, q
      ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k)⁻¹ * a *
        PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k) = q a)
    (v : G F ζ hζ → ℂ) (g : G F ζ hζ) :
    (∫ a : L F, (q a : ℂ) *
      v ((g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) * k) ∂μL) =
    ∫ a : L F, (q a : ℂ) *
      v ((g * k) * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) ∂μL := by
  let φ : L F → L F := fun a =>
    (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k)⁻¹ * a *
      PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k
  have hφmap : Measure.map φ μL = μL := hmap
  have hφemb : MeasurableEmbedding φ := by
    have hφeq : φ = ⇑((Homeomorph.mulLeft
        (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k)⁻¹).trans
        (Homeomorph.mulRight (PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k))) := by
      funext a
      simp only [φ, Homeomorph.trans_apply, Homeomorph.coe_mulLeft,
        Homeomorph.coe_mulRight]
    rw [hφeq]
    exact Homeomorph.measurableEmbedding _
  let F0 : L F → ℂ := fun a => (q a : ℂ) *
    v ((g * k) * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a)
  have hstep : (∫ a : L F, (q a : ℂ) *
      v ((g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) * k) ∂μL) =
      ∫ a : L F, F0 (φ a) ∂μL := by
    apply integral_congr_ae
    filter_upwards with a
    have htr := arch_conjugation_transport F ζ hζ a k
    simp only [φ, F0]
    rw [hq a, mul_assoc g (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) k,
      htr, ← mul_assoc g k (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ
        ((PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k)⁻¹ * a *
          PGLComplex.AdelicSlicesRaw.archProjection F ζ hζ k))]
  have hchange : (∫ a : L F, F0 (φ a) ∂μL) = ∫ a : L F, F0 a ∂μL := by
    rw [← hφemb.integral_map F0, hφmap]
  rw [hstep, hchange]

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel.RightConvolution

end
