module

public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RightConvolution.PointwiseApproximation
public import DedekindZetaZeroFree.RepresentationTheory.Induction.CovariantSampling
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RightConvolution.CompactEquivariance
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RightConvolution.LeftChartSubstitution
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.RightConvolution.ShiftedKernelDifferentiation

@[expose] public section

noncomputable section

namespace DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

open MeasureTheory Filter Set Topology
open scoped NumberField Classical Topology Matrix.Norms.Elementwise

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming actual_kernel_pointwise_approximation → actual_kernel_pointwise_approximation

def rightConv (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) (μK : Measure D.K)
    (b : ContDiffBump (e0 F)) (v : G F ζ hζ → ℂ) (g : G F ζ hζ) : ℂ :=
  ∫ a : L F, (kappa F ζ hζ D μL μK b a : ℂ) *
    v (g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a) ∂μL

open _root_.DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel renaming actual_kernel_pointwise_approximation → actual_kernel_pointwise_approximation

 theorem arch_insertion_continuous :
    Continuous (PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ) := by
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have h : (fun a : L F => e (a, 1)) =
      PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ := by
    funext a
    simpa using he a 1
  rw [← h]
  exact e.continuous.comp (continuous_id.prodMk continuous_const)

 theorem rightConv_integrable
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) [μL.IsHaarMeasure] (μK : Measure D.K)
    (b : ContDiffBump (e0 F)) (v : G F ζ hζ → ℂ)
    (hv : Continuous v)
    (hc : Continuous (kappa F ζ hζ D μL μK b))
    (hs : HasCompactSupport (kappa F ζ hζ D μL μK b)) (g : G F ζ hζ) :
    Integrable (fun a : L F => (kappa F ζ hζ D μL μK b a : ℂ) *
      v (g * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a)) μL := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
  have hk : Continuous (fun a => (kappa F ζ hζ D μL μK b a : ℂ)) :=
    Complex.continuous_ofReal.comp hc
  have hk' : HasCompactSupport (fun a => (kappa F ζ hζ D μL μK b a : ℂ)) :=
    hs.comp_left Complex.ofReal_zero
  exact (hk.mul (hv.comp (continuous_const.mul
    (arch_insertion_continuous F ζ hζ)))).integrable_of_hasCompactSupport hk'.mul_right

 theorem rightConv_linear
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) [μL.IsHaarMeasure] (μK : Measure D.K)
    (b : ContDiffBump (e0 F))
    (hc : Continuous (kappa F ζ hζ D μL μK b))
    (hs : HasCompactSupport (kappa F ζ hζ D μL μK b))
    (u v : G F ζ hζ → ℂ) (c : ℂ) (hu : Continuous u) (hv : Continuous v) :
    rightConv F ζ hζ D μL μK b (u + v) =
      rightConv F ζ hζ D μL μK b u + rightConv F ζ hζ D μL μK b v ∧
    rightConv F ζ hζ D μL μK b (c • v) =
      c • rightConv F ζ hζ D μL μK b v := by
  constructor
  · funext g
    simp only [rightConv, Pi.add_apply, mul_add]
    exact integral_add (rightConv_integrable F ζ hζ D μL μK b u hu hc hs g)
      (rightConv_integrable F ζ hζ D μL μK b v hv hc hs g)
  · funext g
    simp only [rightConv, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (kappa F ζ hζ D μL μK b _ : ℂ) c]
    exact integral_const_mul c _

 theorem rightConv_continuous
    (D : KPMsRationalCompactCrossPairing.Iwasawa F ζ hζ)
    (μL : Measure (L F)) [μL.IsHaarMeasure] (μK : Measure D.K)
    (b : ContDiffBump (e0 F)) (v : G F ζ hζ → ℂ)
    (hv : Continuous v)
    (hc : Continuous (kappa F ζ hζ D μL μK b))
    (hs : HasCompactSupport (kappa F ζ hζ D μL μK b)) :
    Continuous (rightConv F ζ hζ D μL μK b v) := by
  let : IsTopologicalGroup (G F ζ hζ) :=
    (KPCubicCoverConstruction.adelic_topological_covers F ζ hζ).2.2.2.1
  rw [← continuousOn_univ]
  apply continuousOn_integral_of_compact_support hs
  · exact ((Complex.continuous_ofReal.comp (hc.comp continuous_snd)).mul
      (hv.comp (continuous_fst.mul
        ((arch_insertion_continuous F ζ hζ).comp continuous_snd)))).continuousOn
  · intro g a _ ha
    simp [image_eq_zero_of_notMem_tsupport ha]

 theorem globalLevel_le_finite
    (J : KPGlobalTorusFunctionData.FiniteLevel F ζ hζ) :
    KPGlobalTorusFunctionData.globalLevel F ζ hζ J ≤
      PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ := by
  rintro g ⟨j, hj, rfl⟩
  change j.val ∈ PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ
  rcases j.property with ⟨x, hx, heq⟩
  rw [← heq]
  refine ⟨x, ?_, rfl⟩
  intro w
  exact Subgroup.mem_iInf.mp hx w

 theorem arch_commutes_finite (a : L F)
    (j : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ) :
    PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a * j.val =
      j.val * PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ a := by
  obtain ⟨e, he, _⟩ := PGLComplex.AdelicSlicesRaw.actualArchFiniteSplitting F ζ hζ
  have h : (a, (1 : PGLComplex.AdelicSlicesRaw.finiteSubgroup F ζ hζ)) * (1, j) =
      (1, j) * (a, 1) := by simp
  have hm : e (a, 1) * e (1, j) = e (1, j) * e (a, 1) := by
    exact (map_mul e (a, 1) (1, j)).symm.trans
      ((congrArg e h).trans (map_mul e (1, j) (a, 1)))
  simp only [he] at hm
  have he1 : PGLComplex.AdelicSlicesRaw.archimedeanInsertion F ζ hζ 1 = 1 := by
    have ho : e (1, 1) = 1 := e.map_one
    rw [he] at ho
    simpa only [Subgroup.coe_one, mul_one] using ho
  simpa only [he1, Subgroup.coe_one, mul_one, one_mul] using hm

end DedekindZetaZeroFree.KPSpatialSmoothing.ArchKernel

end
