module

public import DedekindZetaZeroFree.Metaplectic.Torus.AdelicSmoothFunctionTopology

@[expose] public section

noncomputable section
open MeasureTheory
open scoped Classical NumberField ENNReal NNReal Topology
set_option backward.isDefEq.respectTransparency false
namespace DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue
variable {F : Type} [Field F] [NumberField F] {ζ : F} {hζ : IsPrimitiveRoot ζ 12}

theorem adelic_integral_mul_idele_inv (μ : Measure (KPGlobalTorusFunctionData.Adeles F)) [μ.IsAddHaarMeasure]
    (a : (KPGlobalTorusFunctionData.Adeles F)ˣ) (k : KPGlobalTorusFunctionData.Adeles F → ℂ) :
    (∫ x, k (x * (↑a⁻¹ : KPGlobalTorusFunctionData.Adeles F)) ∂μ) =
      ((addEquivAddHaarChar (ContinuousAddEquiv.mulLeft a) : ℝ) : ℂ) * ∫ x, k x ∂μ := by
  let T := ContinuousAddEquiv.mulLeft a
  let m := addEquivAddHaarChar T
  have hm := addEquivAddHaarChar_smul_map μ T.symm
  rw [addEquivAddHaarChar_symm] at hm
  have hmap : μ.map T.symm = m • μ := by
    have hh := congrArg (fun ν : Measure (KPGlobalTorusFunctionData.Adeles F) => m • ν) hm
    simpa [m, smul_smul, mul_inv_cancel₀ (addEquivAddHaarChar_pos T).ne'] using hh
  have he : ⇑T.symm.toMeasurableEquiv = fun x : KPGlobalTorusFunctionData.Adeles F =>
      x * (↑a⁻¹ : KPGlobalTorusFunctionData.Adeles F) := by
    ext x
    apply T.injective
    change T (T.symm x) = (↑a : KPGlobalTorusFunctionData.Adeles F) * (x * ↑a⁻¹)
    rw [T.apply_symm_apply, mul_left_comm, Units.mul_inv, mul_one]
  have hh := integral_map_equiv (μ := μ) T.symm.toMeasurableEquiv k
  rw [he] at hh
  have heT : ⇑T.symm = fun x : KPGlobalTorusFunctionData.Adeles F => x * ↑a⁻¹ := he
  rw [heT] at hmap
  rw [← hh, hmap, integral_smul_nnreal_measure]
  rfl

end DedekindZetaZeroFree.KPGlobalResidualKernel.ScatteringResidue

end
