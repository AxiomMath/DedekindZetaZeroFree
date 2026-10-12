module

public import DedekindZetaZeroFree.Adeles.Characters.ArchimedeanAdditiveCharacters
public import DedekindZetaZeroFree.Adeles.Lattices.ArchimedeanIdealCovolume

@[expose] public section

namespace DedekindZetaZeroFree.TateSLocalMeasurability
noncomputable section
open scoped Classical NumberField
open NumberField MeasureTheory

variable (F : Type) [Field F] [NumberField F]

local instance archMeasurable : MeasurableSpace (InfiniteAdeleRing F) := borel _
local instance archBorel : BorelSpace (InfiniteAdeleRing F) := ⟨rfl⟩

private theorem norm_arch_mixed (F : Type) [Field F] [NumberField F]
    (z : InfiniteAdeleRing F) :
    ‖z‖ = (∏ v : {v : InfinitePlace F // v.IsReal},
      |(InfiniteAdeleRing.ringEquiv_mixedSpace F z).1 v|) *
      ∏ v : {v : InfinitePlace F // v.IsComplex},
        Complex.normSq ((InfiniteAdeleRing.ringEquiv_mixedSpace F z).2 v) := by
  classical
  rw [InfiniteAdeleRing.norm_def]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun v : InfinitePlace F => v.IsReal)
    (fun v => ‖z v‖ ^ v.mult)]
  congr 1
  · apply Finset.prod_congr rfl; intro v _
    rw [v.2.mult_eq_one, pow_one]
    change ‖z v.1‖ = |NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (z v.1)|
    simpa only [dist_zero_right, map_zero, Real.norm_eq_abs] using
      ((NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).dist_eq
        (z v.1) 0).symm
  · let equiv : {v : InfinitePlace F // ¬ v.IsReal} ≃
        {v : InfinitePlace F // v.IsComplex} :=
      Equiv.subtypeEquivRight fun _ => InfinitePlace.not_isReal_iff_isComplex
    apply Fintype.prod_equiv equiv
    intro v
    have hv := InfinitePlace.not_isReal_iff_isComplex.mp v.2
    rw [hv.mult_eq_two, Complex.normSq_eq_norm_sq]
    change ‖z v.1‖ ^ 2 = ‖NumberField.InfinitePlace.Completion.extensionEmbedding v.1 (z v.1)‖ ^ 2
    congr 1
    simpa only [dist_zero_right, map_zero] using
      ((NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).dist_eq
        (z v.1) 0).symm

def localArchEquiv (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) : PoissonArch.Space F ≃L[ℝ] PoissonArch.Space F :=
  let w : (mixedEmbedding.mixedSpace F)ˣ :=
    Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toMonoidHom d
  ((mixedEmbedding.euclidean.toMixed F).trans
    ((ContinuousLinearEquiv.piCongrRight fun v : {v : InfinitePlace F // v.IsReal} =>
      ContinuousLinearEquiv.unitsEquivAut ℝ
        (Units.map (Pi.evalRingHom _ v).toMonoidHom
          (Units.map (RingHom.fst _ _).toMonoidHom w))).prodCongr
      (ContinuousLinearEquiv.piCongrRight fun v : {v : InfinitePlace F // v.IsComplex} =>
        (ContinuousLinearEquiv.unitsEquivAut ℂ
          (Units.map (Pi.evalRingHom _ v).toMonoidHom
            (Units.map (RingHom.snd _ _).toMonoidHom w))).restrictScalars ℝ))).trans
    (mixedEmbedding.euclidean.toMixed F).symm

private theorem localArchEquiv_apply (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) (x : PoissonArch.Space F) :
    localArchEquiv F d x = PoissonArch.infiniteAdeleToSpace F
      (d.val * (PoissonArch.infiniteAdeleToSpace F).symm x) := by
  apply (mixedEmbedding.euclidean.toMixed F).injective
  simp only [localArchEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.prodCongr_apply,
    PoissonArch.infiniteAdeleToSpace_coordinates, map_mul]
  have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
    ((PoissonArch.infiniteAdeleToSpace F).symm x)
  rw [ContinuousLinearEquiv.apply_symm_apply] at hx
  rw [← hx]
  ext v <;> simp [ContinuousLinearEquiv.piCongrRight_apply,
    ContinuousLinearEquiv.unitsEquivAut_apply, mul_comm]

private theorem localArchEquiv_abs_det (F : Type) [Field F] [NumberField F]
    (d : (InfiniteAdeleRing F)ˣ) :
    |LinearMap.det (localArchEquiv F d).toLinearMap| = ‖d.val‖ := by
  let z := InfiniteAdeleRing.ringEquiv_mixedSpace F d.val
  let R : {v : InfinitePlace F // v.IsReal} → ℝ →ₗ[ℝ] ℝ :=
    fun v => LinearMap.mulLeft ℝ (z.1 v)
  let C : {v : InfinitePlace F // v.IsComplex} → ℂ →ₗ[ℝ] ℂ :=
    fun v => (LinearMap.mulLeft ℂ (z.2 v)).restrictScalars ℝ
  have he : (localArchEquiv F d).toLinearMap =
    (mixedEmbedding.euclidean.toMixed F).symm.toLinearMap.comp
      (((LinearMap.pi fun v => (R v).comp (LinearMap.proj v)).prodMap
        (LinearMap.pi fun v => (C v).comp (LinearMap.proj v))).comp
          (mixedEmbedding.euclidean.toMixed F).toLinearMap) := by
    ext x
    apply (mixedEmbedding.euclidean.toMixed F).injective
    change (mixedEmbedding.euclidean.toMixed F) (localArchEquiv F d x) = _
    rw [localArchEquiv_apply]
    simp only [PoissonArch.infiniteAdeleToSpace_coordinates, map_mul,
      LinearMap.prodMap_apply, ContinuousLinearEquiv.coe_coe,
      LinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    have hx := PoissonArch.infiniteAdeleToSpace_coordinates F
      ((PoissonArch.infiniteAdeleToSpace F).symm x)
    rw [ContinuousLinearEquiv.apply_symm_apply] at hx
    rw [← hx]
    ext v <;> simp [R, C, z, mul_comm]
  rw [he, ContinuousLinearEquiv.toLinearEquiv_symm]
  have hd := LinearMap.det_conj
    ((LinearMap.pi fun v => (R v).comp (LinearMap.proj v)).prodMap
      (LinearMap.pi fun v => (C v).comp (LinearMap.proj v)))
    (mixedEmbedding.euclidean.toMixed F).toLinearEquiv.symm
  simp only [LinearEquiv.symm_symm] at hd
  rw [hd, LinearMap.det_prodMap, LinearMap.det_pi, LinearMap.det_pi, abs_mul]
  have hc (c : ℂ) : LinearMap.det ((LinearMap.mulLeft ℂ c).restrictScalars ℝ) =
      Complex.normSq c := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_mulLeft, Algebra.norm_complex_apply]
  simp only [R, C, LinearMap.det_mulLeft, hc, Finset.abs_prod,
    abs_of_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _)]
  exact (norm_arch_mixed F d.val).symm

theorem archimedean_map_mul (g : (InfiniteAdeleRing F)ˣ) :
    Measure.map (fun x : InfiniteAdeleRing F => g.val * x)
        (Measure.map (PoissonArch.infiniteAdeleToSpace F).symm
          (PoissonArch.traceMeasure F)) =
      (ENNReal.ofReal ‖g.val‖)⁻¹ •
        Measure.map (PoissonArch.infiniteAdeleToSpace F).symm
          (PoissonArch.traceMeasure F) := by
  let e := PoissonArch.infiniteAdeleToSpace F
  let A := localArchEquiv F g
  let μ := PoissonArch.traceMeasure F
  have hmm : Measurable (fun x : InfiniteAdeleRing F => g.val * x) :=
    (continuous_const.mul continuous_id).measurable
  have hes : Measurable (e.symm : PoissonArch.Space F → InfiniteAdeleRing F) :=
    e.symm.continuous.measurable
  have hAmeas : Measurable (A : PoissonArch.Space F → PoissonArch.Space F) :=
    A.continuous.measurable
  have hA : (fun x : InfiniteAdeleRing F => g.val * x) ∘
        (e.symm : PoissonArch.Space F → InfiniteAdeleRing F) =
      (e.symm : PoissonArch.Space F → InfiniteAdeleRing F) ∘
        (A : PoissonArch.Space F → PoissonArch.Space F) := by
    funext x
    simp only [Function.comp_apply]
    rw [show A x = e (g.val * e.symm x) from localArchEquiv_apply F g x]
    simp
  have hdetabs : |LinearMap.det A.toLinearMap| = ‖g.val‖ := localArchEquiv_abs_det F g
  have hmap : Measure.map (A : PoissonArch.Space F → PoissonArch.Space F) μ =
      (ENNReal.ofReal ‖g.val‖)⁻¹ • μ := by
    have hdet : LinearMap.det A.toLinearMap ≠ 0 := A.toLinearEquiv.isUnit_det'.ne_zero
    have h := Measure.map_linearMap_addHaar_eq_smul_addHaar μ hdet
    have hpos : 0 < ‖g.val‖ := by
      rw [InfiniteAdeleRing.norm_def]
      refine Finset.prod_pos fun v _ => pow_pos ?_ _
      exact norm_pos_iff.mpr (Pi.isUnit_iff.mp g.isUnit v).ne_zero
    have hcoe : Measure.map (A : PoissonArch.Space F → PoissonArch.Space F) μ =
        Measure.map (A.toLinearMap) μ := rfl
    rw [hcoe, h, abs_inv, hdetabs, ENNReal.ofReal_inv_of_pos hpos]
  calc
    Measure.map (fun x : InfiniteAdeleRing F => g.val * x)
        (Measure.map e.symm μ)
      = Measure.map ((fun x : InfiniteAdeleRing F => g.val * x) ∘ e.symm) μ := by
          rw [Measure.map_map hmm hes]
    _ = Measure.map (e.symm ∘ A) μ := by rw [hA]
    _ = Measure.map e.symm (Measure.map A μ) := by rw [Measure.map_map hes hAmeas]
    _ = Measure.map e.symm ((ENNReal.ofReal ‖g.val‖)⁻¹ • μ) := by rw [hmap]
    _ = (ENNReal.ofReal ‖g.val‖)⁻¹ • Measure.map e.symm μ := by
          rw [Measure.map_smul _ hes.aemeasurable]

end
end DedekindZetaZeroFree.TateSLocalMeasurability
