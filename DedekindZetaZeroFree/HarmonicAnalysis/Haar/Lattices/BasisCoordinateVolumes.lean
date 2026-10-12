module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Lattices.DualBasisCoordinates
public import Mathlib.Algebra.Module.ZLattice.Covolume

@[expose] public section

noncomputable section
open scoped Classical
open Module MeasureTheory

namespace DedekindZetaZeroFree.PoissonArch

def coordinateBoxIco (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Set.Ico 0 1}

def coordinateBoxIoc (ι : Type*) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Set.Ioc 0 1}

def basisDomain
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) : Set V :=
  (b.ofZLatticeBasis ℝ L).equivFun.symm '' coordinateBoxIco ι

theorem coordinate_covolume_pos
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] :
    0 < ZLattice.covolume L volume := by
  exact ZLattice.covolume_pos L volume

theorem basisDomain_isAddFundamentalDomain
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    IsAddFundamentalDomain L (basisDomain L b) volume := by
  have hd : basisDomain L b = ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ L) := by
    rw [basisDomain, LinearEquiv.image_eq_preimage_symm]
    ext v
    simp [coordinateBoxIco, ZSpan.fundamentalDomain, Basis.equivFun_apply]
  rw [hd]
  exact ZLattice.isAddFundamentalDomain b volume

theorem basis_coordinates_map_volume
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    Measure.map (b.ofZLatticeBasis ℝ L).equivFun volume =
      ENNReal.ofReal (ZLattice.covolume L volume) • (volume : Measure (ι → ℝ)) := by
  let e := (b.ofZLatticeBasis ℝ L).equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hc : ENNReal.ofReal (ZLattice.covolume L volume) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (coordinate_covolume_pos L))
  change Measure.map e volume = _
  ext s hs
  rw [Measure.map_apply e.measurable hs, Measure.smul_apply, smul_eq_mul]
  have h := ZLattice.volume_image_eq_volume_div_covolume' L b
    (e.measurable hs).nullMeasurableSet
  have he : (b.ofZLatticeBasis ℝ L).equivFun '' (e ⁻¹' s) = s :=
    Set.image_preimage_eq _ e.surjective
  rw [he] at h
  exact ((ENNReal.eq_div_iff hc ENNReal.ofReal_ne_top).mp h).symm

private theorem coordinate_restricted_map
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) :
    Measure.map (b.ofZLatticeBasis ℝ L).equivFun (volume.restrict (basisDomain L b)) =
      ENNReal.ofReal (ZLattice.covolume L volume) • volume.restrict (coordinateBoxIco ι) := by
  let e := (b.ofZLatticeBasis ℝ L).equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hd : basisDomain L b = e ⁻¹' coordinateBoxIco ι := by
    rw [basisDomain, LinearEquiv.image_eq_preimage_symm]
    rfl
  change Measure.map e (volume.restrict (basisDomain L b)) = _
  rw [hd, ← e.restrict_map]
  change (Measure.map (b.ofZLatticeBasis ℝ L).equivFun volume).restrict _ = _
  rw [basis_coordinates_map_volume, Measure.restrict_smul]

theorem integral_basis_coordinates_Ico
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)
    (g : V → ℂ) (hg : IntegrableOn g (basisDomain L b) volume) :
    (∫ x in coordinateBoxIco ι, g ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) =
      (ZLattice.covolume L volume : ℂ)⁻¹ * ∫ v in basisDomain L b, g v := by
  let e := (b.ofZLatticeBasis ℝ L).equivFun.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have h : (ZLattice.covolume L volume : ℂ) *
      (∫ x in coordinateBoxIco ι, g (e.symm x)) = ∫ v in basisDomain L b, g v := by
    have hm := e.measurableEmbedding.integral_map (g ∘ e.symm)
      (μ := volume.restrict (basisDomain L b))
    change (∫ x, (g ∘ e.symm) x ∂Measure.map (b.ofZLatticeBasis ℝ L).equivFun
      (volume.restrict (basisDomain L b))) = _ at hm
    rw [coordinate_restricted_map, integral_smul_measure,
      ENNReal.toReal_ofReal (coordinate_covolume_pos L).le] at hm
    simpa [Function.comp_def, Complex.real_smul] using hm
  have hc : (ZLattice.covolume L volume : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (coordinate_covolume_pos L))
  change (∫ x in coordinateBoxIco ι, g (e.symm x)) = _
  rw [← h]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

private theorem coordinate_boxes_ae_eq (ι : Type*) [Fintype ι] :
    coordinateBoxIco ι =ᵐ[volume] coordinateBoxIoc ι := by
  have h := Measure.ae_eq_set_pi (I := Set.univ)
    (μ := fun _ : ι => (volume : Measure ℝ))
    (s := fun _ => Set.Ico (0 : ℝ) 1) (t := fun _ => Set.Ioc (0 : ℝ) 1)
    (fun _ _ => Ico_ae_eq_Ioc)
  simpa [coordinateBoxIco, coordinateBoxIoc, Set.pi, volume_pi] using h

theorem integral_basis_coordinates_Ioc
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L)
    (g : V → ℂ) (hg : IntegrableOn g (basisDomain L b) volume) :
    (∫ x in coordinateBoxIoc ι, g ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) =
      (ZLattice.covolume L volume : ℂ)⁻¹ * ∫ v in basisDomain L b, g v := by
  rw [setIntegral_congr_set (coordinate_boxes_ae_eq ι).symm]
  exact integral_basis_coordinates_Ico L b g hg

end DedekindZetaZeroFree.PoissonArch

end
