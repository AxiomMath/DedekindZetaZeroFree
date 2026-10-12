module

public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Torus.Periodisation
public import DedekindZetaZeroFree.HarmonicAnalysis.Haar.Lattices.BasisCoordinateVolumes
public import DedekindZetaZeroFree.HarmonicAnalysis.Fourier.Lattices.PeriodisationUnfolding

@[expose] public section

noncomputable section
open scoped FourierTransform SchwartzMap
open Module MeasureTheory

namespace DedekindZetaZeroFree.PoissonArch

private theorem integrableOn_character_periodisation
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (f : 𝓢(V, ℂ)) (w : V) :
    IntegrableOn (fun v : V => (𝐞 (-inner ℝ v w) : ℂ) • periodisation L f v)
      (basisDomain L b) volume := by
  classical
  have hboxmeas : MeasurableSet (coordinateBoxIco ι) := by
    rw [coordinateBoxIco]
    exact MeasurableSet.univ_pi' (fun _ => measurableSet_Ico)
  have hDmeas : MeasurableSet (basisDomain L b) := by
    rw [basisDomain]
    rw [Set.image_eq_preimage_of_inverse
      (fun x => (b.ofZLatticeBasis ℝ L).equivFun.apply_symm_apply x)
      (fun x => (b.ofZLatticeBasis ℝ L).equivFun.symm_apply_apply x)]
    exact hboxmeas.preimage (continuous_equivFun_basis (b.ofZLatticeBasis ℝ L)).measurable
  have hsub : basisDomain L b ⊆ (b.ofZLatticeBasis ℝ L).equivFun.symm ''
      (Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1)) := by
    intro x hx
    simp only [basisDomain, coordinateBoxIco] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, by
      rw [Set.mem_univ_pi]
      intro i
      exact ⟨(hy i).1, le_of_lt (hy i).2⟩, rfl⟩
  have hKc : IsCompact ((b.ofZLatticeBasis ℝ L).equivFun.symm ''
      (Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1))) :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).image
      ((b.ofZLatticeBasis ℝ L).equivFun.symm.toLinearMap.continuous_of_finiteDimensional)
  have hDfin : volume (basisDomain L b) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) hKc.measure_lt_top
  have hchar : Continuous (fun v : V => (𝐞 (-inner ℝ v w) : ℂ)) := by fun_prop
  have hcont : Continuous (fun v : V => (𝐞 (-inner ℝ v w) : ℂ) • periodisation L f v) :=
    hchar.smul (continuous_periodisation L f)
  have hgmeas : AEStronglyMeasurable
      (fun v : V => (𝐞 (-inner ℝ v w) : ℂ) • periodisation L f v)
      (volume.restrict (basisDomain L b)) := hcont.aestronglyMeasurable
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (continuous_periodisation L f).continuousOn
  refine IntegrableOn.of_bound hDfin hgmeas C ?_
  filter_upwards [self_mem_ae_restrict hDmeas] with x hx
  calc ‖(𝐞 (-inner ℝ x w) : ℂ) • periodisation L f x‖ = ‖periodisation L f x‖ := by
        rw [norm_smul, Circle.norm_coe, one_mul]
    _ ≤ C := hC x (hsub hx)

theorem torusPeriodisation_mFourierCoeff
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Fintype ι] (b : Basis ι ℤ L) (f : 𝓢(V, ℂ))
    (n : ι → ℤ) :
    UnitAddTorus.mFourierCoeff (torusPeriodisation b f : UnitAddTorus ι → ℂ) n =
      (ZLattice.covolume L volume : ℂ)⁻¹ *
        (𝓕 (f : V → ℂ)) (dualVector_b L b n : V) := by
  classical
  rw [UnitAddTorus.mFourierCoeff_eq_integral (torusPeriodisation b f) n (fun _ => (0 : ℝ))]
  have hbox : ({x : ι → ℝ | ∀ i, x i ∈ Set.Ioc (0:ℝ) (0 + 1)} : Set (ι → ℝ)) =
      coordinateBoxIoc ι := by
    simp [coordinateBoxIoc]
  rw [hbox]
  have hfun : (fun x : ι → ℝ =>
        (UnitAddTorus.mFourier (-n)) (fun i => (x i : UnitAddCircle)) •
          torusPeriodisation b f (fun i => (x i : UnitAddCircle)))
      = (fun x : ι → ℝ =>
          (𝐞 (-inner ℝ ((b.ofZLatticeBasis ℝ L).equivFun.symm x)
            ((dualVector_b L b n : dualLattice L) : V)) : ℂ) •
          periodisation L f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) := by
    funext x
    rw [torusPeriodisation_coe b f x]
    congr 1
    rw [dualVector_b_fourierChar L b ((b.ofZLatticeBasis ℝ L).equivFun.symm x) n]
    congr 1
    funext i
    rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [hfun]
  trans (ZLattice.covolume L volume : ℂ)⁻¹ * ∫ v in basisDomain L b,
      (𝐞 (-inner ℝ v ((dualVector_b L b n : dualLattice L) : V)) : ℂ) • periodisation L f v
  · exact integral_basis_coordinates_Ioc L b
      (fun v : V => (𝐞 (-inner ℝ v ((dualVector_b L b n : dualLattice L) : V)) : ℂ) •
        periodisation L f v)
      (integrableOn_character_periodisation L b f ((dualVector_b L b n : dualLattice L) : V))
  · congr 1
    exact periodisation_fourierCoefficient_eq_fourier L f (basisDomain L b)
      (by
        rw [basisDomain]
        rw [Set.image_eq_preimage_of_inverse
          (fun x => (b.ofZLatticeBasis ℝ L).equivFun.apply_symm_apply x)
          (fun x => (b.ofZLatticeBasis ℝ L).equivFun.symm_apply_apply x)]
        rw [coordinateBoxIco]
        exact (MeasurableSet.univ_pi' (fun _ => measurableSet_Ico)).preimage
          (continuous_equivFun_basis (b.ofZLatticeBasis ℝ L)).measurable)
      (basisDomain_isAddFundamentalDomain L b)
      (by
        have hsub : basisDomain L b ⊆ (b.ofZLatticeBasis ℝ L).equivFun.symm ''
            (Set.pi Set.univ (fun _ : ι => Set.Icc (0:ℝ) 1)) := by
          intro x hx
          simp only [basisDomain, coordinateBoxIco] at hx
          obtain ⟨y, hy, rfl⟩ := hx
          exact ⟨y, by
            rw [Set.mem_univ_pi]
            intro i
            exact ⟨(hy i).1, le_of_lt (hy i).2⟩, rfl⟩
        exact lt_of_le_of_lt (measure_mono hsub)
          ((isCompact_univ_pi (fun _ => isCompact_Icc)).image
            ((b.ofZLatticeBasis ℝ L).equivFun.symm.toLinearMap.continuous_of_finiteDimensional)).measure_lt_top)
      (dualVector_b L b n)

end DedekindZetaZeroFree.PoissonArch

end
