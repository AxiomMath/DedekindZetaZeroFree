module

public import DedekindZetaZeroFree.Eisenstein.Induction.Archimedean.UniformHarmonicBands

@[expose] public section

noncomputable section
open scoped Classical NumberField BigOperators
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

namespace UniformAssembly
section
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
 def diagonalUnit (x : ℂ) : ℂˣ := if h : x = 0 then 1 else Units.mk0 x h

 def sectionTuple (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ :=
  ⟨fun v => match v with
    | Sum.inl w => KPLocalCover.sectionMap F ζ hζ (Sum.inl w)
        (Matrix.GeneralLinearGroup.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (r w))
    | Sum.inr _ => 1,
    Filter.Eventually.of_forall (by
      intro v; cases v <;> simp [KPAdelicCoverRestrictedProduct.compact])⟩

private theorem tuple_prod (a : KPAdelicCoverRestrictedProduct.RestrictedCover F ζ hζ)
    (ha : ∀ q, a (Sum.inr q) = 1) :
    a = ((Finset.univ : Finset (InfinitePlace F)).toList.map
      (fun w => KPAdelicCoverRestrictedProduct.localToRestricted F ζ hζ (Sum.inl w)
        (a (Sum.inl w)))).prod := by
  apply RestrictedProduct.ext
  intro v
  change a v = (RestrictedProduct.evalMonoidHom _ v) _
  rw [map_list_prod, List.map_map]
  cases v with
  | inl w =>
    simp only [Function.comp_def, KPAdelicCoverRestrictedProduct.localToRestricted,
      RestrictedProduct.mulSingleMonoidHom_apply]
    simp only [RestrictedProduct.evalMonoidHom_apply, RestrictedProduct.coe_mulSingle_apply]
    have he : (fun x : InfinitePlace F => Pi.mulSingle (Sum.inl x) (a (Sum.inl x)) (Sum.inl w)) =
        fun x => if x = w then a (Sum.inl w) else 1 := by
      funext x
      by_cases h : x = w
      · subst x; simp
      · simp [Pi.mulSingle_apply, Sum.inl_injective.ne h, h]
    rw [he]
    rw [List.prod_map_eq_pow_single w _ (by intro x hx _; simp [hx])]
    rw [List.nodup_iff_count_le_one.mp (Finset.nodup_toList _) w |>.antisymm
      (Nat.succ_le_of_lt (List.count_pos_iff.mpr (by simp)))]
    simp
  | inr q =>
    simp [ha, KPAdelicCoverRestrictedProduct.localToRestricted, Function.comp_def,
      RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_apply]

private theorem sectionTuple_insertion
    (r : InfinitePlace F → Matrix.GeneralLinearGroup (Fin 2) ℂ) :
    KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
        (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ (sectionTuple F ζ hζ r)) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (r w)) := by
  rw [tuple_prod F ζ hζ (sectionTuple F ζ hζ r) (by intro q; rfl)]
  rw [map_list_prod, map_list_prod, List.map_map, List.map_map]
  exact (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.2.2.2 r |>.symm

private theorem mapped_diagonalUnit (w : InfinitePlace F) (x : ℂ) :
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (KPHilbert.infinite_isComplex F ζ hζ w)).symm.toRingHom (diagonalUnit x) =
      (if h : x = 0 then (1 : (w.Completion)ˣ) else Units.mk0
        ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
          (KPHilbert.infinite_isComplex F ζ hζ w)).symm x)
        (by
          intro hx
          apply h
          simpa using congrArg (InfinitePlace.Completion.ringEquivComplexOfIsComplex
            (KPHilbert.infinite_isComplex F ζ hζ w)) hx)) := by
  by_cases hx : x = 0
  · simp [diagonalUnit, hx]
  · simp only [diagonalUnit, hx, ↓reduceDIte]
    apply Units.ext; rfl

end

private theorem update_left_mul
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (a : KPSmoothActualFlowData.GInfinity F)
    (g h : Matrix.ProjGenLinGroup (Fin 2) ℂ) :
    Function.update (fun _ => 1) w g * Function.update a w h =
      Function.update a w (g * h) := by
  funext v
  by_cases hv : v = w <;> simp [hv]

 def singleDiagonal (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) (z : ℂˣ) : KPGlobalTorusFunctionData.TorusArch F :=
  Function.update (fun _ => 1) w z

private theorem diagonal_insertion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (z : KPGlobalTorusFunctionData.TorusArch F) :
    (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (fun w => Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (diagonalUnit (z w)) 1)) := by
  rw [← sectionTuple_insertion]
  change KPAdelicCoverRestrictedProduct.scalarQuotient F ζ hζ
    (KPAdelicCoverRestrictedProduct.amalgamation F ζ hζ _) = _
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q => rfl
  | inl w =>
    change KPStandardLocalRootLifts.A F ζ hζ (Sum.inl w) _ = _
    unfold KPStandardLocalRootLifts.A
    rw [← mapped_diagonalUnit F ζ hζ]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map]

 def singleAdele (F : Type) [Field F] [NumberField F]
    (ζ : F) (hζ : IsPrimitiveRoot ζ 12) (w : InfinitePlace F) (u : ℂ) :
    KPGlobalTorusFunctionData.Adeles F :=
  (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (KPHilbert.infinite_isComplex F ζ hζ w)).symm u), 0)

private theorem unipotent_insertion
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (w : InfinitePlace F) (u : ℂ) :
    KPGlobalTorusFunctionData.N F ζ hζ (singleAdele F ζ hζ w u) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update (fun _ => 1) w
          (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.upperUnipotent u))) := by
  let r : InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 :=
    fun v => KPCplxCharacterHaar.upperUnipotent (if v = w then u else 0)
  have he : (fun v => Matrix.ProjGenLinGroup.mk (r v)) =
      Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.upperUnipotent u)) := by
    funext v
    by_cases hv : v = w
    · subst v; simp [r]
    · have hzero : KPCplxCharacterHaar.upperUnipotent 0 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp [KPCplxCharacterHaar.upperUnipotent]
      simp [r, hv, hzero]
  rw [← he, ← sectionTuple_insertion]
  unfold KPGlobalTorusFunctionData.N
  congr 2
  apply RestrictedProduct.ext
  intro v
  cases v with
  | inr q =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inr q) 0 = 1
    exact KPStandardLocalRootLifts.N_zero F ζ hζ (Sum.inr q)
  | inl v =>
    change KPStandardLocalRootLifts.N F ζ hζ (Sum.inl v) _ = _
    unfold KPStandardLocalRootLifts.N
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    by_cases hv : v = w
    · subst v
      fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map,
        singleAdele, KPAdelicCoverRestrictedProduct.adeleEval, r,
        KPCplxCharacterHaar.upperUnipotent, Pi.single_apply, RingHom.comp_apply, RingHom.fst, Pi.evalRingHom_apply]
      change Pi.single w _ w = _
      simp
    · fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.map,
        singleAdele, KPAdelicCoverRestrictedProduct.adeleEval, r, hv,
        KPCplxCharacterHaar.upperUnipotent, Pi.single_apply, RingHom.comp_apply, RingHom.fst, Pi.evalRingHom_apply]
      change Pi.single w _ v = 0
      simp [Pi.single_apply, hv]

private theorem upper_projective (a d : ℂˣ) (b : ℂ) :
    Matrix.ProjGenLinGroup.mk (KPCplxPrincipalSeriesCharts.upperTriangular a d b) =
      Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (a / d) 1 *
        KPCplxCharacterHaar.upperUnipotent (b / a)) := by
  apply (Matrix.ProjGenLinGroup.mk_eq_mk_iff).mpr
  refine ⟨Units.mk0 ((d : ℂ)⁻¹) (inv_ne_zero d.ne_zero), ?_⟩
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [KPCplxPrincipalSeriesCharts.upperTriangular, KPCplxCharacterHaar.upperUnipotent,
      Matrix.mul_apply, Fin.sum_univ_two, div_eq_mul_inv]
  field_simp

private theorem slice_covariance
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ))
    (w : InfinitePlace F) (a₀ : KPSmoothActualFlowData.GInfinity F)
    (c : KPGlobalTorusFunctionData.finitePart F ζ hζ) :
    KPCplxPrincipalSeriesCharts.HasCovariance KPCplxPrincipalSeriesCharts.positiveParameter
      (fun g => t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a₀ w (Matrix.ProjGenLinGroup.mk g)) * c.val)) := by
  intro a d b g
  let z := singleDiagonal F w (a / d)
  have hz : z ∈ KPGlobalTorusFunctionData.torusArchDomain F := by
    intro v
    by_cases hv : v = w
    · subst v; simp [z, singleDiagonal, Units.ne_zero]
    · simp [z, singleDiagonal, hv]
  have hd : (KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update (fun _ => 1) w (Matrix.ProjGenLinGroup.mk (KubotaRankTwo.d ℂ (a / d) 1))) := by
    rw [diagonal_insertion]
    congr 1
    funext v
    by_cases hv : v = w
    · subst v
      simp only [z, singleDiagonal, Function.update_self]
      have hh : diagonalUnit ((a / d : ℂˣ) : ℂ) = a / d := by
        apply Units.ext; simp [diagonalUnit, Units.ne_zero]
      rw [hh]
    · have hh : KubotaRankTwo.d ℂ 1 1 = 1 := by
        apply Matrix.GeneralLinearGroup.ext
        intro i j
        fin_cases i <;> fin_cases j <;> simp
      simp [z, singleDiagonal, diagonalUnit, hv, hh]
  have he : ((KPGlobalTorusFunctionData.torusArchChart F ζ hζ z).val *
        KPGlobalTorusFunctionData.N F ζ hζ (singleAdele F ζ hζ w (b / a))) *
        (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (Function.update a₀ w (Matrix.ProjGenLinGroup.mk g)) * c.val) =
      KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
        (Function.update a₀ w (Matrix.ProjGenLinGroup.mk
          (KPCplxPrincipalSeriesCharts.upperTriangular a d b * g))) * c.val := by
    rw [hd, unipotent_insertion, ← mul_assoc,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1,
      ← (KPSmoothActualFlowData.archimedean_insertion_properties F ζ hζ).2.1]
    rw [update_left_mul]
    congr 2
    funext v
    by_cases hv : v = w
    · subst v
      simp only [Pi.mul_apply, Function.update_self, map_mul, upper_projective]
    · simp [hv]
  have hp : (∏ v : InfinitePlace F, ‖z v‖ ^ 2) = ‖(a : ℂ) / (d : ℂ)‖ ^ 2 := by
    calc _ = ∏ v : InfinitePlace F, if v = w then ‖(a : ℂ) / (d : ℂ)‖ ^ 2 else 1 := by
          apply Finset.prod_congr rfl
          intro v _
          by_cases hv : v = w <;> simp [z, singleDiagonal, hv]
      _ = _ := by simp
  have hc := ActualRaisingGeometry.source_arch_borel_covariance F ζ hζ t z hz
    (singleAdele F ζ hζ w (b / a))
    (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (Function.update a₀ w (Matrix.ProjGenLinGroup.mk g)) * c.val)
  rw [he, hp] at hc
  convert hc using 2
  unfold KPCplxPrincipalSeriesCharts.inductionWeight KPCplxPrincipalSeriesCharts.complexAbs
  norm_num [KPCplxPrincipalSeriesCharts.positiveParameter]

 theorem su2_fixes (u : KPCplxCharacterHaar.ComplexSU2) :
    KPArch.action (KPCplxCharacterHaar.complexSU2Embedding u) (0, 0) = (0, 0) := by
  have hu := Matrix.mem_unitaryGroup_iff.mp (Matrix.mem_specialUnitaryGroup_iff.mp u.property).1
  have hb := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 1 1) hu
  have hz := congrArg (fun A : Matrix (Fin 2) (Fin 2) ℂ => A 0 1) hu
  have hd := (Matrix.mem_specialUnitaryGroup_iff.mp u.property).2
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
    Matrix.one_apply, ite_true, show (0 : Fin 2) ≠ 1 by decide, ite_false] at hb hz
  have hn : ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
      ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 = 1 := by
    simpa [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_pow] using congrArg Complex.re hb
  have hn' : ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 +
      ‖(u : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 = 1 := by simpa [add_comm] using hn
  ext
  · simpa [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KPCplxCharacterHaar.complexSU2Embedding, hn', add_comm] using hz
  · simp [KPArch.action, KPArch.actionDenominator, KPArch.height,
      KPCplxCharacterHaar.complexSU2Embedding, hn', hd]

 def compactTuple (F : Type) [Field F] [NumberField F]
    (u : InfinitePlace F → KPCplxCharacterHaar.ComplexSU2) :
    KPContSectorArchSphericalFibers.KInfinity F :=
  ⟨fun w => Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding (u w)), by
    rw [KPContSectorArchSphericalFibers.KInfinity, Subgroup.mem_comap,
      MulAction.mem_stabilizer_iff]
    funext i
    change Matrix.ProjGenLinGroup.mk (KPCplxCharacterHaar.complexSU2Embedding
      (u (KPCusp.complexPlace F i))) • ((0, 0) : KPArch.H3) = (0, 0)
    rw [Matrix.ProjGenLinGroup.mk_smul KPArch.scalar_action]
    exact su2_fixes _⟩

private theorem section_mk_eq (s : ℝ)
    (f : KPCplxPrincipalSeriesCharts.PrincipalSeries s)
    (a b : KPCplxCharacterHaar.ComplexGL2)
    (h : Matrix.ProjGenLinGroup.mk a = Matrix.ProjGenLinGroup.mk b) : f a = f b := by
  obtain ⟨z, hz⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h
  rw [← hz, ← Matrix.GeneralLinearGroup.scalar_commute]
  exact (KPCplxPrincipalSeriesCharts.central_invariance s f z a).symm

 abbrev band (N : ℕ) := (Finset.range (N + 1)).sup
  (KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter)

private theorem band_finite (N : ℕ) : FiniteDimensional ℂ (band N) := by
  haveI (i : ℕ) : FiniteDimensional ℂ (KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter i) := by
    haveI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ i) :=
      Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin 3) ℂ i)
    haveI : FiniteDimensional ℂ (KPCplxIntertwinerEigenvalues.harmonicPolynomials i) :=
      Submodule.finiteDimensional_of_le inf_le_left
    have hi := KPCplxIntertwinerEigenvalues.compactRestriction_injective KPCplxPrincipalSeriesCharts.positiveParameter
    haveI : FiniteDimensional ℂ ((KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter i).map
        (KPCplxIntertwinerEigenvalues.compactRestriction KPCplxPrincipalSeriesCharts.positiveParameter)) := by
      rw [KPCplxIntertwinerEigenvalues.harmonicKType, Submodule.map_comap_eq]
      exact Submodule.finiteDimensional_of_le inf_le_right
    exact Module.Finite.of_injective
      ((KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter i).equivMapOfInjective _ hi).toLinearMap
      ((KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter i).equivMapOfInjective _ hi).injective
  infer_instance

private theorem band_kfinite (N : ℕ) (f : band N) :
    KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter f.val := by
  letI := band_finite N
  let R : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter →ₗ[ℂ]
      KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter :=
    { toFun := KPCplxPrincipalSeriesCharts.pi _ (1 : KPCplxCharacterHaar.ComplexPGL2)
      map_add' := by intros; simp [KPCplxPrincipalSeriesCharts.pi_one]
      map_smul' := by intros; simp [KPCplxPrincipalSeriesCharts.pi_one] }
  change FiniteDimensional ℂ (Submodule.span ℂ (Set.range (fun k : KPCplxPrincipalSeriesCharts.compactSubgroup => KPCplxPrincipalSeriesCharts.pi _ k f.val)))
  apply Submodule.finiteDimensional_of_le (S₂ := band N)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let L : KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter →ₗ[ℂ]
      KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter :=
    { toFun := KPCplxPrincipalSeriesCharts.pi _ k
      map_add' := by intro a b; induction k.val using Quotient.inductionOn with | h g => rfl
      map_smul' := by intro a b; induction k.val using Quotient.inductionOn with | h g => rfl }
  have hs : (band N).map L ≤ band N := by
    apply Submodule.map_le_iff_le_comap.mpr
    apply Finset.sup_le
    intro i hi
    intro g hg
    exact (Finset.le_sup (f := KPCplxIntertwinerEigenvalues.harmonicKType KPCplxPrincipalSeriesCharts.positiveParameter) hi) ((KPCplxIntertwinerEigenvalues.harmonicKType_multiplicity_one _ i).1 k g hg)
  exact hs (Submodule.mem_map.mpr ⟨f.val, f.property, rfl⟩)

private theorem extend_covariant_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : (ι → KPCplxCharacterHaar.ComplexGL2) → ℂ)
    (hU : ∀ w a, KPCplxPrincipalSeriesCharts.HasCovariance KPCplxPrincipalSeriesCharts.positiveParameter
      (fun g => U (Function.update a w g)))
    (hV : ∀ w a, KPCplxPrincipalSeriesCharts.HasCovariance KPCplxPrincipalSeriesCharts.positiveParameter
      (fun g => V (Function.update a w g)))
    (hk : ∀ r : ι → KPCplxCharacterHaar.ComplexSU2,
      U (fun w => KPCplxCharacterHaar.complexSU2Embedding (r w)) =
      V (fun w => KPCplxCharacterHaar.complexSU2Embedding (r w))) : ∀ a, U a = V a := by
  have hp : ∀ s : Finset ι, ∀ a,
      (∀ w ∉ s, ∃ k, a w = KPCplxCharacterHaar.complexSU2Embedding k) → U a = V a := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro a ha
      choose r hr using fun w => ha w (by simp)
      have he : a = fun w => KPCplxCharacterHaar.complexSU2Embedding (r w) := funext hr
      rw [he]; exact hk r
    | @insert w s hw ih =>
      intro a ha
      obtain ⟨b, d, z, he⟩ := RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2_factor (a w)
      let k := RepresentationTheory.KPSmoothCoreCasimirEnergy.NoncompactAction.PolynomialDerivatives.noncompactNormalizedSU2 (a w)
      have heq := ih (Function.update a w (KPCplxCharacterHaar.complexSU2Embedding k)) (by
        intro v hv
        by_cases hvw : v = w
        · subst v; exact ⟨k, by simp⟩
        · simpa [hvw] using ha v (by simp [hvw, hv]))
      have hu := hU w a b d z (KPCplxCharacterHaar.complexSU2Embedding k)
      have hv := hV w a b d z (KPCplxCharacterHaar.complexSU2Embedding k)
      rw [← he] at hu hv
      simpa only [Function.update_eq_self] using hu.trans ((congrArg (fun x => (KPCplxPrincipalSeriesCharts.inductionWeight _ b d : ℂ) * x) heq).trans hv.symm)
  intro a
  exact hp Finset.univ a (by simp)

private theorem span_finite_expansion {X M : Type*} [AddCommGroup M] [Module ℂ M]
    (v : X → M) (h : M) (hh : h ∈ Submodule.span ℂ (Set.range v)) :
    ∃ (n : ℕ) (x : Fin n → X) (c : Fin n → ℂ), ∑ i, c i • v (x i) = h := by
  obtain ⟨d, hd⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hh
  let E := Fintype.equivFin d.support
  refine ⟨Fintype.card d.support, fun i => (E.symm i).val, fun i => d (E.symm i).val, ?_⟩
  rw [← E.sum_comp]
  simp only [Equiv.symm_apply_apply]
  have he : (∑ x : d.support, d x.val • v x.val) = ∑ x ∈ d.support, d x • v x := by
    exact Finset.sum_coe_sort d.support (fun x => d x • v x)
  rw [he]
  exact hd

private theorem product_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter)
    (w : ι) (a : ι → KPCplxCharacterHaar.ComplexGL2) :
    KPCplxPrincipalSeriesCharts.HasCovariance KPCplxPrincipalSeriesCharts.positiveParameter
      (fun g => ∏ v, f v (Function.update a w g v)) := by
  intro b d z g
  dsimp only
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ w)]
  conv_rhs => rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ w)]
  simp only [Function.update_self]
  rw [(f w).property.1, mul_assoc]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  have hvw : v ≠ w := by simpa using (Finset.mem_sdiff.mp hv).2
  simp [Function.update_of_ne hvw]

private theorem compact_uniform_pure
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ (n m : ℕ) (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
      (A : Fin n → Fin m → ℂ)
      (f : Fin n → InfinitePlace F → KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter),
      (∀ j w, KPContHolomorphicKGeneration.IsKFinite KPCplxPrincipalSeriesCharts.positiveParameter (f j w)) ∧
      ∀ a : KPContSectorArchSphericalFibers.KInfinity F, ∀ c : KPGlobalTorusFunctionData.finitePart F ζ hζ,
        t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ a.val * c.val) =
          ∑ j, evalCoefficient F ζ hζ t k (A j) c * ∏ w, f j w ((a.val w).out) := by
  classical
  obtain ⟨N, hN⟩ := UniformCompactSeparation.actual_compact_translate_space_mem_uniform_native_bands F ζ hζ t
  obtain ⟨n, m, k, A, b, hb⟩ := UniformCompactSeparation.actual_source_uniform_compact_evaluation_reconstruction F ζ hζ t
  let V : Type := (w : InfinitePlace F) → band (N w)
  let p : V → KPContSectorArchSphericalFibers.KInfinity F → ℂ :=
    fun f a => ∏ w, (f w).val ((a.val w).out)
  have he : ∀ j : Fin n, ∃ (l : ℕ) (f : Fin l → V) (C : Fin l → ℂ),
      ∑ i, C i • p (f i) = (b j).val := by
    intro j
    exact span_finite_expansion p (b j).val (hN (b j).property)
  choose l f C hC using he
  let I := (j : Fin n) × Fin (l j)
  let E := Fintype.equivFin I
  let B : Fin (Fintype.card I) → Fin m → ℂ := fun i v => C (E.symm i).1 (E.symm i).2 * A (E.symm i).1 v
  let g := fun i w => (f (E.symm i).1 (E.symm i).2 w).val
  refine ⟨Fintype.card I, m, k, B, g, ?_, ?_⟩
  · intro i w
    exact band_kfinite _ (f (E.symm i).1 (E.symm i).2 w)
  · intro a c
    rw [hb]
    have hev (j : Fin n) := congrFun (hC j) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hev
    simp_rw [← hev, Finset.mul_sum]
    change (∑ j : Fin n, ∑ i : Fin (l j), evalCoefficient F ζ hζ t k (A j) c * (C j i * p (f j i) a)) = _
    rw [← Fintype.sum_sigma (fun q : I => evalCoefficient F ζ hζ t k (A q.1) c * (C q.1 q.2 * p (f q.1 q.2) a))]
    rw [← E.symm.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [B, g, p]
    have hc : evalCoefficient F ζ hζ t k (fun v => C (E.symm i).1 (E.symm i).2 * A (E.symm i).1 v) c =
        C (E.symm i).1 (E.symm i).2 * evalCoefficient F ζ hζ t k (A (E.symm i).1) c := by
      simp only [evalCoefficient, Finset.mul_sum, mul_assoc]
    rw [hc]
    ring

end UniformAssembly

theorem actual_source_uniform_finite_evaluation_separation
    (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
    (t : KPMsRationalCompactCrossPairing.Vplus F ζ hζ
      (KPContFlatSourceRecipe.D F ζ hζ)) :
    ∃ (n m : ℕ) (k : Fin m → KPContSectorArchSphericalFibers.KInfinity F)
      (A : Fin n → Fin m → ℂ)
      (f : Fin n → NumberField.InfinitePlace F →
        KPCplxPrincipalSeriesCharts.PrincipalSeries KPCplxPrincipalSeriesCharts.positiveParameter),
      (∀ j w, KPContHolomorphicKGeneration.IsKFinite
        KPCplxPrincipalSeriesCharts.positiveParameter (f j w)) ∧
      ∀ (a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2)
        (c : KPGlobalTorusFunctionData.finitePart F ζ hζ),
        t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
          (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val) =
          ∑ j, evalCoefficient F ζ hζ t k (A j) c * ∏ w, f j w (a w) := by
  obtain ⟨n, m, k, A, f, hf, he⟩ := UniformAssembly.compact_uniform_pure F ζ hζ t
  refine ⟨n, m, k, A, f, hf, ?_⟩
  intro a c
  let U := fun a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 =>
    t.val.val (KPSmoothActualFlowData.archimedeanInsertion F ζ hζ
      (fun w => Matrix.ProjGenLinGroup.mk (a w)) * c.val)
  let V := fun a : NumberField.InfinitePlace F → KPCplxCharacterHaar.ComplexGL2 =>
    ∑ j, evalCoefficient F ζ hζ t k (A j) c * ∏ w, f j w (a w)
  apply UniformAssembly.extend_covariant_identity U V
  · intro w a₀
    have hc := UniformAssembly.slice_covariance F ζ hζ t w
      (fun v => Matrix.ProjGenLinGroup.mk (a₀ v)) c
    have hu (g : KPCplxCharacterHaar.ComplexGL2) :
        (fun v => Matrix.ProjGenLinGroup.mk (Function.update a₀ w g v)) =
          Function.update (fun v => Matrix.ProjGenLinGroup.mk (a₀ v)) w (Matrix.ProjGenLinGroup.mk g) := by
      funext v
      by_cases hv : v = w <;> simp [hv]
    simpa only [U, hu] using hc
  · intro w a₀ b d z g
    have hp := fun j => UniformAssembly.product_covariance (f j) w a₀ b d z g
    dsimp only [V]
    simp_rw [hp]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro r
    let q := UniformAssembly.compactTuple F r
    have hq := he q c
    have hh (j : Fin n) (w : NumberField.InfinitePlace F) :
        f j w ((q.val w).out) = f j w (KPCplxCharacterHaar.complexSU2Embedding (r w)) := by
      apply UniformAssembly.section_mk_eq
      exact Quotient.out_eq (q.val w)
    simp_rw [hh] at hq
    exact hq

end DedekindZetaZeroFree.KPGlobalResidualConstruction.ActualRaisingLocal.SphericalReseeding

end
