module

public import DedekindZetaZeroFree.Metaplectic.Torus.ReferenceTensorEvaluation

@[expose] public section

noncomputable section
open scoped NumberField Classical
open NumberField IsDedekindDomain ValuativeRel
namespace DedekindZetaZeroFree.EisensteinReferenceSections.LocalSeed
open KPGlobalTorusFiniteStages KPLocalPrincipalSeries
variable (F : Type) [Field F] [NumberField F] (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (P : CompatibleModelData F ζ hζ) (C : LocalFiberData F ζ hζ P)
set_option backward.isDefEq.respectTransparency false

def spherical (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional) :
    sectionSpace (C.canonical q).borel (C.polarization q) .plus 0 :=
  (KPLocalGoodSphericalImage.normalized_plus_spherical_vector
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa
    (C.unramified q hq)).choose

theorem spherical_fixed (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional) :
    spherical F ζ hζ P C q hq ∈ fixedSubmodule
      (IPlus (C.canonical q).borel (C.polarization q))
      (C.canonical q).iwasawa.compact.toOpenSubgroup :=
  (KPLocalGoodSphericalImage.normalized_plus_spherical_vector
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa
    (C.unramified q hq)).choose_spec.1.1

theorem spherical_one_one (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional) :
    ((spherical F ζ hζ P C q hq).val 1).val 1 = 1 :=
  (KPLocalGoodSphericalImage.normalized_plus_spherical_vector
    (C.canonical q).borel (C.polarization q) (C.canonical q).iwasawa
    (C.unramified q hq)).choose_spec.1.2

theorem spherical_one (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional) :
    (spherical F ζ hζ P C q hq).val 1 = localReference F ζ hζ P C q := by
  apply (referenceGoodSpherical F ζ hζ P C q hq).2.2
  · intro j
    let b := (C.canonical q).borel.torus j.val
    have hb : (b : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) ∈
        (C.canonical q).iwasawa.compact.toOpenSubgroup := j.property
    have hf := spherical_fixed F ζ hζ P C q hq ⟨b.val, hb⟩
    have hev := congrArg (fun f => f.val 1) hf
    change (spherical F ζ hζ P C q hq).val (1 * b.val) =
      (spherical F ζ hζ P C q hq).val 1 at hev
    rw [one_mul] at hev
    have hc := (spherical F ζ hζ P C q hq).property.1 b 1
    rw [mul_one] at hc
    have hn := (C.canonical q).iwasawa.intersection_norm b hb
    have hjn : localAbs (KPLocalExceptionalConstruction.LocalField F q)
        ((C.canonical q).borel.coordinate j.val) = 1 := by
      simpa only [b, (C.canonical q).borel.retract_torus] using hn
    simpa [b, inducingAction, inducingScalar, deltaHalf, normPower, hjn,
      borelAction, (C.canonical q).borel.retract_torus] using hc.symm.trans hev
  · exact spherical_one_one F ζ hζ P C q hq

theorem spherical_right_fixed (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional)
    (k : (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (g : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :
    (spherical F ζ hζ P C q hq).val (g * k.val) =
      (spherical F ζ hζ P C q hq).val g :=
  congrArg (fun f => f.val g) (spherical_fixed F ζ hζ P C q hq k)

theorem exists_section_one (q : HeightOneSpectrum (𝓞 F))
    (v : LocalFiber F ζ hζ P C q) :
    ∃ f : sectionSpace (C.canonical q).borel (C.polarization q) .plus 0,
      f.val 1 = v := by
  let O : Set (KPLocalExceptionalConstruction.LocalField F q) :=
    (valuation (KPLocalExceptionalConstruction.LocalField F q)).integer
  have ho : IsClopen O :=
    (valuation (KPLocalExceptionalConstruction.LocalField F q)).isClopen_integer
  have hc : IsCompact O :=
    IsNonarchimedeanLocalField.isCompact_closedBall
      (KPLocalExceptionalConstruction.LocalField F q) 1
  let φ := O.indicator (fun _ => v)
  have hφ : IsLocallyConstant φ := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ O
    · filter_upwards [ho.isOpen.mem_nhds hx] with y hy
      simp [φ, Set.indicator_of_mem, hx, hy]
    · filter_upwards [ho.isClosed.isOpen_compl.mem_nhds hx] with y hy
      have hy' : y ∉ O := hy
      simp [φ, Set.indicator_of_notMem, hx, hy']
  have hcs : HasCompactSupport φ :=
    HasCompactSupport.intro hc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨f, hf, _⟩ := (KPRankOneOpenCellKernel.open_cell_correspondence
    F ζ hζ q (C.canonical q).borel (C.polarization q)
    ((C.canonical q).openCell (C.polarization q)) .plus 0).2 φ hφ hcs
  refine ⟨IPlus (C.canonical q).borel (C.polarization q)
    (KPRankOneOpenCellKernel.openCoordinate F ζ hζ q 0) f, ?_⟩
  change f.val (1 * KPRankOneOpenCellKernel.openCoordinate F ζ hζ q 0) = v
  rw [one_mul, hf.2]
  exact Set.indicator_of_mem
    (show (0 : KPLocalExceptionalConstruction.LocalField F q) ∈ O from
      (valuation (KPLocalExceptionalConstruction.LocalField F q)).integer.zero_mem) _

def finite (q : HeightOneSpectrum (𝓞 F)) :
    sectionSpace (C.canonical q).borel (C.polarization q) .plus 0 :=
  if hq : q ∉ C.exceptional then spherical F ζ hζ P C q hq
  else (exists_section_one F ζ hζ P C q (localReference F ζ hζ P C q)).choose

@[simp] theorem finite_one (q : HeightOneSpectrum (𝓞 F)) :
    (finite F ζ hζ P C q).val 1 = localReference F ζ hζ P C q := by
  by_cases hq : q ∉ C.exceptional
  · rw [finite, dif_pos hq]
    exact spherical_one F ζ hζ P C q hq
  · rw [finite, dif_neg hq]
    exact (exists_section_one F ζ hζ P C q (localReference F ζ hζ P C q)).choose_spec

@[simp] theorem finite_one_one (q : HeightOneSpectrum (𝓞 F)) :
    ((finite F ζ hζ P C q).val 1).val 1 = 1 := by
  rw [finite_one, TorusReference.localReference_one]

theorem finite_right_fixed (q : HeightOneSpectrum (𝓞 F)) (hq : q ∉ C.exceptional)
    (k : (C.canonical q).iwasawa.compact.toOpenSubgroup)
    (g : KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :
    (finite F ζ hζ P C q).val (g * k.val) = (finite F ζ hζ P C q).val g := by
  simpa only [finite, dif_pos hq] using spherical_right_fixed F ζ hζ P C q hq k g

theorem finite_has_level (q : HeightOneSpectrum (𝓞 F)) :
    ∃ J : CompactOpenLevel (KPLocalExceptionalConstruction.ActualCover F ζ hζ q),
      (J.toOpenSubgroup : Subgroup (KPLocalExceptionalConstruction.ActualCover F ζ hζ q)) ≤
        ((C.canonical q).iwasawa.compact.toOpenSubgroup : Subgroup _) ∧
      ∀ (k : J.toOpenSubgroup) g,
        (finite F ζ hζ P C q).val (g * k.val) = (finite F ζ hζ P C q).val g := by
  obtain ⟨U, hU⟩ := (finite F ζ hζ P C q).property.2
  let J : CompactOpenLevel (KPLocalExceptionalConstruction.ActualCover F ζ hζ q) :=
    ⟨(C.canonical q).iwasawa.compact.toOpenSubgroup ⊓ U,
      (C.canonical q).iwasawa.compact.isCompact.inter_right U.isClosed⟩
  exact ⟨J, inf_le_left, fun k g => congrFun (hU k.val k.property.2) g⟩

end DedekindZetaZeroFree.EisensteinReferenceSections.LocalSeed

end
