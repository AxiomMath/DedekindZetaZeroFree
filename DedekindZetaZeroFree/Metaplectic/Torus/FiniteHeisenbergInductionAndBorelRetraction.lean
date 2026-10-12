module

public import DedekindZetaZeroFree.Metaplectic.Torus.CubicHeisenbergInducingData
public import DedekindZetaZeroFree.Metaplectic.Kubota.CubicPGL.CompactIwasawa

@[expose] public section

attribute [local instance 2000] DedekindZetaZeroFree.KPRankOneOpenCellKernel.coverTopology

open scoped NumberField Valued
open NumberField IsDedekindDomain MeasureTheory ValuativeRel

namespace DedekindZetaZeroFree.KPExceptionalRaw

open KPLocalPrincipalSeries KPLocalStoneVonNeumann
open KPRankOneShellContinuation

noncomputable section
set_option autoImplicit false

variable (F : Type) [Field F] [NumberField F]
variable (ζ : F) (hζ : IsPrimitiveRoot ζ 12)
variable (q : HeightOneSpectrum (𝓞 F))

theorem ordinaryIota_injective : Function.Injective (ordinaryIota F ζ hζ) := by
  intro x y h
  have h' := KPLocalCover.coefficientEmbedding_injective F ζ hζ h
  apply Subtype.ext
  exact congrArg (fun z : rootsOfUnity 6 F => (z : Fˣ)) h'

theorem raw_split_scalars (z : (LocalField F q)ˣ) :
    KPPGLLocalCover.coverQuotient F ζ hζ (Sum.inr q)
      (KPScalarSplitCentral.scalarHom F ζ hζ (Sum.inr q) z) = 1 := by
  apply (QuotientGroup.eq_one_iff _).mpr
  exact ⟨z, rfl⟩

theorem raw_prescribed_center {D : Type} [CommGroup D] [Finite D]
    (T : LocalHeisenbergData (actualTorus F ζ hζ q) D)
    (A : LocalBorelData (K := LocalField F q) (G := ActualCover F ζ hζ q) T)
    (central : rootsOfUnity 3 F →* T.C)
    (hcentral : ∀ e, T.ω (central e) = ordinaryIota F ζ hζ e)
    (e : rootsOfUnity 3 F) (x y : (LocalField F q)ˣ) :
    (T.ω (central e * A.cubeLift (x / y)) : ℂ) =
      (ordinaryIota F ζ hζ e : ℂ) *
        normPower (LocalField F q) (x ^ 3 / y ^ 3) (1 / 6) := by
  rw [map_mul, Units.val_mul, hcentral, A.exceptional_cube, div_pow]

theorem exists_rawFiniteInducingData :
    Nonempty (RawFiniteInducingData F ζ hζ q) := by
  classical
  letI := ActualFiniteTorus.finiteCubeClasses F ζ hζ q
  obtain ⟨A, hB, hcoord, hcube, htorus, hratio, _, _, _, hopen⟩ :=
    ActualFiniteBorel.actual_openCell_binding F ζ hζ q
  obtain ⟨P⟩ := (ActualFiniteTorus.actual_heisenberg_and_polarization F ζ hζ q).2.2.2.2
  obtain ⟨I, _⟩ := ActualFiniteBorel.actual_compact_iwasawa F ζ hζ q
    (ActualFiniteBorel.chartDepth F ζ hζ q)
    (ActualFiniteBorel.chartDepth_admissible F ζ hζ q)
    (ActualFiniteTorus.actualHeisenberg F ζ hζ q) A hB hratio
  let central := ActualFiniteTorus.centerInjection F ζ hζ q
  have hcentral : ∀ e,
      (ActualFiniteTorus.actualHeisenberg F ζ hζ q).ω (central e) =
        ordinaryIota F ζ hζ e := by
    intro e
    change ActualFiniteTorus.rawCenterValue F ζ hζ q
      (ActualFiniteTorus.centerInjection F ζ hζ q e) = ActualFiniteTorus.ordinaryIota F ζ hζ e
    apply Units.ext
    have hv := (ActualFiniteTorus.prescribed_center_character F ζ hζ q).2.2.2.2.1 e 1
    simpa [normPower, localAbs_one] using hv
  refine ⟨{
    D := ActualFiniteTorus.D F q
    cubeClassEquiv := MulEquiv.refl _
    heisenberg := ActualFiniteTorus.actualHeisenberg F ζ hζ q
    borel := A
    borel_eq := hB
    torus_full := htorus
    coordinate_lift := ?_
    cube_class := ?_
    center_exact := rfl
    cube_actual := ?_
    central := central
    central_actual := fun _ => rfl
    central_character := hcentral
    center_parameterization := ?_
    prescribed_center := raw_prescribed_center F ζ hζ q _ A central hcentral
    split_scalars := raw_split_scalars F ζ hζ q
    polarization := P
    iwasawa := I
    openCell := fun Q => Classical.choose (hopen Q)
    openCell_ordinary := fun Q => (Classical.choose_spec (hopen Q)).1 }⟩
  · intro t y ht
    rw [hcoord]
    apply ((ActualFiniteTorus.actual_torus_normal_form F ζ hζ q).2.2.2.2.2.2 1 y t _).1
    simpa [ActualFiniteTorus.normalWord] using ht
  · intro t
    rw [hcoord]
    rfl
  · intro y
    rw [hcube]
    change ActualFiniteTorus.normalWord F ζ hζ q 1 (y ^ 3) = _
    simp [ActualFiniteTorus.normalWord]
  · intro c
    obtain ⟨⟨e, v⟩, hv, _⟩ :=
      (ActualFiniteTorus.actual_center_cube_normal_form F ζ hζ q).2.2.2.2.1 c
    obtain ⟨y, hy⟩ := v.property
    refine ⟨e, y, 1, ?_⟩
    rw [div_one, hcube]
    apply Subtype.ext
    change (c : actualTorus F ζ hζ q) =
      ActualFiniteTorus.central F ζ hζ q e * ActualFiniteTorus.torusLift F ζ hζ q (y ^ 3)
    change y ^ 3 = (v : (LocalField F q)ˣ) at hy
    rw [hy]
    exact hv

end
end DedekindZetaZeroFree.KPExceptionalRaw
