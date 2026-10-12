module

public import DedekindZetaZeroFree.Arithmetic.Units.SArithmeticData
public import DedekindZetaZeroFree.Arithmetic.Kummer.TwelfthRootsTotallyComplex

@[expose] public section

section

namespace DedekindZetaZeroFree.SUnitStructureAdapter

noncomputable def finiteCoordinates {ι : Type*} [Finite ι] :
    Multiplicative (ι →₀ ℤ) ≃* Multiplicative (ι → ℤ) :=
  { Finsupp.equivFunOnFinite with
    map_mul' := fun x y => rfl }

end DedekindZetaZeroFree.SUnitStructureAdapter

end

section

open scoped NumberField
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree.SUnitStructureAdapter

theorem logRank_totallyComplex {F : Type*} [Field F] [NumberField F]
    [IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    SUnitGroup.logRank S = InfinitePlace.nrComplexPlaces F + S.card - 1 := by
  rw [SUnitGroup.logRank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

end DedekindZetaZeroFree.SUnitStructureAdapter

end

section

open scoped NumberField Classical
open NumberField IsDedekindDomain

namespace DedekindZetaZeroFree
namespace SArithmeticData

noncomputable section

variable {F : Type} [Field F] [NumberField F] (A : SArithmeticData F)

def sunitRank : ℕ := InfinitePlace.nrComplexPlaces F + A.Sf.card - 1

theorem infinitePlace_card (A : SArithmeticData F) : Fintype.card (InfinitePlace F) =
    InfinitePlace.nrComplexPlaces F := by
  letI : IsTotallyComplex F :=
    primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]

include A in

theorem complexPlace_pos : 0 < InfinitePlace.nrComplexPlaces F := by
  rw [← A.infinitePlace_card]
  exact Fintype.card_pos

theorem sunitRank_add_one (A : SArithmeticData F) : A.sunitRank + 1 =
    InfinitePlace.nrComplexPlaces F + A.Sf.card := by
  have h := A.complexPlace_pos
  dsimp [sunitRank]
  omega

def unitStructure : A.Rˣ ≃*
    NumberField.Units.torsion F × Multiplicative (Fin A.sunitRank → ℤ) := by
  letI : IsTotallyComplex F :=
    primitive12_totallyComplex F A.zeta12 A.primitive_zeta12
  have hrank : SUnitGroup.logRank A.Sf = A.sunitRank :=
    SUnitStructureAdapter.logRank_totallyComplex A.Sf
  let upstream := A.unitEquiv.symm.trans (SUnitGroup.decomposition A.Sf)
  let coordinates : Multiplicative (Fin (SUnitGroup.logRank A.Sf) →₀ ℤ) ≃*
      Multiplicative (Fin A.sunitRank → ℤ) := by
    rw [hrank]
    exact SUnitStructureAdapter.finiteCoordinates
  exact upstream.trans ((MulEquiv.refl (NumberField.Units.torsion F)).prodCongr coordinates)

theorem torsion_finite : Finite (NumberField.Units.torsion F) := inferInstance

def ordinaryTorsionInclusion : NumberField.Units.torsion F →* A.Rˣ :=
  (Units.map (algebraMap (𝓞 F) A.R)).comp
    (NumberField.Units.torsion F).subtype

end
end SArithmeticData
end DedekindZetaZeroFree

end
