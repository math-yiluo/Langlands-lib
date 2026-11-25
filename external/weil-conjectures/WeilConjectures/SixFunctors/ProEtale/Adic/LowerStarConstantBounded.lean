/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitReplete
public import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAb
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
public import WeilConjectures.SixFunctors.ProEtale.Adic.IntegersSheafLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.AbelianConstant
public import WeilConjectures.SixFunctors.ProEtale.Adic.RightDerivedLowerStarColimit
public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetLowerStar

/-!
# Boundedness of the derived pushforward of the constant `ℓ`-adic sheaf

Let `g : T ⟶ Y` be a quasi-compact quasi-separated morphism of schemes of finite type over a
field `k`, with `dim T ≤ d`. Then the derived pushforward of the constant `ℓ`-adic sheaf
`ℚ̄_ℓ,T` lies in degrees `[0, 2d + 1]`
(`AlgebraicGeometry.ProEtale.bounded_rightDerivedFunctor_adicLowerStar_unit`), the boundedness
half of the finiteness theorem (`WeilConjectures.SixFunctors.ProEtale.Adic.LowerStar`) for the
constant sheaf. The argument runs through the abelian sheaves underlying the `ℓ`-adic sheaves:

1. `Rg_* 𝒪_{E,T} = R lim_n ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`, and the étale terms lie in degrees
   `[0, 2d]` (`AlgebraicGeometry.Etale.isGE_and_isLE_rightDerivedLowerStar_constantSheaf_ab`), so
   by repleteness `Rg_* 𝒪_{E,T}` lies in degrees `[0, 2d + 1]`
   (`AlgebraicGeometry.ProEtale.isGE_and_isLE_of_isHomotopyLimit_proEt`,
   `AlgebraicGeometry.ProEtale.isGE_and_isLE_rightDerivedLowerStar_padicIntegersSheaf`);
2. `Rⁱg_*` commutes with the colimits `E_T = 𝒪_{E,T}[1/ℓ]` and `ℚ̄_ℓ,T = colim_E E_T`, so
   `Rⁱg_* ℚ̄_ℓ,T = 0` for `i > 2d + 1`
   (`AlgebraicGeometry.ProEtale.isZero_rightDerived_lowerStar_adicConstantSheaf`);
3. the derived pushforward of `ℓ`-adic sheaves commutes with taking underlying abelian sheaves
   (`AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarCompForgetAbIso`), which is faithful.

The comparison `Rg_* ν^* ≅ ν^* Rg_*^{ét}` used in step 1 depends on
`AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Pretriangulated

namespace AlgebraicGeometry.ProEtale

/-- **Range of a derived limit of abelian pro-étale sheaves**: a derived limit of a tower of
objects of `D(X_proét, Ab)` lying in degrees `[a, b]` lies in degrees `[a, b + 1]`, the
pro-étale topos being replete. -/
theorem isGE_and_isLE_of_isHomotopyLimit_proEt {X : Scheme.{u}}
    {F : ℕᵒᵖ ⥤ DerivedCategory (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})}
    {c : Cone F} (hc : IsHomotopyLimit c) (a b : ℤ)
    (hF : ∀ n : ℕ, (F.obj (op n)).IsGE a ∧ (F.obj (op n)).IsLE b) :
    c.pt.IsGE a ∧ c.pt.IsLE (b + 1) := by
  refine DerivedCategory.isGE_and_isLE_of_isHomotopyLimit hc a (b + 1)
    (fun n ↦ ⟨(hF n).1, ?_⟩) (fun n ↦ ?_) fun G _ hP t ht hG ↦
      epi_one_sub_of_epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_ab hG hP t ht
  · have := (hF n).2
    exact DerivedCategory.TStructure.t.isLE_of_le _ b (b + 1) (by lia)
  · have := (hF n).2
    exact ⟨fun _ _ _ ↦ (DerivedCategory.isZero_of_isLE _ b (b + 1) (by lia)).eq_of_src _ _⟩

open PadicAlgCl in
lemma isAddTorsion_uliftIntegersModPow (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl l)] (n : ℕ) :
    IsAddTorsion (ULift.{u + 1} (integersModPow l E n)) := by
  intro x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_⟩
  obtain ⟨y, hy⟩ := integersModPowMk_surjective l E n x.down
  refine ULift.ext ?_
  change (l ^ n) • x.down = 0
  rw [← hy, nsmul_eq_mul, ← map_natCast (integersModPowMk l E n), ← map_mul]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_span_singleton.2 (Dvd.intro y (by push_cast; ring)))

open PadicAlgCl in
/-- **Boundedness of `Rg_* 𝒪_{E,T}`**: for `g : T ⟶ Y` quasi-compact and quasi-separated between
schemes of finite type over a field with `dim T ≤ d`, the derived pushforward of the abelian
sheaf `𝒪_{E,T}` on the pro-étale site lies in degrees `[0, 2d + 1]`. It is the derived limit of
the `ν^* Rg_*^{ét}(𝒪_E ⧸ ℓⁿ)`
(`isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower`),
which lie in degrees `[0, 2d]`
(`AlgebraicGeometry.Etale.isGE_and_isLE_rightDerivedLowerStar_constantSheaf_ab`). -/
theorem isGE_and_isLE_rightDerivedLowerStar_padicIntegersSheaf {k : Type u} [Field k]
    {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (aT : T ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT]
    [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT) (d : ℕ)
    (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (l : ℕ) [Fact l.Prime] (E : Type) [Field E]
    [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] :
    letI := normedFieldOfAlgebra l E
    ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (continuousMapAbSheaf T (integers l E)))).IsGE 0 ∧
    ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor.obj
        ((DerivedCategory.singleFunctor _ 0).obj (continuousMapAbSheaf T (integers l E)))).IsLE
      (2 * (d : ℤ) + 1) := by
  let := normedFieldOfAlgebra l E
  refine isGE_and_isLE_of_isHomotopyLimit_proEt
    (isHomotopyLimit_comparisonUpperStar_rightDerivedLowerStar_constantSheafTower g l E) 0
    (2 * (d : ℤ)) fun n ↦ ?_
  obtain ⟨h₁, h₂⟩ := Etale.isGE_and_isLE_rightDerivedLowerStar_constantSheaf_ab
    (Λ := ULift.{u + 1} (integersModPow l E n)) (isAddTorsion_uliftIntegersModPow l E n)
    aT aY g hg d hd
  have h₁ : (DerivedCategory.Plus.ι.obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheafTower T (integersModPowTransition l E)).obj (Opposite.op n))))).IsGE 0 := h₁
  have h₂ : (DerivedCategory.Plus.ι.obj
      ((Etale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctorPlus.obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((constantSheafTower T (integersModPowTransition l E)).obj (Opposite.op n))))).IsLE
      (2 * (d : ℤ)) := h₂
  exact ⟨(comparisonUpperStar AddCommGrpCat.{u + 1} Y).isGE_mapDerivedCategory_obj _ 0,
    (comparisonUpperStar AddCommGrpCat.{u + 1} Y).isLE_mapDerivedCategory_obj _ _⟩

section Vanishing

variable {k : Type u} [Field k] {T Y : Scheme.{u}} (g : T ⟶ Y) [QuasiCompact g]
  [QuasiSeparated g] (aT : T ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType aT]
  [QuasiCompact aT] [LocallyOfFiniteType aY] [QuasiCompact aY] (hg : g ≫ aY = aT) (d : ℕ)
  (hd : topologicalKrullDim T ≤ (d : WithBot ℕ∞)) (l : ℕ) [Fact l.Prime]

include aT aY hg hd

open PadicAlgCl in
/-- `Rⁱg_* 𝒪_{E,T} = 0` for `i > 2d + 1`. -/
lemma isZero_rightDerived_lowerStar_padicIntegersSheaf (E : Type) [Field E]
    [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] (i : ℕ) (hi : 2 * d + 1 < i) :
    letI := normedFieldOfAlgebra l E
    IsZero (((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived i).obj
      (continuousMapAbSheaf T (integers l E))) := by
  let := normedFieldOfAlgebra l E
  have := (isGE_and_isLE_rightDerivedLowerStar_padicIntegersSheaf g aT aY hg d hd l E).2
  exact (DerivedCategory.isZero_of_isLE _ (2 * (d : ℤ) + 1) i (by lia)).of_iso
    ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).homologyRightDerivedFunctorObjSingleFunctorIso
      _ i).symm

open PadicAlgCl in
/-- `Rⁱg_* E_T = 0` for `i > 2d + 1`: it is the colimit of the `Rⁱg_* 𝒪_{E,T}`. -/
lemma isZero_rightDerived_lowerStar_padicSubfieldSheaf (E : Type) [Field E]
    [Algebra E (PadicAlgCl l)] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
    [FiniteDimensional ℚ_[l] E] (i : ℕ) (hi : 2 * d + 1 < i) :
    letI := normedFieldOfAlgebra l E
    IsZero (((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived i).obj
      (continuousMapAbSheaf T E)) := by
  let := normedFieldOfAlgebra l E
  have hc := isColimitRightDerivedLowerStarPadicSubfieldSheafCocone g l E i
  exact (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun n ↦
    (isZero_rightDerived_lowerStar_padicIntegersSheaf g aT aY hg d hd l E i hi).eq_of_src _ _)

/-- `Rⁱg_* ℚ̄_ℓ,T = 0` for `i > 2d + 1`, for the abelian sheaf underlying the constant `ℓ`-adic
sheaf: it is the colimit of the `Rⁱg_* E_T` over the finite subextensions `E ⊆ ℚ̄_ℓ`. -/
lemma isZero_rightDerived_lowerStar_adicConstantSheaf (i : ℕ) (hi : 2 * d + 1 < i) :
    IsZero (((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived i).obj
      ((sheafCompose (Scheme.ProEt.topology T) (forget₂ (WeilCoefficients.{u} l)
        AddCommGrpCat.{u + 1})).obj (adicConstantSheaf l T))) := by
  have hc := isColimitRightDerivedLowerStarAdicConstantSheafCocone g l i
  exact (IsZero.iff_id_eq_zero _).2 (hc.hom_ext fun E ↦
    (isZero_rightDerived_lowerStar_padicSubfieldSheaf g aT aY hg d hd l E.1 i hi).eq_of_src _ _)

/-- **Boundedness of the derived pushforward of the constant `ℓ`-adic sheaf**: for
`g : T ⟶ Y` quasi-compact and quasi-separated between schemes of finite type over a field with
`dim T ≤ d`, the derived pushforward `Rg_* ℚ̄_ℓ,T` of `ℓ`-adic sheaves vanishes in degrees
`> 2d + 1`. Its cohomology sheaves have underlying abelian sheaves the `Rⁱg_*` of the abelian
sheaf underlying `ℚ̄_ℓ,T` (`AlgebraicGeometry.ProEtale.rightDerivedAdicLowerStarCompForgetAbIso`),
which vanish (`AlgebraicGeometry.ProEtale.isZero_rightDerived_lowerStar_adicConstantSheaf`). -/
theorem isLE_rightDerivedFunctor_adicLowerStar_unit :
    ((g)_*ᵃ[l].rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l T))).IsLE (2 * (d : ℤ) + 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  let K := (DerivedCategory.singleFunctor (AdicSheaf l T) 0).obj (AdicSheaf.unit l T)
  let G := AdicSheaf.forget (l := l) Y ⋙ weilCoefficientsForgetAb l Y
  have hG : G.Faithful := inferInstance
  -- the underlying abelian sheaf of `Hⁱ(Rg_* ℚ̄_ℓ)`
  obtain ⟨i', rfl⟩ : ∃ i' : ℕ, (i' : ℤ) = i := ⟨i.toNat, by lia⟩
  let e : G.obj ((DerivedCategory.homologyFunctor _ i').obj ((g)_*ᵃ[l].rightDerivedFunctor.obj K)) ≅
      ((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerived i').obj
        ((sheafCompose (Scheme.ProEt.topology T) (forget₂ (WeilCoefficients.{u} l)
          AddCommGrpCat.{u + 1})).obj (adicConstantSheaf l T)) :=
    (weilCoefficientsForgetAb l Y).mapIso
        (((AdicSheaf.forget Y).mapDerivedCategoryHomologyFunctorIso i').app _) ≪≫
      ((weilCoefficientsForgetAb l Y).mapDerivedCategoryHomologyFunctorIso i').app _ ≪≫
      (DerivedCategory.homologyFunctor _ i').mapIso
        ((rightDerivedAdicLowerStarCompForgetAbIso g).app K) ≪≫
      (DerivedCategory.homologyFunctor _ i').mapIso
        (((ProEtale.lowerStar AddCommGrpCat.{u + 1} g).rightDerivedFunctor).mapIso
          ((weilCoefficientsForgetAb l T).mapDerivedCategory.mapIso
            (((AdicSheaf.forget T).mapDerivedCategorySingleFunctor 0).app _) ≪≫
          ((weilCoefficientsForgetAb l T).mapDerivedCategorySingleFunctor 0).app _)) ≪≫
      (ProEtale.lowerStar AddCommGrpCat.{u + 1} g).homologyRightDerivedFunctorObjSingleFunctorIso
        _ i'
  have hz := (isZero_rightDerived_lowerStar_adicConstantSheaf g aT aY hg d hd l i'
    (by lia)).of_iso e
  exact (IsZero.iff_id_eq_zero _).2 (G.map_injective (by
    rw [G.map_id, G.map_zero]
    exact hz.eq_of_src _ _))

/-- **The derived pushforward of the constant `ℓ`-adic sheaf is bounded**, in degrees
`[0, 2d + 1]`: the boundedness half of the finiteness theorem for the constant sheaf. -/
theorem bounded_rightDerivedFunctor_adicLowerStar_unit :
    DerivedCategory.TStructure.t.bounded ((g)_*ᵃ[l].rightDerivedFunctor.obj
      ((DerivedCategory.singleFunctor _ 0).obj (AdicSheaf.unit l T))) :=
  ⟨⟨0, (g)_*ᵃ[l].isGE_rightDerivedFunctor_obj_singleFunctor _⟩,
    ⟨_, isLE_rightDerivedFunctor_adicLowerStar_unit g aT aY hg d hd l⟩⟩

end Vanishing

end AlgebraicGeometry.ProEtale
