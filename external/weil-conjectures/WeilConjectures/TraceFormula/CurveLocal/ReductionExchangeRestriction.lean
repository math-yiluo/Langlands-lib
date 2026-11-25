/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Localization
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReductionLowerShriekIso
public import WeilConjectures.TraceFormula.CurveLocal.ExchangeRestriction
public import WeilConjectures.TraceFormula.CurveLocal.SwapProduct

/-!

# The integral exchange restriction modulo `ℓⁿ`

For a cartesian square `ι ≫ c = d ≫ Δ` of separated `k`-schemes of finite type with `c` and `d`
proper, the reduction modulo `ℓⁿ`, read on the small étale site
(`ProEtale.CondensedRing.etaleReduction`), carries the exchange restriction
`ρ_P : Lι^* Rc^! P ⟶ Rd^! LΔ^* P` with `𝒪_E`-coefficients to the étale exchange restriction of
the reduction, up to an isomorphism on the target and a map on the source
(`ProEtale.CondensedRing.exists_etaleReduction_map_exchangeRestriction_comp_eq`). The étale
square may moreover be transported along an isomorphism `φ : W ≅ X × X` of the ambient scheme.
This uses the coefficient comparisons of blueprint `proposition-six-operations-change-coefficients`
for `𝒪_E ⟶ 𝒪_E ⧸ ℓⁿ` (`ProEtale.CondensedRing.exists_etaleReductionLowerShriekIso`,
`ProEtale.CondensedRing.etaleReductionUpperStarIso`) and
`CategoryTheory.Adjunction.exists_map_mateEquiv_app_comp_eq`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry

namespace Etale

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- The derived lower shriek `Ri_!` along a closed immersion `i` is full: the unit of
`Ri_! ⊣ Ri^!` is an isomorphism. -/
theorem full_rightDerivedLowerShriek_of_isClosedImmersion {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] [HasCompactification i] : (R(i)_![ModuleCat.{u + 1} Λ]).Full :=
  have (Q : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
      IsIso ((rightDerivedUpperShriekAdjunction Λ i).unit.app Q) :=
    isIso_rightDerivedUpperShriekAdjunction_unit_app Λ i Q
  have : IsIso (rightDerivedUpperShriekAdjunction Λ i).unit :=
    NatIso.isIso_of_isIso_app _
  ((rightDerivedUpperShriekAdjunction Λ i).fullyFaithfulLOfIsIsoUnit).full

/-- For `g ≫ φ = c` with `φ` an isomorphism, `Rc_! ⋙ Lφ^* ≅ Rg_!`: compact-support base change
along the cartesian square `𝟙 ≫ c = g ≫ φ`, followed by `L(𝟙)^* ≅ 𝟭`. -/
noncomputable def lowerShriekUpperStarIsoOfIsIso {C W S : Scheme.{u}} (g : C ⟶ W) (φ : W ⟶ S)
    [IsIso φ] (c : C ⟶ S) (h : g ≫ φ = c) [HasCompactification c] [HasCompactification g]
    [QuasiCompact g] :
    R(c)_![ModuleCat.{u + 1} Λ] ⋙ L((φ)^*[ModuleCat.{u + 1} Λ]) ≅ R(g)_![ModuleCat.{u + 1} Λ] :=
  lowerShriekBaseChangeIso Λ (IsPullback.of_horiz_isIso ⟨by rw [Category.id_comp, h]⟩) ≪≫
    Functor.isoWhiskerRight (leftDerivedUpperStarId _ C) _ ≪≫ Functor.leftUnitor _

end Etale

namespace ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] (E : Type) [Field E] [Algebra E (PadicAlgCl ℓ)] [Algebra ℚ_[ℓ] E]
  [IsScalarTower ℚ_[ℓ] E (PadicAlgCl ℓ)] [FiniteDimensional ℚ_[ℓ] E] (n : ℕ)
  {Y C F Z : Over (Spec (.of k))}
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
  [LocallyOfFiniteType F.hom] [QuasiCompact F.hom] [IsSeparated F.hom]
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]

/-- The reduction modulo `ℓⁿ` commutes with `Rc_!` followed by the pullback `Lφ^*` along an
isomorphism `φ` with `g ≫ φ = c.left`: `Rc_! ⋙ R_n ⋙ Lφ^* ≅ R_n ⋙ Rg_!`. -/
noncomputable def etaleReductionLowerShriekUpperStarIso (c : C ⟶ Y) [IsProper c.left]
    {W : Scheme.{u}} (g : C.left ⟶ W) (φ : W ⟶ Y.left) [IsIso φ] (hg : g ≫ φ = c.left)
    [HasCompactification g] [QuasiCompact g]
    (γ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E c ⋙
        etaleReduction ℓ E n Y ≅
      etaleReduction ℓ E n C ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) c.left) :
    PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E c ⋙
        (etaleReduction ℓ E n Y ⋙
          L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ)) ≅
      etaleReduction ℓ E n C ⋙
        Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) g :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight γ _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Etale.lowerShriekUpperStarIsoOfIsIso _ g φ c.left hg)

/-- The reduction modulo `ℓⁿ` commutes with the pullback `LΔ^*`, read through an isomorphism `φ`
with `Δ' ≫ φ = Δ.left`: `LΔ^* ⋙ R_n ≅ R_n ⋙ Lφ^* ⋙ LΔ'^*`. -/
noncomputable def etaleReductionUpperStarIsoOfComp (Δ : Z ⟶ Y) {W : Scheme.{u}}
    (Δ' : Z.left ⟶ W) (φ : W ⟶ Y.left) (hΔ : Δ' ≫ φ = Δ.left) :
    boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ Δ ⋙
        etaleReduction ℓ E n Z ≅
      (etaleReduction ℓ E n Y ⋙
          L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ)) ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Δ') :=
  etaleReductionUpperStarIso ℓ E n Δ ≪≫
    Functor.isoWhiskerLeft _
      (Etale.leftDerivedUpperStarComp _ Δ' φ Δ.left hΔ.symm) ≪≫ (Functor.associator _ _ _).symm

/-- **The integral exchange restriction modulo `ℓⁿ`**: for a cartesian square `ι ≫ c = d ≫ Δ`
with `c`, `d` proper and `d` a closed immersion, and a cartesian square `ι ≫ g = d ≫ Δ'` of
schemes identified with the underlying square through an isomorphism `φ` (`g ≫ φ = c`,
`Δ' ≫ φ = Δ`), the reduction modulo `ℓⁿ` of the exchange restriction `ρ_P`, followed by an
isomorphism, factors through the étale exchange restriction of `ι ≫ g = d ≫ Δ'` at
`Lφ^* (P_{𝒪_E ⧸ ℓⁿ})`. -/
theorem exists_etaleReduction_map_exchangeRestriction_comp_eq {c : C ⟶ Y} {ι : F ⟶ C}
    {d : F ⟶ Z} {Δ : Z ⟶ Y} [IsProper c.left] [IsProper d.left] [IsClosedImmersion d.left]
    (σ : PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E c ⋙
        boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ Δ ≅
      boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ ι ⋙
        PadicIntegersRingObj.boundedConstructibleLowerShriek ℓ E d)
    {W : Scheme.{u}} (g : C.left ⟶ W) (Δ' : Z.left ⟶ W) (φ : W ⟶ Y.left) [IsIso φ]
    (hg : g ≫ φ = c.left) (hΔ : Δ' ≫ φ = Δ.left) [HasCompactification g] [QuasiCompact g]
    (hsq : IsPullback ι.left d.left g Δ') (P : Dᵇc(Y.left)⟦Profinite.padicIntegersRingObj ℓ E⟧) :
    ∃ (s : (etaleReduction ℓ E n F).obj
          ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ ι).obj
            ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E c).obj P)) ⟶
        (L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) ι.left)).obj
          ((Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n) g).obj
            ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ)).obj
              ((etaleReduction ℓ E n Y).obj P))))
      (β : (etaleReduction ℓ E n F).obj
          ((PadicIntegersRingObj.boundedConstructibleUpperShriek ℓ E d).obj
            ((boundedConstructibleUpperStar (Profinite.padicIntegersRingObj ℓ E) ℓ Δ).obj P)) ⟶
        (Etale.rightDerivedUpperShriek (integersModPowCoeff.{u} ℓ E n)
            d.left).obj
          ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) Δ')).obj
            ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ)).obj
              ((etaleReduction ℓ E n Y).obj P)))),
      IsIso β ∧
      (etaleReduction ℓ E n F).map
          ((mateEquiv (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E c)
            (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d)
            (TwoSquare.mk _ _ _ _ σ.inv)).app P) ≫ β =
        s ≫ Etale.exchangeRestriction (integersModPowCoeff.{u} ℓ E n) hsq
          ((L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ)).obj
            ((etaleReduction ℓ E n Y).obj P)) := by
  have hc := exists_etaleReductionLowerShriekIso ℓ E n c
  have hd := exists_etaleReductionLowerShriekIso ℓ E n d
  have := Etale.full_rightDerivedLowerShriek_of_isClosedImmersion
    (integersModPowCoeff.{u} ℓ E n) d.left
  have := hd.choose_spec
  have h := Adjunction.exists_map_mateEquiv_app_comp_eq
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E c)
    (PadicIntegersRingObj.boundedConstructibleUpperShriekAdjunction ℓ E d) _ _ σ
    (Etale.rightDerivedUpperShriekAdjunction _ g)
    (Etale.rightDerivedUpperShriekAdjunction _ d.left) _ _
    (Etale.lowerShriekBaseChangeIso _ hsq)
    (etaleReduction ℓ E n Y ⋙
      L(Etale.upperStar (ModuleCat.{u + 1} (integersModPowCoeff.{u} ℓ E n)) φ))
    (etaleReduction ℓ E n C) (etaleReduction ℓ E n F) (etaleReduction ℓ E n Z)
    (etaleReductionLowerShriekUpperStarIso ℓ E n c g φ hg hc.choose) hd.choose
    (etaleReductionUpperStarIsoOfComp ℓ E n Δ Δ' φ hΔ) P
  exact ⟨h.choose, _, inferInstance, h.choose_spec⟩

end ProEtale.CondensedRing

end AlgebraicGeometry
