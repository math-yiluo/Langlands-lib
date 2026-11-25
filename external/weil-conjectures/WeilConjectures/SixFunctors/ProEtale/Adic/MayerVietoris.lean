/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.ProEtale.Adic.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative

/-!
# Restriction to an open cover of `ℓ`-adic sheaves

The restrictions of sheaves of `ℚ̄_ℓ,X`-modules on `X_proét` along the members of a pro-étale
covering family, for instance an open cover, are jointly conservative
(`AlgebraicGeometry.ProEtale.isIso_of_isIso_adicUpperStar`), and so are the induced functors on
the derived categories
(`AlgebraicGeometry.ProEtale.isIso_of_isIso_mapDerivedCategory_adicUpperStar`). For an open cover
`X = U ∪ V`, a K-injective complex vanishing on `U` is the pushforward of its restriction to `V`
(`AlgebraicGeometry.ProEtale.isIso_Q_map_unit_of_isZero`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] {X : Scheme.{u}}

/-- **Restrictions along a pro-étale cover are jointly conservative** on `ℓ`-adic sheaves. -/
lemma isIso_of_isIso_adicUpperStar {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, WeaklyEtale (g i)] (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {M N : AdicSheaf l X} (φ : M ⟶ N) (h : ∀ i, IsIso ((g i)^*ᵃ[l].map φ)) : IsIso φ := by
  have : IsIso φ.hom := by
    refine ProEtale.isIso_of_isIso_localizationRestriction _ φ.hom g hg fun i ↦ ?_
    have h1 : IsIso ((g i)^*[WeilCoefficients.{u} l].map φ.hom) :=
      inferInstanceAs (IsIso ((Mod.forget _).map ((g i)^*ᵃ[l].map φ)))
    exact (NatIso.isIso_map_iff (ProEtale.upperStarIsoLocalizationRestriction
      (WeilCoefficients.{u} l) (g i) inferInstance) φ.hom).1 h1
  have : IsIso ((Mod.forget (adicConstantSheaf l X)).map φ) := this
  exact isIso_of_reflects_iso φ (Mod.forget _)

/-- **Restrictions along a pro-étale cover are jointly conservative** on the derived
categories of `ℓ`-adic sheaves: a morphism is invertible on cohomology sheaves as soon as
its restrictions are. -/
lemma isIso_of_isIso_mapDerivedCategory_adicUpperStar {ι : Type*} {W : ι → Scheme.{u}}
    (g : ∀ i, W i ⟶ X) [∀ i, WeaklyEtale (g i)]
    (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {K L : DerivedCategory (AdicSheaf l X)} (ψ : K ⟶ L)
    (h : ∀ i, IsIso ((g i)^*ᵃ[l].mapDerivedCategory.map ψ)) : IsIso ψ := by
  rw [DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_adicUpperStar l g hg _ fun i ↦ ?_
  exact (NatIso.isIso_map_iff ((g i)^*ᵃ[l].mapDerivedCategoryHomologyFunctorIso n) ψ).2
    (inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((g i)^*ᵃ[l].mapDerivedCategory.map ψ))))

/-- The restriction to an open subscheme `j : Z ⟶ X` of the unit `I ⟶ j_* j^* I` is a
quasi-isomorphism, by a triangle identity, the counit of `j^* ⊣ j_*` being invertible. -/
lemma isIso_mapDerivedCategory_Q_map_unit {Z : Scheme.{u}} (j : Z ⟶ X) [IsOpenImmersion j]
    (I : CochainComplex (AdicSheaf l X) ℤ) :
    IsIso ((j)^*ᵃ[l].mapDerivedCategory.map (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (adicUpperStarLowerStarAdjunction l j).unit (ComplexShape.up ℤ)).app I))) := by
  refine (NatIso.isIso_map_iff ((j)^*ᵃ[l].mapDerivedCategoryFactors) _).2 ?_
  have : IsIso (((j)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (adicUpperStarLowerStarAdjunction l j).unit
        (ComplexShape.up ℤ)).app I)) := by
    have (n : ℤ) : IsIso ((((j)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (adicUpperStarLowerStarAdjunction l j).unit
          (ComplexShape.up ℤ)).app I)).f n) := by
      change IsIso ((j)^*ᵃ[l].map ((adicUpperStarLowerStarAdjunction l j).unit.app (I.X n)))
      have h := (adicUpperStarLowerStarAdjunction l j).left_triangle_components (I.X n)
      have : IsIso ((j)^*ᵃ[l].map ((adicUpperStarLowerStarAdjunction l j).unit.app
          (I.X n)) ≫ (adicUpperStarLowerStarAdjunction l j).counit.app
            ((j)^*ᵃ[l].obj (I.X n))) := by
        rw [h]
        exact IsIso.id _
      exact IsIso.of_isIso_comp_right _
        ((adicUpperStarLowerStarAdjunction l j).counit.app ((j)^*ᵃ[l].obj (I.X n)))
    exact HomologicalComplex.Hom.isIso_of_components _
  exact Functor.map_isIso DerivedCategory.Q
    (((j)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).map
      ((NatTrans.mapHomologicalComplex (adicUpperStarLowerStarAdjunction l j).unit
        (ComplexShape.up ℤ)).app I))

section MayerVietoris

variable {U V : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X) [IsOpenImmersion jU] [IsOpenImmersion jV]

/-- The two members of an open cover, as a family indexed by `Bool`. -/
abbrev pairCover : ∀ b : Bool, cond b U V ⟶ X
  | true => jU
  | false => jV

instance (b : Bool) : IsOpenImmersion (pairCover jU jV b) := by
  cases b <;> assumption

lemma pairCover_mem_proetalePrecoverage
    (hcov : ∀ x, x ∈ Set.range jU.base ∨ x ∈ Set.range jV.base) :
    Presieve.ofArrows _ (pairCover jU jV) ∈ Scheme.proetalePrecoverage X :=
  Scheme.zariskiPrecoverage_le_proetalePrecoverage _
    ((Scheme.ofArrows_mem_precoverage_iff _).mpr
      ⟨fun x ↦ (hcov x).elim (fun h ↦ ⟨true, h⟩) (fun h ↦ ⟨false, h⟩),
        fun b ↦ inferInstanceAs (IsOpenImmersion (pairCover jU jV b))⟩)

/-- **Objects supported on the complement of an open subscheme.** Let `X = U ∪ V` be an open
cover and `I` a K-injective complex of `ℓ`-adic sheaves on `X` whose restriction to `U`
vanishes in the derived category. Then the unit `I ⟶ j_{V*} j_V^* I` is a quasi-isomorphism:
it is one on `V` by the triangle identities, and on `U` both sides vanish, the restriction to
`U` of `j_{V*} j_V^* I` being computed on `U ∩ V` by open base change. -/
lemma isIso_Q_map_unit_of_isZero (hcov : ∀ x, x ∈ Set.range jU.base ∨ x ∈ Set.range jV.base)
    (I : CochainComplex (AdicSheaf l X) ℤ) [I.IsKInjective]
    (hI : IsZero ((jU)^*ᵃ[l].mapDerivedCategory.obj (DerivedCategory.Q.obj I))) :
    IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
      (adicUpperStarLowerStarAdjunction l jV).unit (ComplexShape.up ℤ)).app I)) := by
  refine isIso_of_isIso_mapDerivedCategory_adicUpperStar l (pairCover jU jV)
    (pairCover_mem_proetalePrecoverage jU jV hcov) _ ?_
  rintro (_ | _)
  · exact isIso_mapDerivedCategory_Q_map_unit l jV I
  · -- on `U`: both sides vanish
    have hsq : IsPullback (pullback.fst jU jV) (pullback.snd jU jV) jU jV :=
      IsPullback.of_hasPullback jU jV
    let J := ((jV)^*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj I
    have hJ : IsZero ((pullback.snd jU jV)^*ᵃ[l].mapDerivedCategory.obj
        (DerivedCategory.Q.obj J)) := by
      refine (((pullback.fst jU jV)^*ᵃ[l].mapDerivedCategory.map_isZero hI)).of_iso ?_
      exact (pullback.snd jU jV)^*ᵃ[l].mapDerivedCategory.mapIso
          (((jV)^*ᵃ[l].mapDerivedCategoryFactors).app I).symm ≪≫
        ((jV)^*ᵃ[l].mapDerivedCategoryCompIso (pullback.snd jU jV)^*ᵃ[l]).app _ ≪≫
        (Functor.mapDerivedCategoryNatIso
          (adicUpperStarCompIso l pullback.condition.symm)).app _ ≪≫
        (((jU)^*ᵃ[l].mapDerivedCategoryCompIso (pullback.fst jU jV)^*ᵃ[l]).app _).symm
    have h₂ : IsZero ((jU)^*ᵃ[l].mapDerivedCategory.obj (DerivedCategory.Q.obj
        (((jV)_*ᵃ[l].mapHomologicalComplex (ComplexShape.up ℤ)).obj J))) := by
      refine (((pullback.fst jU jV)_*ᵃ[l].rightDerivedFunctor.map_isZero hJ)).of_iso ?_
      exact (jU)^*ᵃ[l].mapDerivedCategory.mapIso
          ((jV)_*ᵃ[l].rightDerivedFunctorObjQIso J).symm ≪≫
        (adicDerivedBaseChangeIso l hsq).app _
    exact hI.isIso h₂ _

open ZeroObject in
/-- **Restrictions along a pro-étale cover detect zero objects.** -/
lemma isZero_of_isZero_adicUpperStar {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ X)
    [∀ i, WeaklyEtale (g i)] (hg : Presieve.ofArrows W g ∈ Scheme.proetalePrecoverage X)
    {M : AdicSheaf l X} (h : ∀ i, IsZero ((g i)^*ᵃ[l].obj M)) : IsZero M := by
  have : IsIso (0 : M ⟶ 0) := isIso_of_isIso_adicUpperStar l g hg _ fun i ↦
    (h i).isIso ((g i)^*ᵃ[l].map_isZero (isZero_zero _)) _
  exact (isZero_zero _).of_iso (asIso (0 : M ⟶ 0))

end MayerVietoris

end AlgebraicGeometry.ProEtale
