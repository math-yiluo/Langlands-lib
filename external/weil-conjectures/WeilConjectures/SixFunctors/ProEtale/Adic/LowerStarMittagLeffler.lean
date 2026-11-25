/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Abelian.ImageSubobjectMittagLeffler
public import WeilConjectures.ConstructibleSheaf.MittagLeffler
public import WeilConjectures.ConstructibleSheaf.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStarHomology
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.SmoothProperLocallyConstant
public import WeilConjectures.SixFunctors.ProEtale.Comparison.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.Adic.LowerStarMilnorSequence

/-!
# Higher direct images of `ℓ`-adic towers along smooth proper morphisms are Mittag-Leffler

Let `k` be a field, `Y` of finite type over `k`, `f : X ⟶ Y` smooth and proper, and let `(Gₙ)ₙ` be
a tower of étale sheaves of `Λ`-modules on `X` (e.g. `Λ = ℤ`), each `Gₙ` being the restriction of
scalars of a finite locally constant sheaf `Fₙ` of `Λ ⧸ Iₙ`-modules, with `Λ ⧸ Iₙ` finite and
killed by an integer invertible in `k` (e.g. an `ℓ`-adic tower of `ℤ/ℓⁿ`-sheaves, `ℓ ≠ char k`).
Then for every `i` the tower `(Rⁱf_* ν^* Gₙ)ₙ` of sheaves on `Y_proét` is Mittag-Leffler
(`AlgebraicGeometry.ProEtale.mittagLeffler_homology_rightDerivedLowerStar_of_smooth_of_isProper`).
This is the hypothesis of
`AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_mittagLeffler`, which then
gives `Rʲf_* (lim ν^* Gₙ) ≅ lim Rʲf_* ν^* Gₙ` (the `R¹lim` term of the Milnor sequence vanishes)
for towers with epimorphic transitions
(`AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper`).

The proof: `Rⁱf_* ν^* Gₙ ≅ ν^* Rⁱf_* Gₙ`
(`AlgebraicGeometry.ProEtale.homologyRightDerivedLowerStarSingleComparisonUpperStarIso`), and
`Rⁱf_* Gₙ ≅ res Rⁱf_* Fₙ`
(`AlgebraicGeometry.Etale.homologyRightDerivedLowerStarRestrictScalarsIso`) is finite locally
constant with finite stalks by the smooth proper base change theorem
(`Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper`). As
`ν^*` is fully faithful, the tower is `ν^*` of a tower of finite locally constant étale sheaves
with finite stalks, which is Mittag-Leffler on the noetherian scheme `Y`
(`AlgebraicGeometry.Etale.mittagLeffler_imageSubobject_of_isFiniteLocallyConstantSheaf`), and
`ν^*` is exact
(`AlgebraicGeometry.ProEtale.mittagLeffler_imageSubobject_of_iso_comparisonUpperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The stalks of the restriction of scalars to `Λ` of a finite sheaf of modules over a finite
quotient `Λ ⧸ J` are finite: they are finitely generated modules over the finite ring `Λ ⧸ J`. -/
lemma Scheme.finite_sheafFiber_restrictScalars_of_isFiniteSheaf (J : Ideal Λ) [Finite (Λ ⧸ J)]
    {X : Scheme.{u}} (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ J)))
    [IsFiniteSheaf (FA := fun M N : ModuleCat.{u + 1} (Λ ⧸ J) ↦ M →ₗ[Λ ⧸ J] N)
      (CA := fun M : ModuleCat.{u + 1} (Λ ⧸ J) ↦ M) G]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    Finite ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ) |>.obj
      ((Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk J)).obj G)) := by
  have := (ModuleCat.isFinitelyGenerated_iff _).1
    (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := fun M N : ModuleCat.{u + 1} (Λ ⧸ J) ↦
      M →ₗ[Λ ⧸ J] N) (CA := fun M : ModuleCat.{u + 1} (Λ ⧸ J) ↦ M) (F := G) Ω s)
  have : Finite ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} (Λ ⧸ J)) |>.obj G) :=
    Module.finite_of_finite (Λ ⧸ J)
  have : Finite ((ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J)).obj
      ((pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} (Λ ⧸ J)) |>.obj G)) := this
  exact @Finite.of_equiv _ _ this ((((pointSmallEtale s).sheafFiberCompIso
    (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk J))).app G).toLinearEquiv.toEquiv.symm)

namespace ProEtale

/-- **Towers of pro-étale sheaves coming from finite locally constant étale sheaves are
Mittag-Leffler.** Let `Y` be a scheme with noetherian underlying space and `T` a tower of sheaves
of `Λ`-modules on `Y_proét` with `Tₙ ≅ ν^* Eₙ` for finite locally constant étale sheaves `Eₙ` with
finite stalks. Then for every `n` there is `N ≥ n` such that the image of `T_N ⟶ Tₙ` is contained
in the image of `T_k ⟶ Tₙ` for every `k ≥ n`. Indeed `ν^*` is fully faithful, so `T` is `ν^*` of
a tower of étale sheaves, which is Mittag-Leffler
(`AlgebraicGeometry.Etale.mittagLeffler_imageSubobject_of_isFiniteLocallyConstantSheaf`), and `ν^*`
is exact. -/
theorem mittagLeffler_imageSubobject_of_iso_comparisonUpperStar {Y : Scheme.{u}}
    [TopologicalSpace.NoetherianSpace Y]
    (T : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))
    (E : ℕ → Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [∀ n : ℕ, IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (E n)]
    (hfin : ∀ (n : ℕ) (y : Y), Finite ((pointSmallEtale (Y.algClosurePoint y)).sheafFiber
      (A := ModuleCat.{u + 1} Λ) |>.obj (E n)))
    (e : ∀ n : ℕ, (ν^*(Y)[ModuleCat.{u + 1} Λ]).obj (E n) ≅ T.obj (op n)) (n : ℕ) :
    ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject (T.map (homOfLE hN).op) ≤ imageSubobject (T.map (homOfLE hk).op) := by
  let hν := Functor.FullyFaithful.ofFullyFaithful (ν^*(Y)[ModuleCat.{u + 1} Λ])
  let E' := hν.liftDiagram T (fun m ↦ E m.unop) (fun m ↦ e m.unop)
  have (m : ℕ) : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (E'.obj (op m)) :=
    inferInstanceAs (IsFiniteLocallyConstantSheaf (E m))
  exact Abelian.mittagLeffler_imageSubobject_of_iso (hν.liftDiagramCompIso T _ _)
    (Abelian.mittagLeffler_imageSubobject_comp (ν^*(Y)[ModuleCat.{u + 1} Λ])
      (Etale.mittagLeffler_imageSubobject_of_isFiniteLocallyConstantSheaf E' hfin)) n

/-- **Higher direct images of an `ℓ`-adic tower along a smooth proper morphism are
Mittag-Leffler.** Let `K` be a field, `Y` of finite type over `K`, `f : X ⟶ Y` smooth and proper
and `G` a tower of étale sheaves of `Λ`-modules on `X` such that each `Gₙ` is the restriction of
scalars of a finite locally constant sheaf `Fₙ` of `Λ ⧸ Iₙ`-modules, where `Λ ⧸ Iₙ` is finite and
killed by an integer invertible in `K`. Then for every `i` the tower `(Rⁱf_* ν^* Gₙ)ₙ` of sheaves
on `Y_proét` satisfies the Mittag-Leffler condition: for every `n` there is `N ≥ n` such that the
image of `Rⁱf_* ν^* G_N ⟶ Rⁱf_* ν^* Gₙ` is contained in the image of `Rⁱf_* ν^* G_k ⟶ Rⁱf_* ν^* Gₙ`
for every `k ≥ n`. This is the hypothesis `hML` of
`AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_mittagLeffler` for the
tower of complexes `ν^* Gₙ[0]`. -/
theorem mittagLeffler_homology_rightDerivedLowerStar_of_smooth_of_isProper
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (I : ℕ → Ideal Λ)
    [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (i n : ℕ) :
    ∃ N : ℕ, ∃ hN : n ≤ N, ∀ (k : ℕ) (hk : n ≤ k),
      imageSubobject ((DerivedCategory.homologyFunctor _ i).map
        (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).map (DerivedCategory.Q.map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            ((ν^*(X)[ModuleCat.{u + 1} Λ]).map (G.map (homOfLE hN).op)))))) ≤
      imageSubobject ((DerivedCategory.homologyFunctor _ i).map
        (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).map (DerivedCategory.Q.map
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
            ((ν^*(X)[ModuleCat.{u + 1} Λ]).map (G.map (homOfLE hk).op)))))) := by
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace aY
  have : IsNoetherian Y := { __ := LocallyOfFiniteType.isLocallyNoetherian aY }
  let T : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ) :=
    ((((G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
      HomologicalComplex.single _ (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q) ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)) ⋙ DerivedCategory.homologyFunctor _ i
  -- the étale higher direct images `Rⁱf_* Gₙ`
  let E (m : ℕ) : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    (DerivedCategory.homologyFunctor _ i).obj (R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f).obj
      ((DerivedCategory.singleFunctor _ 0).obj (G.obj (op m))))
  -- `Rⁱf_* Gₙ ≅ res Rⁱf_* Fₙ`
  let eE (m : ℕ) : E m ≅ (Sheaf.restrictScalars Y.smallEtaleTopology (Ideal.Quotient.mk (I m))).obj
      ((DerivedCategory.homologyFunctor _ i).obj
        (R(Etale.lowerStar (ModuleCat.{u + 1} (Λ ⧸ I m)) f).obj
          ((DerivedCategory.singleFunctor _ 0).obj (F m)))) :=
    (DerivedCategory.homologyFunctor _ i).mapIso
      ((R(Etale.lowerStar (ModuleCat.{u + 1} Λ) f)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso (eG m))) ≪≫
      (Etale.homologyRightDerivedLowerStarRestrictScalarsIso (Ideal.Quotient.mk (I m)) f
        (F m) i).symm
  have hF (m : ℕ) :=
    Etale.isFiniteLocallyConstantSheaf_homology_rightDerivedLowerStar_of_smooth_of_isProper
      (Λ ⧸ I m) aY f (F m) i
  have (m : ℕ) : IsFiniteLocallyConstantSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (E m) :=
    have := hF m
    IsFiniteLocallyConstantSheaf.of_iso (eE m).symm
  refine mittagLeffler_imageSubobject_of_iso_comparisonUpperStar T E (fun m y ↦ ?_)
    (fun m ↦ (homologyRightDerivedLowerStarSingleComparisonUpperStarIso _ f (G.obj (op m))
      i).symm) n
  have := hF m
  have := finite_sheafFiber_restrictScalars_of_isFiniteSheaf (I m)
    ((DerivedCategory.homologyFunctor _ i).obj
      (R(Etale.lowerStar (ModuleCat.{u + 1} (Λ ⧸ I m)) f).obj
        ((DerivedCategory.singleFunctor _ 0).obj (F m)))) (Y.algClosurePoint y)
  exact Finite.of_equiv _
    ((pointSmallEtale (Y.algClosurePoint y)).sheafFiber.mapIso (eE m)).toLinearEquiv.toEquiv.symm

/-- **`Rʲf_*` commutes with the limit of an `ℓ`-adic tower along a smooth proper morphism.** In the
situation of
`AlgebraicGeometry.ProEtale.mittagLeffler_homology_rightDerivedLowerStar_of_smooth_of_isProper`,
if moreover the transition maps of `G` are epimorphisms, then for `i + 1 = j` the map
`Rʲf_* (lim ν^* Gₙ) ⟶ lim Rʲf_* ν^* Gₙ` induced by the projections is an isomorphism: the
Milnor sequence
(`AlgebraicGeometry.ProEtale.isIso_lift_homology_rightDerivedLowerStar_of_mittagLeffler`)
applies, the tower `(Rⁱf_* ν^* Gₙ)ₙ` being Mittag-Leffler. -/
theorem isIso_lift_homology_rightDerivedLowerStar_of_smooth_of_isProper
    {K : Type u} [Field K] {X Y : Scheme.{u}} (aY : Y ⟶ Spec (.of K)) [LocallyOfFiniteType aY]
    [QuasiCompact aY] (f : X ⟶ Y) [Smooth f] [IsProper f]
    (G : ℕᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (I : ℕ → Ideal Λ)
    [∀ n, Finite (Λ ⧸ I n)] [∀ n, HasInvertibleExponent (Λ ⧸ I n) (Spec (.of K))]
    (F : ∀ n, Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (Λ ⧸ I n)))
    [∀ n, IsFiniteLocallyConstantSheaf (F n)]
    (eG : ∀ n, G.obj (op n) ≅
      (Sheaf.restrictScalars X.smallEtaleTopology (Ideal.Quotient.mk (I n))).obj (F n))
    (hG : ∀ n : ℕ, Epi (G.map (homOfLE n.le_succ).op))
    {c : Cone (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ])} (hc : IsLimit c) (i : ℕ) (j : ℤ)
    (hij : (i : ℤ) + 1 = j)
    {d : Cone (((((G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙
      HomologicalComplex.single _ (ComplexShape.up ℤ) 0) ⋙ DerivedCategory.Q) ⋙
        R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f)) ⋙ DerivedCategory.homologyFunctor _ j)}
    (hd : IsLimit d) :
    IsIso (hd.lift ((DerivedCategory.homologyFunctor _ j).mapCone
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} Λ) f).mapCone (DerivedCategory.Q.mapCone
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapCone c))))) := by
  let S := HomologicalComplex.single (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (ComplexShape.up ℤ) 0
  have : (ν^*(X)[ModuleCat.{u + 1} Λ]).IsLeftAdjoint := (comparisonAdjunction _ X).isLeftAdjoint
  have (n : ℕ) : Epi ((G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]).map (homOfLE n.le_succ).op) :=
    have := hG n
    (ν^*(X)[ModuleCat.{u + 1} Λ]).map_epi (G.map (homOfLE n.le_succ).op)
  exact isIso_lift_homology_rightDerivedLowerStar_of_mittagLeffler f
    (T := (G ⋙ ν^*(X)[ModuleCat.{u + 1} Λ]) ⋙ S) (c := S.mapCone c)
    (fun n i ↦ epi_single_map_f _ 0 i) (isLimitOfPreserves S hc) i j hij
    (mittagLeffler_homology_rightDerivedLowerStar_of_smooth_of_isProper aY f G I F eG i) hd

end ProEtale

end AlgebraicGeometry
