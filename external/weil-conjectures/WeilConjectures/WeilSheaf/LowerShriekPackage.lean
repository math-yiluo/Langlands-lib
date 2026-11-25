/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
public import WeilConjectures.WeilSheaf.LowerStarId

/-!
# The compact support package for Weil complexes

Forms of clauses 3 and 4 of the coefficient and functor package (blueprint
`prop-functor-package`) and of the projection formula (blueprint `sec-Weil-complexes`) for the
direct image with compact support `Rf_!` of Weil complexes
(`AlgebraicGeometry.WeilComplex.derivedLowerShriek`), in the shape used by the Fourier
transform computations of `chap-The-Deligne-Laumon-theorem-for-curves`. They are derived from the
statements of those nodes in `WeilConjectures.WeilSheaf.LowerShriekFunctoriality` and
`WeilConjectures.WeilSheaf.FourierInversion.OtherSections`.

## Main statements

- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriekCompIso`: `R(f ≫ g)_! ≅ Rg_! Rf_!`.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriekIdIso`: `R(𝟙)_! K ≅ K`.
- `AlgebraicGeometry.WeilComplex.nonempty_derivedLowerShriekIsoDerivedLowerStar`: `Rf_! ≅ Rf_*`
  for proper `f`.
- `AlgebraicGeometry.WeilComplex.exists_distTriang_derivedLowerShriek_openClosed_comp`: the
  triangle `R(fj)_! j^*K ⟶ Rf_! K ⟶ R(fi)_! i^*K ⟶`.
- `AlgebraicGeometry.WeilComplex.nonempty_upperStarDerivedLowerShriekIso_of_isPullback`: compact
  support base change.
- `AlgebraicGeometry.WeilComplex.nonempty_tensorLisseDerivedLowerShriekIso`: the projection
  formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace AlgebraicGeometry

namespace WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Composition of direct images with compact support**: for morphisms `f : X ⟶ Y` and
`g : Y ⟶ W` of `k₀`-schemes with composite `h = f ≫ g`, `Rh_! ≅ Rg_! ∘ Rf_!` on Weil complexes.
(blueprint: `prop-functor-package`, clause 3) -/
theorem nonempty_derivedLowerShriekCompIso {X Y W : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [W.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (g : Y ⟶ W) [g.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated g]
    [LocallyOfFiniteType g] [QuasiCompact g] (h : X ⟶ W) [h.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h] (hfg : f ≫ g = h)
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (W ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (W ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (W ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (derivedLowerShriek k₀ l h ≅
      derivedLowerShriek k₀ l f ⋙ derivedLowerShriek k₀ l g) := by
  subst hfg
  exact nonempty_derivedLowerShriek_comp_iso f g

/-- **The identity equation of the composition law**: the direct image with compact support along
the identity is the identity, `R(𝟙)_! K ≅ K`: the identity is proper, so `R(𝟙)_! K ≅ R(𝟙)_* K`,
and the pushforward along the identity is the identity. (blueprint: `prop-functor-package`,
clause 3) -/
theorem nonempty_derivedLowerShriekIdIso (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    (K : WeilComplex k₀ l X) : Nonempty ((derivedLowerShriek k₀ l (𝟙 X)).obj K ≅ K) :=
  ⟨derivedLowerShriekObjIsoDerivedLowerStar (𝟙 X) K ≪≫ ObjectProperty.isoMk _
    ((Functor.rightDerivedFunctorNatIso (ProEtaleWeilSheaf.lowerStarIdIso k₀ l X)).app K.obj ≪≫
      (Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _)).app K.obj ≪≫
      (Functor.mapDerivedCategoryIdIso _).app K.obj)⟩

/-- **Compact support and ordinary direct image agree for proper morphisms**: `Rf_! ≅ Rf_*` for a
proper morphism `f` of `k₀`-schemes. (blueprint: `prop-functor-package`, clause 3) -/
theorem nonempty_derivedLowerShriekIsoDerivedLowerStar {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsProper f]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    Nonempty ((derivedLowerShriek k₀ l f).obj K ≅ (derivedLowerStar f).obj K) :=
  ⟨derivedLowerShriekObjIsoDerivedLowerStar f K⟩

/-- **The open–closed triangle under `Rf_!`**: for a closed immersion `i : Z ↪ X` with open
complement `j : U ↪ X`, a morphism `f : X ⟶ Y` of `k₀`-schemes and a Weil complex `K` on `X`,
applying `Rf_!` to the localization triangle `j_!j^*K ⟶ K ⟶ i_*i^*K ⟶` gives a distinguished
triangle

`R(fj)_! j^*K ⟶ Rf_! K ⟶ R(fi)_! i^*K ⟶ R(fj)_! j^*K[1]`.

The composites `fj = j ≫ f` and `fi = i ≫ f` are given as separate morphisms.
(blueprint: `prop-functor-package`, clause 3) -/
theorem exists_distTriang_derivedLowerShriek_openClosed_comp {U X Z Y : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [X.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (j : U ⟶ X) [IsOpenImmersion j] [j.IsOver (Spec (CommRingCat.of k₀))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of k₀))]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (fj : U ⟶ Y) [fj.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated fj]
    [LocallyOfFiniteType fj] [QuasiCompact fj] (fi : Z ⟶ Y) [fi.IsOver (Spec (CommRingCat.of k₀))]
    [IsSeparated fi] [LocallyOfFiniteType fi] [QuasiCompact fi] (hfj : j ≫ f = fj)
    (hfi : i ≫ f = fi) [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (K : WeilComplex k₀ l X) :
    ∃ (α : (derivedLowerShriek k₀ l fj).obj ((upperStar j).obj K) ⟶
        (derivedLowerShriek k₀ l f).obj K)
      (β : (derivedLowerShriek k₀ l f).obj K ⟶
        (derivedLowerShriek k₀ l fi).obj ((upperStar i).obj K))
      (γ : (derivedLowerShriek k₀ l fi).obj ((upperStar i).obj K) ⟶
        ((derivedLowerShriek k₀ l fj).obj ((upperStar j).obj K))⟦(1 : ℤ)⟧),
      Triangle.mk α β γ ∈ distTriang (WeilComplex k₀ l Y) := by
  have : QuasiCompact j := by
    have : QuasiCompact (j ≫ f) := hfj ▸ inferInstance
    exact QuasiCompact.of_comp j f
  subst hfj hfi
  obtain ⟨T, hT, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := exists_distTriang_derivedLowerShriek_openClosed (k₀ := k₀)
    (l := l) j i (by rw [hij]; exact isCompl_compl) f K
  refine ⟨e₁.inv ≫ T.mor₁ ≫ e₂.hom, e₂.inv ≫ T.mor₂ ≫ e₃.hom,
    e₃.inv ≫ T.mor₃ ≫ (shiftFunctor _ (1 : ℤ)).map e₁.hom, ?_⟩
  refine isomorphic_distinguished T hT _ (Triangle.isoMk _ _ e₁.symm e₂.symm e₃.symm ?_ ?_ ?_)
  · simp
  · simp
  · simp [← Functor.map_comp]

/-- **Compact support base change**: for a cartesian square
```
X' --- g ---> X
|             |
f'            f
v             v
Y' --- h ---> Y
```
of `k₀`-schemes, `h^* Rf_! K ≅ Rf'_! g^* K` for Weil complexes `K` on `X`.
(blueprint: `prop-functor-package`, clause 4) -/
theorem nonempty_upperStarDerivedLowerShriekIso_of_isPullback {X Y X' Y' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [X'.Over (Spec (CommRingCat.of k₀))] [Y'.Over (Spec (CommRingCat.of k₀))]
    {f : X ⟶ Y} [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))]
    {f' : X' ⟶ Y'} [f'.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f']
    [LocallyOfFiniteType f'] [QuasiCompact f']
    [LocallyOfFiniteType (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y' ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y' ↘ Spec (CommRingCat.of k₀))]
    {g : X' ⟶ X} [g.IsOver (Spec (CommRingCat.of k₀))] {h : Y' ⟶ Y}
    [h.IsOver (Spec (CommRingCat.of k₀))] (hH : IsPullback g f' f h) (K : WeilComplex k₀ l X) :
    Nonempty ((upperStar h).obj ((derivedLowerShriek k₀ l f).obj K) ≅
      (derivedLowerShriek k₀ l f').obj ((upperStar g).obj K)) :=
  ⟨(nonempty_upperStar_derivedLowerShriek_iso hH).some.app K⟩

/-- **The projection formula** for the tensor product with a lisse Weil sheaf: for a morphism
`f : X ⟶ Y` of `k₀`-schemes, a lisse Weil sheaf `L` on `Y` and a Weil complex `K` on `X`,
`L ⊗ Rf_! K ≅ Rf_!(f^*L ⊗ K)`. (blueprint: `sec-Weil-complexes`) -/
theorem nonempty_tensorLisseDerivedLowerShriekIso {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (Y ↘ Spec (CommRingCat.of k₀))] (L : WeilSheaf k₀ l Y) (hL : L.IsLisse)
    (K : WeilComplex k₀ l X) :
    Nonempty ((tensorLisse L hL).obj ((derivedLowerShriek k₀ l f).obj K) ≅
      (derivedLowerShriek k₀ l f).obj
        ((tensorLisse ((WeilSheaf.upperStar f).obj L)
          (ProEtale.IsAdicLisseSheaf.upperStar _ hL)).obj K)) :=
  ⟨(nonempty_iso_derivedLowerShriek_tensorLisse f L hL).some.app K⟩

end WeilComplex

end AlgebraicGeometry
