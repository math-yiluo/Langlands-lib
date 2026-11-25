/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.CohomPresheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import WeilConjectures.CategoryTheory.Sites.CechInjectiveModule
public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions

/-!
# Free sheaves under extension by zero and pullback, and cohomology

For an étale `v : V ⟶ Y`, extension by zero sends the free sheaf `Λ[T]` on an étale
`V`-scheme `T` to the free sheaf on `T → V → Y`, and the derived adjunction `v_! ⊣ v^*`
identifies `Hom((v_! M)[0], N[0]⟦q⟧)` with `Hom(M[0], (v^* N)[0]⟦q⟧)`. Combined with
`h^* Λ[W] ≅ Λ[W ×_X Y]`, this computes `Hom((h^* Λ[W])[0], N[0]⟦q⟧)` as the étale cohomology
`Hᵠ(W ×_X Y, N|)` of the scheme `W ×_X Y`. The file also states that étale cohomology of a
quasi-compact quasi-separated scheme commutes with filtered colimits.

## Main definitions

- `AlgebraicGeometry.Etale.etaleLowerShriekFreeSheafIso`: `v_! Λ[T] ≅ Λ[T → V → Y]`.
- `AlgebraicGeometry.Etale.shiftedHomFunctor`: the functor `N ↦ Hom(A[0], N[0]⟦q⟧)`.
- `AlgebraicGeometry.Etale.etaleLowerShriekShiftedHomIso`: the derived adjunction `v_! ⊣ v^*`
  on shifted maps out of a sheaf in degree `0`.
- `AlgebraicGeometry.Etale.shiftedHomFunctorUpperStarFreeSheafIso`:
  `Hom((h^* Λ[W])[0], N[0]⟦q⟧) ≅ Hᵠ(W ×_X Y, N|)`.

## Main statements

- `AlgebraicGeometry.Etale.subsingleton_H_forget₂_succ_of_injective`: on a quasi-compact
  quasi-separated scheme, injective sheaves of `Λ`-modules have acyclic underlying abelian sheaves.
- `AlgebraicGeometry.Etale.shiftedHomFunctorFreeSheafIso`: on such a scheme,
  `Hom(Λ_Z[0], N[0]⟦n⟧)` is the cohomology of the underlying abelian sheaf of `N`.
- `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject`:
  étale cohomology of a quasi-compact quasi-separated scheme commutes with filtered colimits.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme Etale

section FreeSheaf

variable {X Y : Scheme.{u}}

/-- Maps out of `v_! Λ[T]` are maps out of `Λ[T → V → Y]`, for `v : V ⟶ Y` étale. -/
noncomputable def Etale.etaleLowerShriekFreeSheafHomEquiv {V : Scheme.{u}} (v : V ⟶ Y)
    (hv : Etale v) (T : V.Etale) (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj ((Etale.freeSheaf Λ V).obj T) ⟶
      G) ≃ ((Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.map ⊤ hv).obj T) ⟶ G) :=
  (((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v hv).homEquiv _ _).trans
    (((Iso.refl _).homCongr
      ((Etale.upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) v hv).app G)).trans
    (Etale.freeSheafHomEquiv Λ T _))).trans (Etale.freeSheafHomEquiv Λ _ G).symm

lemma Etale.etaleLowerShriekFreeSheafHomEquiv_comp {V : Scheme.{u}} (v : V ⟶ Y)
    (hv : Etale v) (T : V.Etale) {G G' : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (f : (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj
      ((Etale.freeSheaf Λ V).obj T) ⟶ G) (g : G ⟶ G') :
    Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G' (f ≫ g) =
      Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G f ≫ g := by
  apply (Etale.freeSheafHomEquiv Λ _ G').injective
  simp only [Etale.etaleLowerShriekFreeSheafHomEquiv, Equiv.trans_apply,
    Etale.freeSheafHomEquiv_comp, Iso.homCongr_apply, Iso.refl_inv,
    Category.id_comp, Adjunction.homEquiv_naturality_right, Category.assoc, Iso.app_hom,
    NatTrans.naturality]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rfl

/-- Extension by zero of a free sheaf along an étale morphism `v : V ⟶ Y` is free:
`v_! Λ[T] ≅ Λ[T → V → Y]`, both corepresenting the functor `G ↦ G(T → V → Y)`. -/
noncomputable def Etale.etaleLowerShriekFreeSheafIso {V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)
    (T : V.Etale) :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj ((Etale.freeSheaf Λ V).obj T) ≅
      (Etale.freeSheaf Λ Y).obj ((MorphismProperty.Over.map ⊤ hv).obj T) :=
  (Coyoneda.fullyFaithful.preimageIso (NatIso.ofComponents
    (fun G ↦ (Etale.etaleLowerShriekFreeSheafHomEquiv Λ v hv T G).toIso)
    (fun g ↦ by
      ext f
      exact Etale.etaleLowerShriekFreeSheafHomEquiv_comp Λ v hv T f g))).unop.symm

end FreeSheaf

section Restriction

variable {Y V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)

instance Etale.additive_etaleLowerShriek :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).Additive :=
  (Etale.etaleLowerShriekUpperStarAdjunction _ v hv).left_adjoint_additive

instance Etale.isLeftAdjoint_etaleLowerShriek :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).IsLeftAdjoint :=
  (Etale.etaleLowerShriekUpperStarAdjunction _ v hv).isLeftAdjoint

/-- The derived adjunction `v_! ⊣ v^*` on bounded below derived categories, for an étale `v`:
both functors are exact. -/
noncomputable def Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus :
    (Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlus ⊣
      ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus :=
  ((Etale.etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) v hv).derivedPlus).ofNatIsoRight
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus _)

/-- The functor `N ↦ Hom(A[0], N[0]⟦q⟧)` on sheaves of `Λ`-modules on `Z_ét`; for `A = Λ` it is
the étale cohomology `N ↦ Hᵠ(Z, N)` with coefficients in `Λ`-modules. -/
@[reducible]
noncomputable def Etale.shiftedHomFunctor {Z : Scheme.{u}}
    (A : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤ AddCommGrpCat.{u + 1} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
    preadditiveCoyoneda.obj (op ((DerivedCategory.Plus.singleFunctor _ 0).obj A))

/-- `v^*` commutes with `N ↦ N[0]⟦q⟧`. -/
noncomputable def Etale.upperStarSingleShiftIso (q : ℤ) :
    DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q ⋙
        ((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q :=
  Functor.isoWhiskerLeft _ (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlus.commShiftIso q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (((v)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryPlusSingleFunctor 0)
      (shiftFunctor _ q) ≪≫ Functor.associator _ _ _

/-- The derived adjunction `v_! ⊣ v^*` on shifted maps out of a sheaf placed in degree `0`:
`Hom((v_! M)[0], N[0]⟦q⟧) ≃ Hom(M[0], (v^* N)[0]⟦q⟧)`. -/
noncomputable def Etale.etaleLowerShriekShiftedHomEquiv
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ((Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q).obj
      N) ≃+ ((Etale.shiftedHomFunctor Λ M q).obj ((v)^*[ModuleCat.{u + 1} Λ].obj N)) :=
  let i₁ := ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
    0).app M
  let i₂ := (Etale.upperStarSingleShiftIso Λ v hv q).app N
  let adj := Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv
  AddEquiv.mk'
    { toFun f := adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom
      invFun g := i₁.inv ≫ (adj.homEquiv _ _).symm (g ≫ i₂.inv)
      left_inv f := by simp
      right_inv g := by simp }
    (fun a b ↦ by
      simp only [Equiv.coe_fn_mk, Adjunction.homEquiv_unit]
      erw [Preadditive.comp_add, Functor.map_add, Preadditive.comp_add, Preadditive.add_comp])

lemma Etale.etaleLowerShriekShiftedHomEquiv_apply
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    (N : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (f : (Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M)
      q).obj N) :
    Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N f =
      (Etale.derivedEtaleLowerShriekUpperStarAdjunctionPlus Λ v hv).homEquiv _ _
        ((((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).mapDerivedCategoryPlusSingleFunctor
          0).app M).hom ≫ f) ≫ ((Etale.upperStarSingleShiftIso Λ v hv q).app N).hom :=
  rfl

/-- The derived adjunction `v_! ⊣ v^*` on shifted maps out of a sheaf placed in degree `0`,
naturally in the target. -/
noncomputable def Etale.etaleLowerShriekShiftedHomIso
    (M : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((Etale.etaleLowerShriek (ModuleCat.{u + 1} Λ) v hv).obj M) q ≅
      (v)^*[ModuleCat.{u + 1} Λ] ⋙ Etale.shiftedHomFunctor Λ M q :=
  NatIso.ofComponents
    (fun N ↦ (Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N).toAddCommGrpIso)
    (fun {N N'} g ↦ by
      ext f
      change Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N'
          (f ≫ (shiftFunctor _ q).map ((DerivedCategory.Plus.singleFunctor _ 0).map g)) =
        Etale.etaleLowerShriekShiftedHomEquiv Λ v hv M q N f ≫ (shiftFunctor _ q).map
          ((DerivedCategory.Plus.singleFunctor _ 0).map ((v)^*[ModuleCat.{u + 1} Λ].map g))
      rw [Etale.etaleLowerShriekShiftedHomEquiv_apply, Etale.etaleLowerShriekShiftedHomEquiv_apply,
        ← Category.assoc, Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc]
      congr 1
      exact (Etale.upperStarSingleShiftIso Λ v hv q).hom.naturality g)

end Restriction

/-- The final object of the small étale site of `Z`, the identity of `Z`. -/
noncomputable abbrev Etale.finalObject (Z : Scheme.{u}) : Z.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))

/-- The canonical section of the free sheaf `Λ[V]` over `V`, corresponding to `𝟙 Λ[V]`. -/
noncomputable def Etale.freeSheafGenerator {T : Scheme.{u}} (V : T.Etale) :
    ((Etale.freeSheaf Λ T).obj V).obj.obj (op V) :=
  Etale.freeSheafHomEquiv Λ V _ (𝟙 _)

/-- The free sheaf generator is natural: its restriction along `a : V' ⟶ V` is the image of the
generator of `Λ[V']` under `Λ[a]`. -/
lemma Etale.freeSheaf_map_freeSheafGenerator {T : Scheme.{u}} {V V' : T.Etale} (a : V' ⟶ V) :
    ((Etale.freeSheaf Λ T).map a).hom.app (op V') (Etale.freeSheafGenerator Λ V') =
      ((Etale.freeSheaf Λ T).obj V).obj.map a.op (Etale.freeSheafGenerator Λ V) := by
  rw [Etale.freeSheafGenerator, Etale.freeSheafGenerator, ← Etale.freeSheafHomEquiv_comp,
    ← Etale.freeSheafHomEquiv_map, Category.id_comp, Category.comp_id]

/-- The final object `𝟙 Z` of the small étale site of `Z` is terminal. -/
noncomputable def Etale.isTerminalFinalObject (Z : Scheme.{u}) :
    IsTerminal (Etale.finalObject Z) :=
  MorphismProperty.Over.mkIdTerminal _ Z

section Acyclicity

open Presheaf

/-- On a quasi-compact quasi-separated scheme `Z`, the underlying abelian sheaf of an injective
sheaf of `Λ`-modules has no higher cohomology, by the Čech criterion
`CategoryTheory.Sheaf.subsingleton_H_succ_of_exactAt_cechComplex` and
`CategoryTheory.Sheaf.exactAt_cechComplex_forget₂_of_injective`. -/
theorem Etale.subsingleton_H_forget₂_succ_of_injective (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (I : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [Injective I]
    (q : ℕ) :
    Subsingleton (Sheaf.H ((sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I) (q + 1)) := by
  let B : Z.Etale → Prop := fun W ↦ CompactSpace W.left ∧ QuasiSeparatedSpace W.left
  have hcov (V : Z.Etale) (hV : B V) (R : Sieve V) (hR : R ∈ Z.smallEtaleTopology V) :
      ∃ (n : ℕ) (U : Fin n → Over V),
        (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧ (∀ a, R (U a).hom) ∧
        Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ Z.smallEtaleTopology V := by
    obtain ⟨_, _⟩ := hV
    obtain ⟨n, U, g, hRg, hU, hg⟩ := exists_finite_affine_of_mem_smallEtaleTopology hR
    refine ⟨n, fun a ↦ Over.mk (g a), fun k y ↦ ?_, hRg,
      (ofArrows_mem_smallEtaleTopology_iff g).2 hg⟩
    refine compactSpace_and_quasiSeparatedSpace_piObj _ fun l ↦ ?_
    have := hU (y l)
    exact ⟨inferInstanceAs (CompactSpace (U (y l)).left),
      inferInstanceAs (QuasiSeparatedSpace (U (y l)).left)⟩
  let T : Z.Etale := MorphismProperty.Over.mk ⊤ (𝟙 Z) (inferInstance : Etale (𝟙 Z))
  have hT : IsTerminal T :=
    MorphismProperty.Over.mkIdTerminal _ Z
  have key := Sheaf.subsingleton_H_succ_of_exactAt_cechComplex hT B
    ⟨‹CompactSpace Z›, ‹QuasiSeparatedSpace Z›⟩ hcov ((sheafCompose Z.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj I)
    (fun _ _ _ U _ _ q ↦ Sheaf.exactAt_cechComplex_forget₂_of_injective I U q) q
  exact key

end Acyclicity

section Comparison

variable {Z : Scheme.{u}}

/-- The underlying abelian sheaf of a sheaf of `Λ`-modules on `Z_ét`. -/
noncomputable abbrev Etale.forget₂Sheaf (Z : Scheme.{u}) :
    Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  sheafCompose Z.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

instance Etale.additive_forget₂Sheaf : (Etale.forget₂Sheaf Λ Z).Additive where
  map_add := rfl

instance Etale.preservesFiniteLimits_forget₂Sheaf :
    PreservesFiniteLimits (Etale.forget₂Sheaf Λ Z) := by
  have : PreservesFiniteLimits (Etale.forget₂Sheaf Λ Z ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)

instance Etale.preservesColimitsOfSize_forget₂Sheaf :
    PreservesColimitsOfSize.{u + 1, u + 1} (Etale.forget₂Sheaf Λ Z) :=
  (Sheaf.forget₂CoinduceAdj Z.smallEtaleTopology Λ).leftAdjoint_preservesColimits

instance Etale.preservesFiniteColimits_forget₂Sheaf :
    PreservesFiniteColimits (Etale.forget₂Sheaf Λ Z) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

variable (Z) in
/-- The class in `H⁰(Z, Λ_Z)`, cohomology of the underlying abelian sheaf, of the global section
of the free sheaf `Λ_Z` given by the identity of `Z`. -/
noncomputable def Etale.freeSheafUnitClass :
    Sheaf.H ((Etale.forget₂Sheaf Λ Z).obj ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z))) 0 :=
  (Sheaf.H.equiv₀ _ (Etale.isTerminalFinalObject Z)).symm
    (Etale.freeSheafHomEquiv Λ (Etale.finalObject Z) _ (𝟙 _))

/-- The comparison map `Extⁿ(Λ_Z, N) ⟶ Hⁿ(Z, N)` from the cohomology of a sheaf of `Λ`-modules to
the cohomology of its underlying abelian sheaf: apply the exact forgetful functor and precompose
with the class of the unit section `ℤ_Z ⟶ Λ_Z`. -/
noncomputable def Etale.extFreeSheafToH (N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) :
    Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) N n →+
      Sheaf.H ((Etale.forget₂Sheaf Λ Z).obj N) n :=
  ((Etale.freeSheafUnitClass Λ Z).precomp _ (zero_add n)).comp
    ((Etale.forget₂Sheaf Λ Z).mapExtAddHom _ N n)

lemma Etale.extFreeSheafToH_apply (N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (n : ℕ) (x : Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) N n) :
    Etale.extFreeSheafToH Λ N n x =
      (Etale.freeSheafUnitClass Λ Z).comp (x.mapExactFunctor (Etale.forget₂Sheaf Λ Z))
        (zero_add n) :=
  rfl

lemma Etale.extFreeSheafToH_comp_mk₀ {N N' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : N ⟶ N') (n : ℕ)
    (x : Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) N n) :
    Etale.extFreeSheafToH Λ N' n (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) =
      Sheaf.H.map ((Etale.forget₂Sheaf Λ Z).map g) n (Etale.extFreeSheafToH Λ N n x) := by
  rw [Etale.extFreeSheafToH_apply, Etale.extFreeSheafToH_apply, Sheaf.H.map_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

lemma Etale.extFreeSheafToH_comp_extClass
    {S : ShortComplex (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (n : ℕ) (y : Abelian.Ext.{u + 1} ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) S.X₃ n) :
    Etale.extFreeSheafToH Λ S.X₁ (n + 1) (y.comp hS.extClass rfl) =
      (Etale.extFreeSheafToH Λ S.X₃ n y).comp
        (hS.map_of_exact (Etale.forget₂Sheaf Λ Z)).extClass rfl := by
  rw [Etale.extFreeSheafToH_apply, Etale.extFreeSheafToH_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_extClass]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

attribute [local instance] Abelian.Ext.subsingleton_of_injective in
/-- On a quasi-compact quasi-separated scheme, the cohomology of a sheaf of `Λ`-modules is the
cohomology of its underlying abelian sheaf: `Extⁿ(Λ_Z, N) ⟶ Hⁿ(Z, N)` is bijective. Both are
universal δ-functors, as the underlying abelian sheaves of injective sheaves of `Λ`-modules are
acyclic (`AlgebraicGeometry.Etale.subsingleton_H_forget₂_succ_of_injective`), and in degree `0`
both are the global sections. -/
theorem Etale.bijective_extFreeSheafToH [CompactSpace Z] [QuasiSeparatedSpace Z] (n : ℕ)
    (N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (Etale.extFreeSheafToH Λ N n) := by
  induction n generalizing N with
  | zero =>
    have h (f : (Etale.freeSheaf Λ Z).obj (Etale.finalObject Z) ⟶ N) :
        Etale.extFreeSheafToH Λ N 0 (Abelian.Ext.mk₀ f) =
          (Sheaf.H.equiv₀ _ (Etale.isTerminalFinalObject Z)).symm
            (Etale.freeSheafHomEquiv Λ _ N f) := by
      apply (Sheaf.H.equiv₀ _ (Etale.isTerminalFinalObject Z)).injective
      rw [AddEquiv.apply_symm_apply, Etale.extFreeSheafToH_apply,
        Abelian.Ext.mapExactFunctor_mk₀, ← Sheaf.H.map_apply, ← Sheaf.H.equiv₀_naturality,
        Etale.freeSheafUnitClass, AddEquiv.apply_symm_apply]
      conv_rhs => rw [← Category.id_comp f, Etale.freeSheafHomEquiv_comp]
      rfl
    have hc : (Etale.extFreeSheafToH Λ N 0) ∘ Abelian.Ext.mk₀ =
        (Sheaf.H.equiv₀ _ (Etale.isTerminalFinalObject Z)).symm ∘
          Etale.freeSheafHomEquiv Λ _ N := funext h
    refine (Function.Bijective.of_comp_iff _ (Abelian.Ext.mk₀_bijective _ _)).1 ?_
    rw [hc]
    exact (Sheaf.H.equiv₀ _ (Etale.isTerminalFinalObject Z)).symm.bijective.comp
      (Etale.freeSheafHomEquiv Λ _ N).bijective
  | succ n ih =>
    let I : InjectivePresentation N := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS : (T.map (Etale.forget₂Sheaf Λ Z)).ShortExact := hT.map_of_exact _
    have hI := Etale.subsingleton_H_forget₂_succ_of_injective Λ Z I.J n
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Abelian.Ext.mk₀ T.g).postcomp _ (add_zero n)) (hT.extClass.postcomp _ rfl)
      ((Abelian.Ext.mk₀ ((Etale.forget₂Sheaf Λ Z).map T.g)).postcomp _ (add_zero n))
      (hS.extClass.postcomp _ rfl)
      (Etale.extFreeSheafToH Λ I.J n) (Etale.extFreeSheafToH Λ T.X₃ n)
      (Etale.extFreeSheafToH Λ N (n + 1))
      (AddMonoidHom.ext fun x ↦ (Etale.extFreeSheafToH_comp_mk₀ Λ T.g n x).symm)
      (AddMonoidHom.ext fun y ↦ (Etale.extFreeSheafToH_comp_extClass Λ hT n y).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' _ hT n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      (ih I.J).2 (ih T.X₃)
      (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ _ hT x
        (Abelian.Ext.eq_zero_of_injective _) rfl)
      (fun y ↦ Abelian.Ext.covariant_sequence_exact₁ _ hS y (@Subsingleton.elim _ hI _ _) rfl)

end Comparison

section ShiftedHom

variable {Z : Scheme.{u}}

/-- Shifted morphisms `A[0] ⟶ N[0]⟦n⟧` in the bounded below derived category are
`Extⁿ(A, N)`, additively: `D⁺` is a full subcategory of the derived category, stable under
shifts. -/
noncomputable def Etale.shiftedHomFunctorObjAddEquivExt
    (A N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    (Etale.shiftedHomFunctor Λ A n).obj N ≃+ Abelian.Ext.{u + 1} A N n :=
  (AddEquiv.mk' ((ObjectProperty.fullyFaithfulι _).homEquiv.trans
      (Iso.homCongr (Iso.refl _) ((DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj N))))
    (fun a b ↦ by
      simp only [Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_inv]
      erw [Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_apply,
        Functor.FullyFaithful.homEquiv_apply, Functor.map_add, Preadditive.add_comp]
      exact Preadditive.comp_add _ _ _ _ _ _) :
      _ ≃+ ShiftedHom ((DerivedCategory.singleFunctor _ 0).obj A)
        ((DerivedCategory.singleFunctor _ 0).obj N) (n : ℤ)).trans
    (Abelian.Ext.homAddEquiv (X := A) (Y := N) (n := n)).symm

lemma Etale.shiftedHomFunctorObjAddEquivExt_naturality
    (A : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {N N' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (g : N ⟶ N') (n : ℕ)
    (f : (Etale.shiftedHomFunctor Λ A n).obj N) :
    Etale.shiftedHomFunctorObjAddEquivExt Λ A N' n ((Etale.shiftedHomFunctor Λ A n).map g f) =
      (Etale.shiftedHomFunctorObjAddEquivExt Λ A N n f).comp (Abelian.Ext.mk₀ g)
        (add_zero n) := by
  have key {N₀ : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (y : ShiftedHom
      ((DerivedCategory.singleFunctor _ 0).obj A) ((DerivedCategory.singleFunctor _ 0).obj N₀)
        (n : ℤ)) : (Abelian.Ext.homAddEquiv.{u + 1}.symm y).hom = y :=
    Abelian.Ext.homAddEquiv.apply_symm_apply y
  apply Abelian.Ext.homAddEquiv.injective
  rw [Abelian.Ext.homAddEquiv_apply, Abelian.Ext.homAddEquiv_apply, Abelian.Ext.comp_hom,
    Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  simp only [Etale.shiftedHomFunctorObjAddEquivExt, AddEquiv.trans_apply, key]
  change 𝟙 _ ≫ DerivedCategory.Plus.ι.map (f ≫ _) ≫ _ =
    (𝟙 _ ≫ DerivedCategory.Plus.ι.map f ≫ _) ≫ _
  rw [Category.id_comp, Category.id_comp, Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (DerivedCategory.Plus.ι.commShiftIso (n : ℤ)).hom.naturality
    ((DerivedCategory.Plus.singleFunctor _ 0).map g)

end ShiftedHom

section FilteredColimit

variable (Z : Scheme.{u}) [CompactSpace Z] [QuasiSeparatedSpace Z]

/-- On a quasi-compact quasi-separated scheme, the cohomology `Hⁿ(Z, -)` of abelian sheaves
commutes with filtered colimits, by `AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`. -/
lemma Etale.preservesColimitsOfShape_functorH (n : ℕ) (J : Type (u + 1)) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J (Sheaf.functorH Z.smallEtaleTopology n) := by
  refine ⟨fun {K} ↦ ⟨fun {c} hc ↦ ⟨?_⟩⟩⟩
  obtain ⟨h₁, h₂⟩ := Scheme.H_map_isColimit_of_isFiltered Z hc n
  have : ReflectsColimitsOfShape J (forget AddCommGrpCat.{u + 1}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget AddCommGrpCat.{u + 1})
    (Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j x y hxy ↦ ?_))
  · obtain ⟨j, y, rfl⟩ := h₁ x
    exact ⟨j, y, rfl⟩
  · have hxy' : Sheaf.H.map (c.ι.app j) n x = Sheaf.H.map (c.ι.app j) n y := hxy
    obtain ⟨k, φ, hk⟩ := h₂ j (x - y) (by rw [map_sub, hxy', sub_self])
    refine ⟨k, φ, ?_⟩
    change Sheaf.H.map (K.map φ) n x = Sheaf.H.map (K.map φ) n y
    rw [← sub_eq_zero, ← map_sub]
    exact hk

/-- On a quasi-compact quasi-separated scheme `Z`, the cohomology `Hom(Λ_Z[0], N[0]⟦n⟧)` of a
sheaf of `Λ`-modules is the cohomology of its underlying abelian sheaf, naturally in `N`. -/
noncomputable def Etale.shiftedHomFunctorFreeSheafIso (n : ℕ) :
    Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) n ≅
      Etale.forget₂Sheaf Λ Z ⋙ Sheaf.functorH Z.smallEtaleTopology n :=
  NatIso.ofComponents
    (fun N ↦ ((Etale.shiftedHomFunctorObjAddEquivExt Λ _ N n).trans
      (AddEquiv.ofBijective (Etale.extFreeSheafToH Λ N n)
        (Etale.bijective_extFreeSheafToH Λ n N))).toAddCommGrpIso)
    (fun {N N'} g ↦ by
      ext f
      change Etale.extFreeSheafToH Λ N' n (Etale.shiftedHomFunctorObjAddEquivExt Λ _ N' n
          ((Etale.shiftedHomFunctor Λ _ n).map g f)) =
        Sheaf.H.map ((Etale.forget₂Sheaf Λ Z).map g) n
          (Etale.extFreeSheafToH Λ N n (Etale.shiftedHomFunctorObjAddEquivExt Λ _ N n f))
      rw [Etale.shiftedHomFunctorObjAddEquivExt_naturality, Etale.extFreeSheafToH_comp_mk₀])

/-- In negative degrees `q`, there are no shifted morphisms `A[0] ⟶ N[0]⟦q⟧`. -/
lemma Etale.isZero_shiftedHomFunctor_obj_of_neg {Z : Scheme.{u}}
    (A N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) {q : ℤ} (hq : q < 0) :
    IsZero ((Etale.shiftedHomFunctor Λ A q).obj N) := by
  have : DerivedCategory.Plus.TStructure.t.IsGE
      ((shiftFunctor _ q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N)) (-q) :=
    DerivedCategory.Plus.TStructure.t.isGE_shift _ 0 q (-q) (by omega)
  have : Subsingleton ((Etale.shiftedHomFunctor Λ A q).obj N) := ⟨fun a b ↦
    (DerivedCategory.Plus.TStructure.t.zero (show (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N) from a) 0 (-q)
        (by omega)).trans
    (DerivedCategory.Plus.TStructure.t.zero (show (DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      (shiftFunctor _ q).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N) from b) 0 (-q)
        (by omega)).symm⟩
  exact AddCommGrpCat.isZero_of_subsingleton _

end FilteredColimit

/-- Blueprint `lemma-finiteness-small-etale-topoi--2` (subsection
`lem-sc-second-kummer-divisors`): Filtered colimits of étale cohomology. Let `Z` be a quasi-compact
and quasi-separated scheme. Then étale cohomology `N ↦ Hᵠ(Z, N) = Hom(Λ_Z[0], N[0]⟦q⟧)` with
coefficients in sheaves of `Λ`-modules commutes with filtered colimits:
`colim Hᵠ(Z, N_a) ≅ Hᵠ(Z, colim N_a)`.

The same statement for abelian sheaves is
`AlgebraicGeometry.Scheme.H_map_isColimit_of_isFiltered`. As in the blueprint, there is no
restriction on the size of the filtered category beyond that of the coefficients: it may be any
filtered category in `Type (u + 1)`, the universe of the sheaves of `Λ`-modules.

The proof identifies the functor with abelian sheaf cohomology of the underlying abelian sheaf
(`AlgebraicGeometry.Etale.shiftedHomFunctorFreeSheafIso`) in nonnegative degrees; in negative
degrees it vanishes. -/
@[stacks 03Q6]
theorem Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject (Z : Scheme.{u})
    [CompactSpace Z] [QuasiSeparatedSpace Z] (q : ℤ) (J : Type (u + 1)) [SmallCategory J]
    [IsFiltered J] :
    PreservesColimitsOfShape J
      (Etale.shiftedHomFunctor Λ ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) q) := by
  rcases le_or_gt 0 q with hq | hq
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    have := Etale.preservesColimitsOfShape_functorH Z n J
    exact preservesColimitsOfShape_of_natIso (Etale.shiftedHomFunctorFreeSheafIso Λ Z n).symm
  · have hz (N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
      Etale.isZero_shiftedHomFunctor_obj_of_neg Λ
        ((Etale.freeSheaf Λ Z).obj (Etale.finalObject Z)) N hq
    exact ⟨fun {K} ↦ ⟨fun {c} _ ↦ ⟨
      { desc s := (hz c.pt).to_ s.pt
        fac _ _ := (hz _).eq_of_src _ _
        uniq _ _ _ := (hz _).eq_of_src _ _ }⟩⟩⟩

/-- An isomorphism `A ≅ A'` identifies the functors `N ↦ Hom(A[0], N[0]⟦q⟧)` and
`N ↦ Hom(A'[0], N[0]⟦q⟧)`. -/
noncomputable def Etale.shiftedHomFunctorMapIso {Z : Scheme.{u}}
    {A A' : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : A ≅ A') (q : ℤ) :
    Etale.shiftedHomFunctor Λ A q ≅ Etale.shiftedHomFunctor Λ A' q :=
  Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor _ 0 ⋙ shiftFunctor _ q)
    (preadditiveCoyoneda.mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso e).symm.op)

section Pullback

variable {X Y : Scheme.{u}} (h : Y ⟶ X)

/-- An étale `Y`-scheme `W`, as an étale scheme over itself extended along its structure
morphism, is `W`. -/
noncomputable def Etale.overMapFinalObjectIso (W : Y.Etale) :
    (MorphismProperty.Over.map ⊤ W.prop).obj (Etale.finalObject W.left) ≅ W :=
  MorphismProperty.Over.isoMk (Iso.refl _) rfl

/-- The functor `N ↦ Hom((h^* Λ[W])[0], N[0]⟦q⟧)` is the cohomology functor of `W ×_X Y`
precomposed with restriction. -/
noncomputable def Etale.shiftedHomFunctorUpperStarFreeSheafIso (W : X.Etale) (q : ℤ) :
    Etale.shiftedHomFunctor Λ ((h)^*[ModuleCat.{u + 1} Λ].obj ((Etale.freeSheaf Λ X).obj W)) q ≅
      (((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).hom)^*[ModuleCat.{u + 1} Λ] ⋙
        Etale.shiftedHomFunctor Λ
          ((Etale.freeSheaf Λ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).left).obj
            (Etale.finalObject _)) q :=
  Etale.shiftedHomFunctorMapIso Λ (Etale.upperStarFreeSheafIso Λ h W ≪≫
    (Etale.freeSheaf Λ Y).mapIso (Etale.overMapFinalObjectIso _).symm ≪≫
    (Etale.etaleLowerShriekFreeSheafIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
      (Etale.finalObject _)).symm) q ≪≫
  Etale.etaleLowerShriekShiftedHomIso Λ _ ((MorphismProperty.Over.pullback @Etale ⊤ h).obj W).prop
    _ q

end Pullback

end AlgebraicGeometry

section

/-!
# Free sheaves under extension by zero and pullback, and cohomology

For an étale `v : V ⟶ Y`, extension by zero sends the free sheaf `Λ[T]` on an étale
`V`-scheme `T` to the free sheaf on `T → V → Y`, and the derived adjunction `v_! ⊣ v^*`
identifies `Hom((v_! M)[0], N[0]⟦q⟧)` with `Hom(M[0], (v^* N)[0]⟦q⟧)`. Combined with
`h^* Λ[W] ≅ Λ[W ×_X Y]`, this computes `Hom((h^* Λ[W])[0], N[0]⟦q⟧)` as the étale cohomology
`Hᵠ(W ×_X Y, N|)` of the scheme `W ×_X Y`. The file also states that étale cohomology of a
quasi-compact quasi-separated scheme commutes with filtered colimits.

## Main definitions

- `AlgebraicGeometry.Etale.etaleLowerShriekFreeSheafIso`: `v_! Λ[T] ≅ Λ[T → V → Y]`.
- `AlgebraicGeometry.Etale.shiftedHomFunctor`: the functor `N ↦ Hom(A[0], N[0]⟦q⟧)`.
- `AlgebraicGeometry.Etale.etaleLowerShriekShiftedHomIso`: the derived adjunction `v_! ⊣ v^*`
  on shifted maps out of a sheaf in degree `0`.
- `AlgebraicGeometry.Etale.shiftedHomFunctorUpperStarFreeSheafIso`:
  `Hom((h^* Λ[W])[0], N[0]⟦q⟧) ≅ Hᵠ(W ×_X Y, N|)`.

## Main statements

- `AlgebraicGeometry.Etale.preservesColimitsOfShape_shiftedHomFunctor_freeSheaf_finalObject`:
  étale cohomology of a quasi-compact quasi-separated scheme commutes with filtered colimits.
-/

@[expose] public section

universe w

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ]

open Scheme Etale

section FreeSheaf

variable {X Y : Scheme.{u}}







end FreeSheaf

section Restriction

variable {Y V : Scheme.{u}} (v : V ⟶ Y) (hv : Etale v)









/-- An exact functor commutes with degree-zero single objects and shifts.
This is the composition of its single-object and shift comparison isomorphisms. -/
noncomputable def Etale.exactSingleShiftIso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (q : ℤ) :
    DerivedCategory.Plus.singleFunctor C 0 ⋙ shiftFunctor _ q ⋙ F.mapDerivedCategoryPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor D 0 ⋙ shiftFunctor _ q :=
  Functor.isoWhiskerLeft _ (F.mapDerivedCategoryPlus.commShiftIso q) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (F.mapDerivedCategoryPlusSingleFunctor 0) (shiftFunctor _ q) ≪≫
    Functor.associator _ _ _

/-- A named copy of pullback used to share its derived-shift comparison instances. -/
noncomputable def Etale.upperStarForShift :
    Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (v)^*[ModuleCat.{u + 1} Λ]

instance Etale.additive_upperStarForShift : (Etale.upperStarForShift Λ v).Additive := by
  dsimp [Etale.upperStarForShift]
  infer_instance

/-- Pullback, in its named presentation, preserves finite limits. -/
theorem Etale.preservesFiniteLimits_upperStarForShift :
    PreservesFiniteLimits (Etale.upperStarForShift Λ v) := by
  dsimp [Etale.upperStarForShift]
  infer_instance

instance Etale.preservesFiniteColimits_upperStarForShift :
    PreservesFiniteColimits (Etale.upperStarForShift Λ v) := by
  dsimp [Etale.upperStarForShift]
  infer_instance



/-- Transport the additive Hom equivalence of an adjunction across two isomorphisms. -/
noncomputable def Etale.adjunctionHomAddEquivOfIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R)
    {M : C} {N A : D} {B : C} (i₁ : L.obj M ≅ A) (i₂ : R.obj N ≅ B) :
    (A ⟶ N) ≃+ (M ⟶ B) :=
  AddEquiv.mk'
    { toFun f := adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom
      invFun g := i₁.inv ≫ (adj.homEquiv _ _).symm (g ≫ i₂.inv)
      left_inv f := by simp
      right_inv g := by simp }
    (fun f g ↦ by simp)

lemma Etale.adjunctionHomAddEquivOfIso_apply
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R)
    {M : C} {N A : D} {B : C} (i₁ : L.obj M ≅ A) (i₂ : R.obj N ≅ B) (f : A ⟶ N) :
    Etale.adjunctionHomAddEquivOfIso adj i₁ i₂ f =
      adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom := rfl

/-- The transported additive Hom equivalence is natural in its target argument. -/
noncomputable def Etale.adjunctionHomNatIso
    {C D E : Type*} [Category.{w} C] [Category.{w} D] [Category E]
    [Preadditive C] [Preadditive D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] (adj : L ⊣ R)
    {M : C} {A : D} (i₁ : L.obj M ≅ A) (S : E ⥤ D) (T : E ⥤ C)
    (e : S ⋙ R ≅ T) :
    S ⋙ preadditiveCoyoneda.obj (op A) ≅ T ⋙ preadditiveCoyoneda.obj (op M) :=
  NatIso.ofComponents
    (fun N ↦ (Etale.adjunctionHomAddEquivOfIso adj i₁ (e.app N)).toAddCommGrpIso)
    (fun {N N'} g ↦ by
      ext f
      change Etale.adjunctionHomAddEquivOfIso adj i₁ (e.app N') (f ≫ S.map g) =
        Etale.adjunctionHomAddEquivOfIso adj i₁ (e.app N) f ≫ T.map g
      rw [Etale.adjunctionHomAddEquivOfIso_apply, Etale.adjunctionHomAddEquivOfIso_apply,
        ← Category.assoc, Adjunction.homEquiv_naturality_right, Category.assoc, Category.assoc]
      congr 1
      exact e.hom.naturality g)



end Restriction







section Pullback

variable {X Y : Scheme.{u}} (h : Y ⟶ X)





end Pullback

end AlgebraicGeometry

end
