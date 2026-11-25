/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.ConstructibleSheaf.FiniteEtalePushforward
public import WeilConjectures.ConstructibleSheaf.GenericConstancy
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.FiniteProjectiveResolution
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
public import WeilConjectures.SixFunctors.Etale.Derived.Triangulated

/-!
# Tor sheaves of constructible sheaves

For a commutative ring `Λ` and sheaves `F`, `G` of `Λ`-modules on `X_ét`, the *Tor sheaves*
are the homology sheaves `Hʳ(F ⊗ᴸ G)` of the derived tensor product of `F` and `G` placed in
degree `0` (`AlgebraicGeometry.Etale.torSheaf`). This file shows that for a noetherian ring `Λ`
the Tor sheaves of two constructible sheaves are constructible
(blueprint: `proposition-six-operations-dctf--14`), following the blueprint proof.

* On the strata of a common refinement of stratifications witnessing the constructibility of `F`
  and `G`, both pullbacks are finite locally constant; the pullback along any morphism commutes
  with Tor sheaves (`AlgebraicGeometry.Etale.upperStarTorSheafIso`), the pullback being exact
  and its derived functor monoidal.
* Finite local constancy is étale local
  (`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.of_cover`), and two finite locally
  constant sheaves are constant on a common étale cover, with finitely generated values `M`
  and `N`.
* The Tor sheaves of the constant sheaves `M_Y` and `N_Y` are computed with a projective
  resolution `P` of `M` by finitely generated modules: `P_Y` is a bounded above complex of flat
  sheaves, hence K-flat, so `Hʳ(M_Y ⊗ᴸ N_Y)` is the constant sheaf at the finitely generated
  module `Hʳ(P ⊗ N) = Tor_{-r}(M, N)`
  (`AlgebraicGeometry.Etale.homologyDerivedTensorConstantSheafIso`).
-/

@[expose] public section

universe u u'

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

/-- **Finite local constancy is étale local**: if the pullbacks of `G` to the members of an
étale cover are finite locally constant, so is `G`. A geometric point of `X` lifts to a member
of the cover, where the stalk is that of the pullback. -/
theorem Scheme.IsFiniteLocallyConstantSheaf.of_cover {A : Type u'} [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
    [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{u + 1} A FA] {X : Scheme.{u}}
    (𝒰 : Cover.{u} etalePrecoverage X) (G : Sheaf X.smallEtaleTopology A)
    [∀ i, IsFiniteLocallyConstantSheaf ((Etale.upperStar A (𝒰.f i)).obj G)] :
    IsFiniteLocallyConstantSheaf G where
  toIsLocallyConstantSheaf := IsLocallyConstantSheaf.of_cover 𝒰 G
  toIsFiniteSheaf := ⟨fun Ω _ _ s ↦ by
    obtain ⟨i, x, hx⟩ := 𝒰.exists_eq (s (IsLocalRing.closedPoint _))
    have : _root_.AlgebraicGeometry.Etale (𝒰.f i) := 𝒰.map_prop i
    obtain ⟨s', rfl⟩ := exists_comp_eq_of_etale (𝒰.f i) s ⟨x, hx⟩
    exact (IsFiniteSheaf.isFinitelyGenerated_sheafFiber (FA := FA) (CA := CA)
      (F := (Etale.upperStar A (𝒰.f i)).obj G) Ω s').of_iso
      ((Etale.upperStarCompSheafFiberIso A (𝒰.f i) s').app G)⟩

namespace Etale

open _root_.AlgebraicGeometry.Etale.DerivedCategory

/-! ### Tor sheaves of constant sheaves, for a general coefficient category -/

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

attribute [local instance] Sheaf.monoidalCategory Abelian.hasFiniteBiproducts

omit [Abelian.HasFunctorialFlatResolution A] in
/-- The constant sheaf at a retract of a finite direct sum of copies of the unit is flat: it is
a retract of a finite direct sum of copies of the unit sheaf, the constant sheaf functor being
additive and monoidal. -/
lemma flat_constantSheaf_obj_of_retract {Y : Scheme.{u}} {J : Type} [Finite J] {X : A}
    (h : Retract X (⨁ fun _ : J ↦ 𝟙_ A)) :
    ObjectProperty.flat ((constantSheaf Y.smallEtaleTopology A).obj X) := by
  let c := constantSheaf Y.smallEtaleTopology A
  have : c.Additive := Functor.additive_of_preserves_binary_products c
  refine ObjectProperty.flat_of_retract (h.map c) ?_
  have hu : ObjectProperty.flat (𝟙_ (Sheaf Y.smallEtaleTopology A)) :=
    ObjectProperty.flat_of_tensorIso (λ_ _)
  have hs : ObjectProperty.flat (∐ fun _ : ULift.{u + 1} J ↦ 𝟙_ (Sheaf Y.smallEtaleTopology A)) :=
    ObjectProperty.flat_coproduct _ fun _ ↦ hu
  exact ObjectProperty.prop_of_iso _ (Sigma.whiskerEquiv Equiv.ulift (fun _ ↦ Iso.refl _) ≪≫
    (biproduct.isoCoproduct _).symm ≪≫
    biproduct.mapIso (fun _ ↦ Functor.Monoidal.εIso c) ≪≫ (c.mapBiproduct _).symm) hs

/-- The constant case of the constructibility of Tor sheaves: the Tor sheaves of constant
sheaves are constant. Let `π : P ⟶ M[0]` be a quasi-isomorphism from a complex `P`
concentrated in degrees `≤ 0` whose terms have flat constant sheaves (for instance a
projective resolution by finitely generated modules). Then `P_Y` is K-flat and resolves
`M_Y`, so `M_Y ⊗ᴸ N_Y` is computed by the complex `P_Y ⊗ N_Y = (P ⊗ N)_Y`, and
`Hʳ(M_Y ⊗ᴸ N_Y)` is the constant sheaf at `Hʳ(P ⊗ N) = Tor_{-r}(M, N)`.
(blueprint: `proposition-six-operations-dctf--14`) -/
noncomputable def homologyDerivedTensorConstantSheafIso {Y : Scheme.{u}}
    (P : CochainComplex A ℤ) [P.IsStrictlyLE 0]
    (hP : ∀ n, ObjectProperty.flat ((constantSheaf Y.smallEtaleTopology A).obj (P.X n)))
    {M : A} (π : P ⟶ (HomologicalComplex.single A (.up ℤ) 0).obj M) [QuasiIso π]
    (N : A) (r : ℤ) :
    (_root_.DerivedCategory.homologyFunctor _ r).obj
      (((-⊗ᴸ-(Y)[A]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf Y.smallEtaleTopology A).obj M))).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            ((constantSheaf Y.smallEtaleTopology A).obj N))) ≅
      (constantSheaf Y.smallEtaleTopology A).obj
        ((HomologicalComplex.homologyFunctor A (.up ℤ) r).obj
          (((tensorRight N).mapHomologicalComplex (.up ℤ)).obj P)) := by
  let c := constantSheaf Y.smallEtaleTopology A
  let cP := (c.mapHomologicalComplex (.up ℤ)).obj P
  have hk : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat cP :=
    CochainComplex.kFlat_of_isStrictlyLE_of_flat cP 0 hP
  have : IsIso (_root_.DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).map π)) := by
    rw [_root_.DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let e₁ : (_root_.DerivedCategory.singleFunctor _ 0).obj (c.obj M) ≅
      _root_.DerivedCategory.Q.obj cP :=
    (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app _ ≪≫
      _root_.DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex c (.up ℤ) 0).app M).symm ≪≫
      (asIso (_root_.DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).map π))).symm
  let e₂ : c ⋙ tensorRight (c.obj N) ≅ tensorRight N ⋙ c :=
    NatIso.ofComponents (fun X ↦ Functor.Monoidal.μIso c X N)
      (fun f ↦ by simp [Functor.LaxMonoidal.μ_natural_left])
  exact (_root_.DerivedCategory.homologyFunctor _ r).mapIso
      (((-⊗ᴸ-(Y)[A]).mapIso e₁).app _ ≪≫
        _root_.DerivedCategory.QObjTensorSingleFunctorObjIso cP hk (c.obj N) ≪≫
        _root_.DerivedCategory.Q.mapIso
          ((Functor.mapHomologicalComplexCompIso e₂ (.up ℤ)).app P ≪≫
            ((Functor.mapHomologicalComplexCompIso (Iso.refl (tensorRight N ⋙ c))
              (.up ℤ)).app P).symm)) ≪≫
    (_root_.DerivedCategory.homologyFunctorFactors _ r).app _ ≪≫
    (c.mapHomologicalComplexHomologyIso (.up ℤ) r).app _

end General

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The `r`-th *Tor sheaf* `Hʳ(F ⊗ᴸ G)` of two sheaves of `Λ`-modules on `X_ét`: the `r`-th
homology sheaf of the derived tensor product of `F` and `G` placed in degree `0`. -/
noncomputable abbrev torSheaf {X : Scheme.{u}} (r : ℤ)
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (_root_.DerivedCategory.homologyFunctor _ r).obj
    (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj F)).obj
      ((_root_.DerivedCategory.singleFunctor _ 0).obj G))

/-- The Tor sheaves are functorial in isomorphisms of both variables. -/
noncomputable def torSheafMapIso {X : Scheme.{u}} (r : ℤ)
    {F F' G G' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : F ≅ F') (e' : G ≅ G') :
    torSheaf Λ r F G ≅ torSheaf Λ r F' G' :=
  (_root_.DerivedCategory.homologyFunctor _ r).mapIso
    (((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).mapIso
      ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e)).app _ ≪≫
      ((-⊗ᴸ-(X)[ModuleCat.{u + 1} Λ]).obj _).mapIso
        ((_root_.DerivedCategory.singleFunctor _ 0).mapIso e'))

/-- The pullback of a Tor sheaf is the Tor sheaf of the pullbacks,
`g^* Hʳ(F ⊗ᴸ G) ≅ Hʳ(g^*F ⊗ᴸ g^*G)`: the pullback `g^*` is exact, so it commutes with homology
and `Lg^* ≅ D(g^*)`, and `Lg^*` is monoidal. -/
noncomputable def upperStarTorSheafIso {X Y : Scheme.{u}} (g : Y ⟶ X) (r : ℤ)
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (g)^*[ModuleCat.{u + 1} Λ].obj (torSheaf Λ r F G) ≅
      torSheaf Λ r ((g)^*[ModuleCat.{u + 1} Λ].obj F) ((g)^*[ModuleCat.{u + 1} Λ].obj G) :=
  let e (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
      L((g)^*[ModuleCat.{u + 1} Λ]).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj H) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj ((g)^*[ModuleCat.{u + 1} Λ].obj H) :=
    (leftDerivedUpperStarIsoMapDerivedCategory _ g).app _ ≪≫
      ((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategorySingleFunctor 0).app H
  ((g)^*[ModuleCat.{u + 1} Λ].mapDerivedCategoryHomologyFunctorIso r).app _ ≪≫
    (_root_.DerivedCategory.homologyFunctor _ r).mapIso
      (((leftDerivedUpperStarIsoMapDerivedCategory _ g).app _).symm ≪≫
        leftDerivedUpperStarTensorIso _ g _ _ ≪≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).mapIso (e F)).app _ ≪≫
        ((-⊗ᴸ-(Y)[ModuleCat.{u + 1} Λ]).obj _).mapIso (e G))

/-! ### Tor sheaves over a noetherian ring -/

section Noetherian

variable {Λ}

/-- A finitely generated projective `Λ`-module is a retract of a finite direct sum of copies of
`Λ`: a surjection from a finite free module splits. -/
lemma exists_retract_biproduct_unit_of_projective (X : ModuleCat.{u + 1} Λ) [Projective X]
    [Module.Finite Λ X] :
    ∃ (J : Type) (_ : Finite J),
      Nonempty (Retract X (⨁ fun _ : J ↦ 𝟙_ (ModuleCat.{u + 1} Λ))) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' Λ X
  let g : (⨁ fun _ : Fin n ↦ 𝟙_ (ModuleCat.{u + 1} Λ)) ⟶ X :=
    (ModuleCat.biproductIsoPi _).hom ≫ ModuleCat.ofHom f
  have : Epi g := by
    refine (ModuleCat.epi_iff_surjective _).2 ?_
    simp only [g, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp]
    exact hf.comp (ModuleCat.biproductIsoPi _).toLinearEquiv.surjective
  exact ⟨Fin n, inferInstance, ⟨⟨Projective.factorThru (𝟙 X) g, g, by simp⟩⟩⟩

variable (Λ) [IsNoetherianRing Λ]

/-- The constant case of the constructibility of Tor sheaves: for finitely generated
`Λ`-modules `M` and `N`, the Tor sheaves of the constant sheaves `M_Y` and `N_Y` are finite
locally constant. With a projective resolution `P` of `M` by finitely generated modules,
`Hʳ(M_Y ⊗ᴸ N_Y)` is the constant sheaf at `Hʳ(P ⊗ N) = Tor_{-r}(M, N)`
(`AlgebraicGeometry.Etale.homologyDerivedTensorConstantSheafIso`), a subquotient of the
finitely generated module `P^r ⊗ N`, hence finitely generated, `Λ` being noetherian.
(blueprint: `proposition-six-operations-dctf--14`) -/
theorem isFiniteLocallyConstantSheaf_torSheaf_constantSheaf {Y : Scheme.{u}}
    (M N : ModuleCat.{u + 1} Λ) [Module.Finite Λ M] [Module.Finite Λ N] (r : ℤ) :
    IsFiniteLocallyConstantSheaf (torSheaf Λ r
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj N)) := by
  obtain ⟨R, hR⟩ := ModuleCat.exists_projectiveResolution_moduleFinite M
  have hfin (n : ℤ) : Module.Finite Λ (R.cochainComplex.X n) := by
    by_cases hn : n ≤ 0
    · obtain ⟨k, rfl⟩ := Int.exists_eq_neg_ofNat hn
      have := hR k
      exact Module.Finite.equiv (R.cochainComplexXIso (-k) k rfl).symm.toLinearEquiv
    · have : Subsingleton (R.cochainComplex.X n) := ModuleCat.subsingleton_of_isZero
        (R.cochainComplex.isZero_of_isStrictlyLE 0 n (by lia))
      infer_instance
  let K := ((tensorRight N).mapHomologicalComplex (.up ℤ)).obj R.cochainComplex
  have : Module.Finite Λ (K.X r) := by
    have := hfin r
    change Module.Finite Λ (TensorProduct Λ (R.cochainComplex.X r) N)
    infer_instance
  have : Module.Finite Λ
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u + 1} Λ) (.up ℤ) r).obj K) := by
    have hi : Function.Injective (K.iCycles r) :=
      (ModuleCat.mono_iff_injective _).1 inferInstance
    have hp : Function.Surjective (K.homologyπ r) :=
      (ModuleCat.epi_iff_surjective _).1 inferInstance
    have : Module.Finite Λ (K.cycles r) := Module.Finite.of_injective (K.iCycles r).hom hi
    exact Module.Finite.of_surjective (K.homologyπ r).hom hp
  exact IsFiniteLocallyConstantSheaf.of_iso
    (homologyDerivedTensorConstantSheafIso (ModuleCat.{u + 1} Λ) R.cochainComplex (fun n ↦ by
      have := hfin n
      obtain ⟨J, _, ⟨h⟩⟩ := exists_retract_biproduct_unit_of_projective (R.cochainComplex.X n)
      exact flat_constantSheaf_obj_of_retract _ h) R.π' N r).symm

/-- The locally constant case of the constructibility of Tor sheaves: the Tor sheaves of
two finite locally constant sheaves of modules over a noetherian ring are finite locally
constant. On a common étale cover both sheaves are constant, with finitely generated values `M`
and `N`; the pullback to a member of the cover commutes with Tor sheaves
(`AlgebraicGeometry.Etale.upperStarTorSheafIso`), and the Tor sheaves of `M` and `N` are
finite locally constant
(`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_torSheaf_constantSheaf`). Finite local
constancy is étale local. (blueprint: `proposition-six-operations-dctf--14`) -/
theorem isFiniteLocallyConstantSheaf_torSheaf {Z : Scheme.{u}}
    (F G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    [IsFiniteLocallyConstantSheaf G] (r : ℤ) :
    IsFiniteLocallyConstantSheaf (torSheaf Λ r F G) := by
  obtain ⟨𝒰₀, h𝒰₀⟩ := IsLocallyConstantSheaf.exists_cover₂ F G
  let 𝒰 := 𝒰₀.nonemptyMembers
  have (i : 𝒰.I₀) : IsFiniteLocallyConstantSheaf
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj (torSheaf Λ r F G)) := by
    have : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F).IsConstant
        (𝒰.X i).smallEtaleTopology := (h𝒰₀ i.1).1
    have : ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G).IsConstant
        (𝒰.X i).smallEtaleTopology := (h𝒰₀ i.1).2
    obtain ⟨M, ⟨eF⟩⟩ :=
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj F).mem_essImage_of_isConstant
    obtain ⟨N, ⟨eG⟩⟩ :=
      ((Etale.upperStar (ModuleCat.{u + 1} Λ) (𝒰.f i)).obj G).mem_essImage_of_isConstant
    have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (𝒰.f i) F
    have := IsFiniteSheaf.upperStar (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) (𝒰.f i) G
    have := IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) eF.symm
    have := IsFiniteSheaf.of_iso (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) eG.symm
    have : Module.Finite Λ M := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := 𝒰.X i) M
    have : Module.Finite Λ N := moduleFinite_of_isFiniteSheaf_constantSheaf (Y := 𝒰.X i) N
    have := isFiniteLocallyConstantSheaf_torSheaf_constantSheaf Λ (Y := 𝒰.X i) M N r
    exact IsFiniteLocallyConstantSheaf.of_iso
      (torSheafMapIso Λ r eF eG ≪≫ (upperStarTorSheafIso Λ (𝒰.f i) r F G).symm)
  exact IsFiniteLocallyConstantSheaf.of_cover 𝒰 _

/-- **Tor sheaves of constructible sheaves are constructible.** For a
noetherian ring `Λ` and constructible sheaves `F` and `G` of `Λ`-modules on `X_ét`, every Tor
sheaf `Hʳ(F ⊗ᴸ G)` is constructible. On the strata of a common refinement of witnessing
stratifications both pullbacks are finite locally constant, the pullback commutes with Tor
sheaves (`AlgebraicGeometry.Etale.upperStarTorSheafIso`), and the Tor sheaves of finite
locally constant sheaves are finite locally constant
(`AlgebraicGeometry.Etale.isFiniteLocallyConstantSheaf_torSheaf`).
(blueprint: `proposition-six-operations-dctf--14`) -/
theorem isConstructibleSheaf_torSheaf {X : Scheme.{u}}
    (F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf F]
    [IsConstructibleSheaf G] (r : ℤ) :
    IsConstructibleSheaf (torSheaf Λ r F G) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := F)
  obtain ⟨T, hT⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := G)
  refine ⟨⟨S.inter T, fun k ↦ ?_⟩⟩
  have := (S.inter_refines_left T).isFiniteLocallyConstantSheaf_upperStar F hS k
  have := (S.inter_refines_right T).isFiniteLocallyConstantSheaf_upperStar G hT k
  have := isFiniteLocallyConstantSheaf_torSheaf Λ
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).obj F)
    ((Etale.upperStar (ModuleCat.{u + 1} Λ) ((S.inter T).immersion k)).obj G) r
  exact IsFiniteLocallyConstantSheaf.of_iso
    (upperStarTorSheafIso Λ ((S.inter T).immersion k) r F G).symm

end Noetherian

end Etale

end AlgebraicGeometry
