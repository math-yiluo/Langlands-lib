/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Sites.PointCohomology
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Equivalence
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import WeilConjectures.CategoryTheory.Sites.Point.Flat
public import WeilConjectures.ConstructibleSheaf.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect

/-!
# The point category

Let `k` be a separably closed field and `s = Spec k`. An étale sheaf on `s` is determined by its
global sections (`AlgebraicGeometry.Scheme.isZero_of_subsingleton_sections_of_isSepClosed`). In
the derived category `D(s_ét, Λ)` of étale sheaves of `Λ`-modules, the *point category*, the
shifts `Λ_s[r]` of the constant complex therefore detect isomorphisms.

## Main statements

- `AlgebraicGeometry.Etale.isIso_iff_bijective_comp_of_isSepClosed` (`theorem-poincare-duality`): a
  morphism `u : P ⟶ Q` of the point category is an isomorphism if and only if
  `Hom(Λ_s[r], u)` is bijective for every `r : ℤ`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual`
  (`theorem-global-verdier-duality`): evaluation at the point carries the dual `RHom_s(C, Λ_s)` of
  an object of `D^b_c(s, Λ)` to the dual `RHom_Λ(RΓ(s, C), Λ)`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence`
  : the same for any coefficient category `A` and scheme `X` for which the constant sheaf functor
  `A ⥤ Sheaf X_ét A` is an equivalence of categories.
- `AlgebraicGeometry.Etale.isEquivalence_rightDerivedGlobalSections_of_isSepClosed`
  (`theorem-global-verdier-duality`): evaluation at the point `RΓ(s, -)` is an equivalence of
  categories.
- `AlgebraicGeometry.Etale.homSingleShiftEquivOfIsSepClosed` (`theorem-global-verdier-duality`):
morphisms
  `Λ_s[-r] ⟶ C` are the global sections of the `r`-th cohomology sheaf of `C`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Etale

open Scheme Pretriangulated ZeroObject

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [Ring Λ]

/-- If the `n`-th cohomology sheaf of an object `C` of the point category is nonzero, then
there is a nonzero morphism `Λ_s[-n] ⟶ C`. -/
theorem exists_ne_zero_of_not_isZero_homology_of_isSepClosed
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (n : ℤ) (hC : ¬ IsZero ((DerivedCategory.homologyFunctor _ n).obj C)) :
    ∃ g : ((DerivedCategory.singleFunctor _ 0).obj ((constantSheaf
      (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))⟦-n⟧ ⟶ C,
      g ≠ 0 := by
  let e := DerivedCategory.Q.objObjPreimageIso C
  set K := DerivedCategory.Q.objPreimage C
  have hK : ¬ IsZero (K.homology n) := fun h ↦ hC (IsZero.of_iso h
    ((DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app K))
  obtain ⟨s, hs⟩ : ∃ s : (K.homology n).obj.obj (op (etalePoint k)), s ≠ 0 := by
    by_contra! h
    exact hK (isZero_of_subsingleton_sections_of_isSepClosed _ ⟨fun x y ↦ by rw [h x, h y]⟩)
  obtain ⟨t, rfl⟩ := surjective_app_of_epi_of_isSepClosed k (K.homologyπ n) s
  let f : (HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj ((constantSheaf
      (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)) ⟶ K :=
    HomologicalComplex.mkHomFromSingle (homOfGlobalSection t ≫ K.iCycles n) (by simp)
  have hf : (HomologicalComplex.singleObjHomologySelfIso _ _ _).inv ≫
      HomologicalComplex.homologyMap f n = homOfGlobalSection t ≫ K.homologyπ n := by
    rw [← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
      HomologicalComplex.homologyπ_naturality, ← Category.assoc]
    congr 1
    rw [← cancel_mono (K.iCycles n), Category.assoc, HomologicalComplex.cyclesMap_i,
      HomologicalComplex.singleObjCyclesSelfIso_inv_iCycles_assoc,
      HomologicalComplex.mkHomFromSingle_f, Iso.inv_hom_id_assoc]
  have hQf : DerivedCategory.Q.map f ≠ 0 := by
    intro h0
    have := DerivedCategory.homologyFunctorFactors_hom_naturality f n
    rw [h0, Functor.map_zero, zero_comp] at this
    have hzero : HomologicalComplex.homologyMap f n = 0 :=
      (cancel_epi ((DerivedCategory.homologyFunctorFactors _ n).hom.app _)).1
        (this.symm.trans comp_zero.symm)
    apply homOfGlobalSection_ne_zero hs
    rw [← homOfGlobalSection_comp, ← hf, hzero, comp_zero]
  refine ⟨((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).hom.app _ ≫
    DerivedCategory.Q.map f ≫ e.hom, ?_⟩
  intro h0
  apply hQf
  rw [← cancel_mono e.hom, zero_comp]
  exact (cancel_epi (((DerivedCategory.singleFunctors _).shiftIso (-n) n 0 (by omega)).hom.app
    _)).1 (h0.trans comp_zero.symm)

/-- Blueprint `theorem-poincare-duality`: Detection of isomorphisms at the point.

Let `k` be a separably closed field and `s = Spec k`. A morphism `u : P ⟶ Q` of the point
category `D(s_ét, Λ)` is an isomorphism if and only if `Hom(Λ_s[r], u)` is bijective for every
`r : ℤ`, where `Λ_s` is the constant sheaf `Λ` placed in degree `0`.

The blueprint deduces this from the equivalence of the point category with complexes of
`Λ`-modules. Here the cone `C` of `u` is shown to be zero directly: `Hom(Λ_s[r], C) = 0` for all
`r` by the long exact sequence, and a nonzero cohomology sheaf `H^n(C)` would give a nonzero
morphism `Λ_s[-n] ⟶ C`, since an étale sheaf on `Spec k` is determined by its global sections
(`AlgebraicGeometry.Etale.exists_ne_zero_of_not_isZero_homology_of_isSepClosed`). -/
theorem isIso_iff_bijective_comp_of_isSepClosed
    {P Q : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (u : P ⟶ Q) :
    IsIso u ↔ ∀ r : ℤ, Function.Bijective (fun g : ((DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ Λ)))⟦r⟧ ⟶ P ↦ g ≫ u) := by
  refine ⟨fun hu r ↦ (isIso_iff_yoneda_map_bijective u).1 hu _, fun h ↦ ?_⟩
  set T := (DerivedCategory.singleFunctor _ 0).obj
    ((constantSheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
      (ModuleCat.of Λ Λ))
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle u
  -- composition with `u⟦1⟧'` is injective on morphisms out of `T⟦r⟧`
  have hinj : ∀ (r : ℤ) (x : T⟦r⟧ ⟶ P⟦(1 : ℤ)⟧), x ≫ u⟦(1 : ℤ)⟧' = 0 → x = 0 := by
    intro r x hx
    let E : T⟦r⟧ ≅ (T⟦r - 1⟧)⟦(1 : ℤ)⟧ := (shiftFunctorAdd' _ (r - 1) 1 r (by omega)).app T
    obtain ⟨y, hy⟩ := (shiftFunctor _ (1 : ℤ)).map_surjective (E.inv ≫ x)
    have hyu : y ≫ u = 0 := by
      apply (shiftFunctor _ (1 : ℤ)).map_injective
      rw [Functor.map_comp, hy, Functor.map_zero, Category.assoc, hx, comp_zero]
    have hy0 : y = 0 := (h (r - 1)).1 (hyu.trans zero_comp.symm)
    rw [← cancel_epi E.inv, ← hy, hy0, Functor.map_zero, comp_zero]
  have hw : w ≫ u⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have huv : u ≫ v = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hzero : ∀ (r : ℤ) (g : T⟦r⟧ ⟶ C), g = 0 := by
    intro r g
    obtain ⟨g', hg'⟩ := Triangle.coyoneda_exact₃ _ hT g
      (hinj r (g ≫ w) (by rw [Category.assoc, hw, comp_zero]))
    obtain ⟨g'', rfl⟩ := (h r).2 g'
    change g = (g'' ≫ u) ≫ v at hg'
    rw [hg', Category.assoc, huv, comp_zero]
  have hC : IsZero C := by
    have : IsIso (0 : C ⟶ 0) := (DerivedCategory.isIso_iff _ _).2 fun n ↦ by
      have hn : IsZero ((DerivedCategory.homologyFunctor _ n).obj C) := by
        by_contra hn
        obtain ⟨g, hg⟩ := exists_ne_zero_of_not_isZero_homology_of_isSepClosed C n hn
        exact hg (hzero _ g)
      exact isIso_of_source_target_iso_zero _ hn.isoZero
        ((Functor.map_isZero _ (isZero_zero _)).isoZero)
    exact IsZero.of_iso (isZero_zero _) (asIso (0 : C ⟶ 0))
  exact (Triangle.isZero₃_iff_isIso₁ _ hT).1 hC

section GlobalSections

/-- Over a separably closed field `k`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec k` preserves epimorphisms: an epimorphism of sheaves is surjective on
sections over the terminal object, every covering sieve of which is maximal. -/
instance preservesEpimorphisms_Γ_of_isSepClosed :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).PreservesEpimorphisms where
  preserves {F G} φ _ := by
    let e := Sheaf.ΓNatIsoSheafSections (Spec (.of k)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ) isTerminalEtalePoint
    have h : (Sheaf.Γ _ _).map φ =
        e.hom.app F ≫ ((sheafSections _ _).obj _).map φ ≫ e.inv.app G := by
      rw [← reassoc_of% (e.hom.naturality φ)]
      simp
    have : Epi (((sheafSections (Spec (.of k)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ)).obj (op (etalePoint k))).map φ) :=
      (ModuleCat.epi_iff_surjective _).2 (surjective_app_of_epi_of_isSepClosed k φ)
    rw [h]
    infer_instance

/-- Over a separably closed field `k`, the global sections functor on étale sheaves of
`Λ`-modules on `Spec k` is exact. -/
instance preservesFiniteColimits_Γ_of_isSepClosed :
    PreservesFiniteColimits (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) := by
  have h := (Functor.preservesFiniteLimits_tfae
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))).out 4 1
  have h' := (Functor.preservesFiniteColimits_tfae
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))).out 1 4
  exact h'.1 fun S hS ↦ ⟨(h.1 inferInstance S hS).1, by have := hS.epi_g; infer_instance⟩

/-- Over a separably closed field `k`, the cohomology of the derived global sections of an
object `L` of `D(Spec(k)_ét, Λ)` is the global sections of its cohomology sheaves:
`Hⁿ(RΓ(Spec k, L)) ≅ Γ(Spec k, Hⁿ(L))`, the global sections functor being exact. -/
noncomputable def homologyRightDerivedGlobalSectionsIsoOfIsSepClosed (n : ℤ) :
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k)) ⋙
        DerivedCategory.homologyFunctor _ n ≅
      DerivedCategory.homologyFunctor _ n ⋙
        Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
  (Functor.rightDerivedFunctorHomologyFunctorIso _ n).symm

/-- Over a separably closed field `k`, the global sections of an étale sheaf of `Λ`-modules on
`Spec k` inject into its stalk at any geometric point: a section vanishing on an étale
neighbourhood of the point vanishes, as that neighbourhood has a `k`-point. -/
lemma injective_toPresheafFiber_etalePoint_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Spec (.of k))
    (x : (pointSmallEtale s).fiber.obj (etalePoint k)) :
    Function.Injective ((pointSmallEtale s).toPresheafFiber (etalePoint k) x F.obj) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro z₁ z₂ h
  obtain ⟨Y, f, y, -, hy⟩ := ((pointSmallEtale s).toPresheafFiber_eq_iff' _ x z₁ z₂).1 h
  have : AlgebraicGeometry.Etale Y.hom := Y.prop
  obtain ⟨l, hl, -⟩ := exists_fac_of_etale_of_isSepClosed Y.hom (𝟙 _)
    ((y.left : Spec (.of Ω) ⟶ Y.left) (default : Spec (.of Ω)))
    (Subsingleton.elim (α := Spec (.of k)) _ _)
  let σ : etalePoint k ⟶ Y := MorphismProperty.Over.homMk (A := etalePoint k) (B := Y) l
    (hl.trans rfl)
  have hσ : σ ≫ f = 𝟙 _ := isTerminalEtalePoint.hom_ext _ _
  have := congrArg (F.obj.map σ.op) hy
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, hσ, op_id,
    CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using this

/-- Over a separably closed field `k`, the global sections of a constructible étale sheaf of
modules over a noetherian ring `Λ` on `Spec k` form a finite `Λ`-module: they inject into the
stalk at the geometric point `𝟙 : Spec k ⟶ Spec k`, which is finite. -/
lemma finite_Γ_of_isConstructibleSheaf [IsNoetherianRing Λ]
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [IsConstructibleSheaf F] :
    Module.Finite Λ ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F) := by
  have hfin := (IsConstructibleSheaf.isFiniteSheaf (F := F)
    inferInstance).isFinitelyGenerated_sheafFiber k (𝟙 _)
  rw [ModuleCat.isFinitelyGenerated_iff] at hfin
  have : Module.Finite Λ (((pointSmallEtale (𝟙 (Spec (.of k)))).presheafFiber
    (A := ModuleCat.{u + 1} Λ)).obj F.obj) := hfin
  let x : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.obj (etalePoint k) :=
    Over.homMk (𝟙 _) (by simp [etalePoint])
  let e := (Sheaf.ΓNatIsoSheafSections (Spec (.of k)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).app F
  exact Module.Finite.of_injective
    (e.hom ≫ (pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber (etalePoint k) x F.obj).hom
    ((injective_toPresheafFiber_etalePoint_of_isSepClosed F _ x).comp
      ((ConcreteCategory.bijective_of_isIso e.hom).1))

/-- Over a separably closed field `k`, the global sections of an étale sheaf of `Λ`-modules on
`Spec k` are its stalk at the geometric point `𝟙 : Spec k ⟶ Spec k`: the canonical map is
injective by `AlgebraicGeometry.Etale.injective_toPresheafFiber_etalePoint_of_isSepClosed`,
and surjective since every étale neighbourhood of this point has a `k`-point through which the
point factors. -/
lemma bijective_toPresheafFiber_etalePoint_of_isSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (x : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.obj (etalePoint k)) :
    Function.Bijective
      ((pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber (etalePoint k) x F.obj) := by
  refine ⟨injective_toPresheafFiber_etalePoint_of_isSepClosed F _ x, fun p ↦ ?_⟩
  have : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget (ModuleCat.{u + 1} Λ)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  obtain ⟨V, v, z, rfl⟩ := (pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber_jointly_surjective
    (P := F.obj) p
  let σ : etalePoint k ⟶ V := MorphismProperty.Over.homMk (A := etalePoint k) (B := V) v.left
    ((Over.w v).trans rfl)
  have hv : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.map σ x = v := by
    apply Over.OverMorphism.ext
    have hx : x.left = 𝟙 _ := by simpa [etalePoint] using Over.w x
    change x.left ≫ v.left = v.left
    rw [hx, Category.id_comp]
  refine ⟨F.obj.map σ.op z, ?_⟩
  rw [← hv, ← (pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber_w σ x F.obj]
  rfl

/-- Over a separably closed field `k`, the global sections of an étale sheaf of `Λ`-modules on
`Spec k` are isomorphic to its stalk at the geometric point `𝟙 : Spec k ⟶ Spec k`. -/
noncomputable def ΓIsoSheafFiberOfIsSepClosed
    (F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F ≅
      (pointSmallEtale (𝟙 (Spec (.of k)))).sheafFiber.obj F :=
  let x : (pointSmallEtale (𝟙 (Spec (.of k)))).fiber.obj (etalePoint k) :=
    Over.homMk (𝟙 _) (by simp [etalePoint])
  (Sheaf.ΓNatIsoSheafSections (Spec (.of k)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ) isTerminalEtalePoint).app F ≪≫
    (LinearEquiv.ofBijective
      ((pointSmallEtale (𝟙 (Spec (.of k)))).toPresheafFiber (etalePoint k) x F.obj).hom
      (bijective_toPresheafFiber_etalePoint_of_isSepClosed F x)).toModuleIso

end GlobalSections

section Flat

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance instEssentiallySmallEtale_point
    (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

/-- Over a separably closed field `k`, the global sections of a flat étale sheaf of
`Λ`-modules on `Spec k` form a flat `Λ`-module: they are its stalk at a geometric point. -/
lemma flat_Γ_of_isSepClosed {F : Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : ObjectProperty.flat F) :
    ObjectProperty.flat
      ((Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj F) :=
  ObjectProperty.prop_of_iso _ ((ΓIsoSheafFiberOfIsSepClosed F) ≪≫
    ((pointSmallEtale (𝟙 (Spec (.of k)))).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} Λ)).symm.app F).symm
    (((pointSmallEtale (𝟙 (Spec (.of k)))).ulift.{u + 1}).flat_sheafFiber_obj hF)

/-- Over a separably closed field `k`, an object of `D(Spec(k)_ét, Λ)` of Tor amplitude in
`[a, b]` has derived global sections of Tor amplitude in `[a, b]`: it is represented by a
complex of flat sheaves in degrees `[a, b]`, and the global sections functor is exact and
preserves flatness (`AlgebraicGeometry.Etale.flat_Γ_of_isSepClosed`). -/
lemma torAmplitudeIn_rightDerivedGlobalSections_of_isSepClosed {a b : ℤ}
    {L : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (hL : _root_.DerivedCategory.torAmplitudeIn _ a b L) :
    _root_.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) a b
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj L) := by
  obtain ⟨P, _, _, hP, ⟨e⟩⟩ := _root_.DerivedCategory.exists_iso_Q_obj_flat_of_torAmplitudeIn hL
  let Γ := Sheaf.Γ (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)
  have : CochainComplex.IsStrictlyGE ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a := by
    rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi ↦ Γ.map_isZero (P.isZero_of_isStrictlyGE a i hi)
  have : CochainComplex.IsStrictlyLE ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) b := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi ↦ Γ.map_isZero (P.isZero_of_isStrictlyLE b i hi)
  refine (_root_.DerivedCategory.torAmplitudeIn _ a b).prop_of_iso ?_
    (_root_.DerivedCategory.torAmplitudeIn_Q_obj_of_flat
      ((Γ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) a b
      fun n ↦ flat_Γ_of_isSepClosed (hP n))
  exact (Γ.mapDerivedCategoryFactors.app P).symm ≪≫ Γ.mapDerivedCategory.mapIso e ≪≫
    (Functor.rightDerivedFunctorIsoMapDerivedCategory Γ).symm.app L

end Flat

/-- Blueprint `theorem-global-verdier-duality` (cohomology at the point):
`H^r(-) = Hom_s(Λ[-r], -)`.

Let `k` be a separably closed field and `s = Spec k`. For an object `C` of the point category
and `r : ℤ`, morphisms `Λ_s[-r] ⟶ C` correspond to elements of the fibre at the geometric point
(the global sections) of the `r`-th cohomology sheaf of `C`. The constant sheaf `Λ_s` is
projective, so morphisms `Λ_s[-r] ⟶ C` are morphisms `Λ_s ⟶ H^r(C)`
(`DerivedCategory.homSingleEquivOfProjective`), and those are global sections of `H^r(C)`. -/
noncomputable def homSingleShiftEquivOfIsSepClosed
    (C : DerivedCategory (Sheaf (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (r : ℤ) :
    (((DerivedCategory.singleFunctor _ 0).obj ((constantSheaf
      (Spec (.of k)).smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ)))⟦-r⟧ ⟶ C) ≃
      ((DerivedCategory.homologyFunctor _ r).obj C).obj.obj (op (etalePoint k)) :=
  have := projective_constantSheaf_moduleCat_of_iso (Iso.refl (Spec (.of k))) Λ
  ((((DerivedCategory.singleFunctors _).shiftIso (-r) r 0 (by omega)).app _).homCongr
      (Iso.refl C)).trans <|
    (DerivedCategory.homSingleEquivOfProjective _ r C).trans <|
      ((constantSheafAdj _ _ isTerminalEtalePoint).homEquiv _ _).trans <|
        ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf Λ ℕ _).toEquiv

section Duality

section

section Equivalence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  (X : Scheme.{u}) [(constantSheaf X.smallEtaleTopology A).IsEquivalence]

/-- If the constant sheaf functor `F : A ⥤ Sheaf X_ét A` is an equivalence of categories, the
global sections functor is a quasi-inverse of `F`, hence exact, and the derived global sections
`RΓ(X, -)` are the functor induced by `F⁻¹` on derived categories. -/
noncomputable def rightDerivedGlobalSectionsIsoMapDerivedCategoryInv :
    rightDerivedGlobalSections A X ≅
      (constantSheaf X.smallEtaleTopology A).inv.mapDerivedCategory :=
  let eΓ : Sheaf.Γ X.smallEtaleTopology A ≅ (constantSheaf X.smallEtaleTopology A).inv :=
    (constantSheafΓAdj _ _).rightAdjointUniq
      (constantSheaf X.smallEtaleTopology A).asEquivalence.toAdjunction
  have : PreservesFiniteLimits (Sheaf.Γ X.smallEtaleTopology A) :=
    preservesFiniteLimits_of_natIso eΓ.symm
  have : PreservesFiniteColimits (Sheaf.Γ X.smallEtaleTopology A) :=
    preservesFiniteColimits_of_natIso eΓ.symm
  (Sheaf.Γ _ _).rightDerivedFunctorIsoMapDerivedCategory ≪≫ Functor.mapDerivedCategoryNatIso eΓ

/-- If the constant sheaf functor `A ⥤ Sheaf X_ét A` is an equivalence of categories, the
derived global sections `RΓ(X, -) : D(X_ét) ⥤ D(A)` are an equivalence of categories. -/
theorem isEquivalence_rightDerivedGlobalSections_of_isEquivalence :
    (rightDerivedGlobalSections A X).IsEquivalence :=
  Functor.isEquivalence_of_iso (rightDerivedGlobalSectionsIsoMapDerivedCategoryInv A X).symm

end Equivalence

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] (X : Scheme.{u})
  [(constantSheaf X.smallEtaleTopology A).IsEquivalence]

/-- If the constant sheaf functor `A ⥤ Sheaf X_ét A` is an equivalence of categories (as it is
for `X` the spectrum of a separably closed field), then the derived global sections carry the
coefficient dual `RHom(C, Λ_X)` of a complex of étale sheaves to the dual of its derived global
sections: `RΓ(X, RHom(C, Λ_X)) ≅ RHom(RΓ(X, C), 𝟙)`.

The global sections functor is then the quasi-inverse of the monoidal equivalence
`constantSheaf`, so its derived functor commutes with derived internal homs
(`DerivedCategory.mapDerivedCategoryInvIhomUnitIso`). The statement is made for a general
coefficient category `A`: in this generality the monoidal structures on the derived categories
are the ones of `AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`, which keeps kernel
checks of its instances cheap. -/
theorem nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence
    (C : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    Nonempty ((rightDerivedGlobalSections A X).obj
        ((DerivedCategory.coefficientDual A X).obj (op C)) ≅
      (ihom ((rightDerivedGlobalSections A X).obj C)).obj (𝟙_ _)) :=
  let e := rightDerivedGlobalSectionsIsoMapDerivedCategoryInv A X
  ⟨e.app _ ≪≫ DerivedCategory.mapDerivedCategoryInvIhomUnitIso _ C ≪≫
    (MonoidalClosed.internalHom.mapIso (e.app C).op).app (𝟙_ _)⟩

end

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- Blueprint `theorem-global-verdier-duality`: The point, evaluated (evaluation at the point is an
equivalence).

Let `k` be a separably closed field and `s = Spec k`. Evaluation at the geometric point, the
derived global sections `RΓ(s, -) : D(s_ét, Λ) ⥤ D(Λ)`, is an equivalence of categories; in
particular it is conservative. It restricts to the equivalence `Fib_s` of the blueprint between
the point category `D^b_c(s, Λ)` and the bounded derived category of finite `Λ`-modules. -/
instance isEquivalence_rightDerivedGlobalSections_of_isSepClosed :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).IsEquivalence :=
  isEquivalence_rightDerivedGlobalSections_of_isEquivalence _ _

/-- Blueprint `theorem-global-verdier-duality`: The point, evaluated (the duality part).

Let `k` be a separably closed field, `s = Spec k` and `Λ` a coefficient ring. For every
object `C` of the point category `D^b_c(s, Λ)`, the dual `RHom_s(C, ω_s)`, where
`ω_s = Ra_s^! Λ = Λ_s` is the unit (`AlgebraicGeometry.Etale.DerivedCategory.coefficientDual`),
is computed after evaluation at the point by the dual over `Λ`:

`RΓ(s, RHom_s(C, Λ_s)) ≅ RHom_Λ(RΓ(s, C), Λ)`.

Evaluation at the geometric point is the derived global sections `RΓ(s, -)`. Over a separably
closed field the constant sheaf functor `ModuleCat Λ ⥤ Sheaf s_ét (ModuleCat Λ)` is a monoidal
equivalence (`AlgebraicGeometry.Scheme.isEquivalence_constantSheaf_of_isSepClosed`) with
quasi-inverse the global sections, so this is
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence`.
Neither the finiteness of `Λ` nor the constructibility of `C` is used. -/
theorem nonempty_iso_rightDerivedGlobalSections_coefficientDual
    {C : DerivedCategoryModule Λ (Spec (.of k))}
    (_hC : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) C) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj (op C)) ≅
      (ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C)).obj
        (𝟙_ _)) :=
  nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence _ _ C

end Duality

end AlgebraicGeometry.Etale
